// Copyright 2022 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Suyang Song <susong@student.ethz.ch>
// Bowen Wang <bowwang@student.ethz.ch>

`include "axi/typedef.svh"

//response buffer: convert byte address to word address, theDramWordNumsDramWordNumsn store them into aw/ar fifo
//                 store word data into write data fifo
//                 differentiate between write and read valid based on numbers of word in wrtie data fifo
module buffer_resp #(
    parameter int unsigned BufferDepth      = 4,
    parameter int unsigned DramDataWidth    = 256,
    parameter int unsigned DramStrbWidth    = DramDataWidth/8,
    parameter int unsigned DramLenWidth     = 6,
    //soc defined signals
    parameter int unsigned AXI_ID_WIDTH     = 6,
    parameter int unsigned AXI_USER_WIDTH   = 1,

    parameter type user_t   = logic[AXI_USER_WIDTH-1:0],
    parameter type id_t     = logic[AXI_ID_WIDTH-1:0]
) (
    input  logic clk_i,
    input  logic rst_ni,

    ///////////////////////////////////////////////////
    /////response buffer ready output//////////////////
    ///////////////////////////////////////////////////
    input  logic                    trx_is_write_i,
    input  logic [DramLenWidth-1:0] trx_len_i,
    output logic                    buf_resp_ready_o,

    ///////////////////////////////////////////////////
    //B channel buffer output signals//////////////////
    ///////////////////////////////////////////////////
    output user_t           b_user_o,
    output id_t             b_id_o,
    output axi_pkg::resp_t  b_resp_o,
    
    input  logic            b_axi_ready_i,
    output logic            b_axi_valid_o,

    //response fifo push valid signal
    input  logic cmd_valid_i,
    input  logic cmd_ready_i,

    ///////////////////////////////////////////////////
    /////////////////R channel signal//////////////////
    ///////////////////////////////////////////////////

    //master interface with axi
    output logic [DramDataWidth-1:0] r_axi_data_o,
    output logic                     r_axi_last_o,
    output logic [AXI_ID_WIDTH-1:0]  r_axi_id_o,
    output logic                     r_axi_valid_o,
    input  logic                     r_axi_ready_i,

    //slave interface with phy
    input  logic [DramDataWidth-1:0] r_phy_data_i,
    input  logic                     r_phy_last_i,
    input  logic                     r_buf_valid_i,
    output logic                     r_buf_ready_o

);

    //----------------------=======================---------------------------//
    //----------------------=write response buffer=---------------------------//
    //----------------------=======================---------------------------//

    //channel B
    localparam BBufDepth = BufferDepth;
    localparam BWidth    = 2 + AXI_USER_WIDTH + AXI_ID_WIDTH;

    typedef struct packed {
        user_t      user;
        id_t        id;
        axi_pkg::resp_t  resp;
    } b_buf_t;

    b_buf_t     b_buffer_i, b_buffer_o;
    logic       b_buf_valid_i, b_buf_ready_o;

    //slave okay defaultly
    assign b_buffer_i.resp = axi_pkg::RESP_OKAY;   
    //no user defined currently
    assign b_buffer_i.user = '0;     
    //No need for ID, cause transactions carried out in order             
    assign b_buffer_i.id   = '0;                   
    //When write transaction sent to downstream, push B response back to B buffer
    assign b_buf_valid_i   =  cmd_valid_i && cmd_ready_i 
                              && trx_is_write_i ;   
    //assign b buffer output to axi interface
    assign b_user_o        =  b_buffer_o.user;
    assign b_id_o          =  b_buffer_o.id;
    assign b_resp_o        =  b_buffer_o.resp;    
    
    stream_fifo #(
        .DATA_WIDTH ( BWidth        ),
        .DEPTH      ( BBufDepth     ),
        .T          ( b_buf_t       ) 
    ) i_b_channel_fifo (
        .clk_i      (clk_i),
        .rst_ni     (rst_ni),
        
        //TODO: support DFT
        .flush_i    (1'b0),
        .testmode_i (1'b0),

        //slave interface port
        .data_i     (b_buffer_i),
        .valid_i    (b_buf_valid_i),
        .ready_o    (b_buf_ready_o),

        //master interface port
        .usage_o    (),
        .data_o     (b_buffer_o),
        .valid_o    (b_axi_valid_o),
        .ready_i    (b_axi_ready_i)
    );


    localparam int unsigned PreIdWidth = BufferDepth == 1 ? 1 : $clog2(BufferDepth);
    logic [AXI_ID_WIDTH-1:0] counter_delta;
    logic [AXI_ID_WIDTH-1:0] b_counter_id;

    assign counter_delta = 'b1 << (AXI_ID_WIDTH - PreIdWidth);
//    assign b_buffer_i.id = b_counter_id;

    delta_counter #(
        .WIDTH      (AXI_ID_WIDTH)
    ) i_b_id_counter(  
        .clk_i      (clk_i             ),
        .rst_ni     (rst_ni            ),
        .clear_i    (1'b0              ),
        .en_i       (b_buf_valid_i     ),
        .load_i     (1'b0              ),
        .down_i     (1'b0              ),
        .delta_i    (counter_delta     ),
        .d_i        ('0                ),
        .q_o        (b_counter_id      ),
        .overflow_o (/* unconnected */ )
    );


    //----------------------=======================---------------------------//
    //----------------------=read    data   SRAM  =---------------------------//
    //----------------------=======================---------------------------//
    localparam RBufDepth = BufferDepth << DramLenWidth;
    localparam RDepth    = (RBufDepth > 1 )? $clog2(RBufDepth) : 1; //pointer width



    logic [RDepth:0]  r_fifo_pointer;
    logic [RDepth:0]  r_fifo_usage;

    sram_wrapper #(
        .DramDataWidth  (DramDataWidth),
        .BufferDepth    (BufferDepth),
        .DramLenWidth   (DramLenWidth)
    )i_r_sram(
        .clk_i          (clk_i),
        .rst_ni         (rst_ni),

        //slave handshake signal
        .w_valid_i      (r_buf_valid_i),
        .w_ready_o      (r_buf_ready_o),

        //master  handshake signal
        .r_ready_i      (r_axi_ready_i),
        .r_valid_o      (r_axi_valid_o),

        .w_data_i       (r_phy_data_i),
        .r_data_o       (r_axi_data_o),
        
        .usage_o        (r_fifo_pointer)
    );

    //----------------------===========================------------------------//
    //----------------------=   r_last signal fifo    =------------------------//
    //----------------------===========================------------------------//


    //r_last signal has to synchronize with read data
    //when r_data pushed last also will be pushed
    //when r_data poped  last also should be poped
    

    fifo_v3 #(
        .DATA_WIDTH  (1),
        .DEPTH       (RBufDepth)
    )i_r_last_fifo(
        .clk_i  (clk_i),
        .rst_ni (rst_ni),

        .flush_i    (1'b0),
        .testmode_i (1'b0),

        //slave port read last input
        .data_i(r_phy_last_i),
        .push_i(r_buf_valid_i && r_buf_ready_o),

        //master port write last output
        .data_o(r_axi_last_o),
        .pop_i (r_axi_valid_o && r_axi_ready_i),

        .full_o(/* unconnected */ ),
        .empty_o(/* unconnected */ ),
        .usage_o(/* unconnected */ )
    );

    //----------------------===========================------------------------//
    //----------------------=   r_id   signal fifo    =------------------------//
    //----------------------===========================------------------------//
    logic [AXI_ID_WIDTH-1:0] r_counter_id;

    fifo_v3 #(
        .DATA_WIDTH  (AXI_ID_WIDTH),
        .DEPTH       (RBufDepth)
    )i_r_id_fifo(
        .clk_i  (clk_i),
        .rst_ni (rst_ni),

        .flush_i    (1'b0),
        .testmode_i (1'b0),

        //slave port read last input
        .data_i(r_counter_id ),
        .push_i(r_buf_valid_i && r_buf_ready_o ),
        //master port write last output
        .data_o(r_axi_id_o   ),
        .pop_i (r_axi_valid_o && r_axi_ready_i),

        .full_o(/* unconnected */ ),
        .empty_o(/* unconnected */ ),
        .usage_o(/* unconnected */ )
    );

    delta_counter #(
        .WIDTH      (AXI_ID_WIDTH)
    ) i_r_id_counter(  
        .clk_i      (clk_i             ),
        .rst_ni     (rst_ni            ),
        .clear_i    (1'b0              ),
        .en_i       (r_phy_last_i && r_buf_valid_i && r_buf_ready_o),
        .load_i     (1'b0              ),
        .down_i     (1'b0              ),
        .delta_i    (counter_delta     ),
        .d_i        ('0                ),
        .q_o        (r_counter_id      ),
        .overflow_o (/* unconnected */ )
    );


    //----------------------===========================------------------------//
    //----------------------=buffer response generator=------------------------//
    //----------------------===========================------------------------//

    //buffer response signal is asserted according to is_write:
    //if is_write is 1, which means transaction meant to be sent is wrtie,
    //then b_ready_o should be directly connected to buffer response ready 
    //when is_write is 0, it meas transaction meant to be sent is read,
    //then should know whether remaining space of read fifo is enough to suport read transaction
    //external world uses trx_valid with buffer_ready_o to tell fsm when cmd_valid is asserted

    logic r_buf_word_ready;
    logic b_buf_word_ready;
    logic [RDepth:0] r_fifo_space;

    assign r_fifo_usage      = r_buf_ready_o ? r_fifo_pointer : RBufDepth;

    assign b_buf_word_ready  = b_buf_ready_o;
    assign r_fifo_space      =  RBufDepth - r_fifo_usage ;
    assign r_buf_word_ready  =  ((trx_len_i + 1) <= r_fifo_space) ? 1 : 0;

    //write or read transaction buffer ready output signal
    assign buf_resp_ready_o  = trx_is_write_i ? b_buf_word_ready : r_buf_word_ready;


endmodule
