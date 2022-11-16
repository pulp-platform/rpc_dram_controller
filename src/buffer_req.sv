// Copyright 2022 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Suyang Song <susong@student.ethz.ch>
// Bowen Wang <bowwang@student.ethz.ch>

//write buffer: convert byte address to word address, then store them into aw/ar fifo
//              store word data into write data fifo
//              differentiate between write and read valid based on numbers of word in wrtie data fifo
module buffer_req #(
  parameter int unsigned DramAddrWidth = 20,
  parameter int unsigned DramLenWidth  = 6,
  parameter int unsigned DramDataWidth = 256,
  parameter int unsigned DramStrbWidth = DramDataWidth / 8,
  parameter int unsigned BufferDepth   = 4,

  parameter int unsigned AxiAddrWidth = 48,
  parameter int unsigned AxiLenWidth  = 8
) (
  input  logic clk_i,
  input  logic rst_ni,
  //write buffer signals
  input  logic [AxiAddrWidth-1:0]      aw_addr_i,
  input  logic [AxiLenWidth-1:0 ]      aw_len_i,
  input  logic aw_axi_valid_i,
  output logic aw_axi_ready_o,

  //read  buffer signals
  input  logic [AxiAddrWidth-1:0]      ar_addr_i,
  input  logic [AxiLenWidth-1:0 ]      ar_len_i,
  input  logic ar_axi_valid_i,
  output logic ar_axi_ready_o,

  //write data signals
  input  logic [DramDataWidth-1:0]    w_data_i,
  // input  logic [DramStrbWidth-1:0]    w_strobe_i,
  output logic [DramDataWidth-1:0]    w_data_o,
  // output logic [DramStrbWidth-1:0]    w_strobe_o,

  input  logic w_axi_valid_i,
  output logic w_axi_ready_o,
  output logic w_buf_valid_o,
  input  logic w_buf_ready_i,

  //output transaction
  output logic trx_valid_o,
  input  logic trx_ready_i,
  output logic trx_is_write_o,
  output logic [DramAddrWidth-1:0] trx_addr_o,
  output logic [DramLenWidth-1:0]  trx_len_o
);

  //buffer handshake with arbiter
  logic aw_buf_ready_i;
  logic aw_buf_valid_o;
  logic ar_buf_ready_i;
  logic ar_buf_valid_o;

  //FIFO word width
  localparam FIFOAddrWidth = DramAddrWidth + DramLenWidth;
  //Address FIFO Depth
  localparam AddrBufDepth = BufferDepth;
  //FIFO address Depth -> depth pointer
  //TODO: In reality RDepth must add 1. to avoid being when FIFO is full
  //      this is just to eliminate warning in simulation
  localparam AddrDepth = (AddrBufDepth > 1) ? $clog2(AddrBufDepth) : 1;
  //Dram word aligned position
  localparam DramAlignPos = $clog2(DramDataWidth / 8);
  //FIFO data width
  localparam FIFODataWidth = DramDataWidth + DramLenWidth;
  //FIFO data depth
  localparam DataBufDepth = AddrBufDepth << DramLenWidth;
  //FIFO data Depth address
  //TODO: In reality RDepth must add 1. to avoid being when FIFO is full
  //      this is just to eliminate warning in simulation
  localparam DataDepth = (DataBufDepth > 1) ? $clog2(DataBufDepth) : 1;

  //write address buffer variable type
  typedef struct packed {
    logic [DramAddrWidth-1:0] addr;
    logic [DramLenWidth-1:0]  len;
  } aw_buffer_t;

  //read address buffer variable type
  typedef struct packed {
    logic [DramAddrWidth-1:0] addr;
    logic [DramLenWidth-1:0]  len;
  } ar_buffer_t;

  //write data buffer variable type
  typedef struct packed {
    logic [DramDataWidth-1:0] data;
    //      logic [DramStrbWidth-1:0] strb;  //don't need strobe anymore
  } w_buffer_t;

  //------------------------======================---------------------------//
  //------------------------=write address buffer=---------------------------//
  //------------------------======================---------------------------//

  //assign axi request len and address to buffer
  //high address of aw_addr is fixed for memory mapping
  //experiencing 64->256 conversion means aw_len is bound to be within scope

  aw_buffer_t aw_buffer_i, aw_buffer_o;

  assign aw_buffer_i.addr = aw_addr_i >> DramAlignPos;
  assign aw_buffer_i.len  = aw_len_i;

  //write address buffer
  stream_fifo #(
    .DATA_WIDTH(FIFOAddrWidth),
    .DEPTH     (AddrBufDepth),
    .T         (aw_buffer_t),
    .ADDR_DEPTH(AddrDepth)
  ) i_aw_channel_fifo (
    .clk_i (clk_i),
    .rst_ni(rst_ni),

    //TODO: support DFT
    .flush_i   (1'b0),
    .testmode_i(1'b0),

    //slave interface port
    .data_i (aw_buffer_i),
    .valid_i(aw_axi_valid_i),
    .ready_o(aw_axi_ready_o),

    //master interface port
    .usage_o(),
    .data_o (aw_buffer_o),
    .valid_o(aw_buf_valid_o),
    .ready_i(aw_buf_ready_i)
  );


  //------------------------======================---------------------------//
  //------------------------=read  address buffer=---------------------------//
  //------------------------======================---------------------------//
  //read address buffer variable type

  ar_buffer_t ar_buffer_i, ar_buffer_o;
  assign ar_buffer_i.addr = ar_addr_i >> DramAlignPos;
  assign ar_buffer_i.len  = ar_len_i;

  //read  address buffer
  stream_fifo #(
    .DATA_WIDTH(FIFOAddrWidth),
    .DEPTH     (AddrBufDepth),
    .T         (ar_buffer_t),
    .ADDR_DEPTH(AddrDepth)
  ) i_ar_channel_fifo (
    .clk_i (clk_i),
    .rst_ni(rst_ni),

    //TODO: support DFT
    .flush_i   (1'b0),
    .testmode_i(1'b0),

    //slave interface port
    .data_i (ar_buffer_i),
    .valid_i(ar_axi_valid_i),
    .ready_o(ar_axi_ready_o),

    //master interface port
    .usage_o(),
    .data_o (ar_buffer_o),
    .valid_o(ar_buf_valid_o),
    .ready_i(ar_buf_ready_i)
  );



  //------------------------===================---------------------------//
  //------------------------= write data sram =---------------------------//
  //------------------------===================---------------------------//


  // w_buffer_t             w_buffer_i, w_buffer_o;
  // logic [DataDepth-1:0]  w_fifo_pointer;

  // assign w_buffer_i.data   = w_data_i;
  // // assign w_buffer_i.strb   = w_strobe_i;  //don't need strobe
  // assign w_data_o          = w_buffer_o.data;
  // // assign w_strobe_o        = w_buffer_o.strb;  //don't need strobe

  // stream_fifo #(
  //     .DATA_WIDTH ( FIFODataWidth ),
  //     .DEPTH      ( DataBufDepth  ),
  //     .T          ( w_buffer_t    ),
  //     .ADDR_DEPTH ( DataDepth     )
  // ) i_w_channel_fifo (
  //     .clk_i      (clk_i),
  //     .rst_ni     (rst_ni),

  //     //TODO: support DFT
  //     .flush_i    (1'b0),
  //     .testmode_i (1'b0),

  //     //slave interface port
  //     .data_i     (w_buffer_i),
  //     .valid_i    (w_axi_valid_i),
  //     .ready_o    (w_axi_ready_o),

  //     //master interface port
  //     .usage_o    (w_fifo_pointer),
  //     .data_o     (w_buffer_o),
  //     .valid_o    (w_buf_valid_o),
  //     .ready_i    (w_buf_ready_i)
  // );


  /////////////////////////////////////////////////////////////////////////////

  logic [DataDepth:0] w_fifo_pointer;

  sram_wrapper #(
    .DramDataWidth(DramDataWidth),
    .BufferDepth  (BufferDepth),
    .DramLenWidth (DramLenWidth)
  ) i_w_sram (
    .clk_i (clk_i),
    .rst_ni(rst_ni),

    //slave handshake signal
    .w_valid_i(w_axi_valid_i),
    .w_ready_o(w_axi_ready_o),

    //master  handshake signal
    .r_ready_i(w_buf_ready_i),
    .r_valid_o(w_buf_valid_o),

    .w_data_i(w_data_i),
    .r_data_o(w_data_o),
    .usage_o (w_fifo_pointer)
  );

  //--------------------============================--------------------------//
  //--------------------=write/read request arbiter=--------------------------//
  //--------------------============================--------------------------//

  //arbiter inout type
  typedef aw_buffer_t arb_t;
  arb_t rr_data_o;
  //arbitrate result: 1:write 0:read
  logic rr_is_write;
  //arbiter output handshake
  logic rr_valid_o, rr_ready_i;
  //write buffer transaction valid
  logic aw_buf_trx_valid;

  rr_arb_tree #(
    .NumIn    (2),
    .DataType (arb_t),
    .DataWidth(FIFOAddrWidth),
    //Attention: LockIn has to be set 0
    //To avoid Arbiter mistaken LockIn
    .LockIn   (0),
    .AxiVldRdy(1)
  ) i_rw_req_arb (
    .clk_i  (clk_i),
    .rst_ni (rst_ni),
    .flush_i(1'b0),
    .rr_i   (1'b0),
    //slave interface port
    .req_i  ({aw_buf_trx_valid, ar_buf_valid_o}),
    .gnt_o  ({aw_buf_ready_i, ar_buf_ready_i}),
    .data_i ({aw_buffer_o, ar_buffer_o}),
    //master interface port
    .req_o  (rr_valid_o),
    .gnt_i  (rr_ready_i),
    .data_o (rr_data_o),
    .idx_o  (rr_is_write)
  );


  //--------------------============================--------------------------//
  //--------------------=transaction valid process =--------------------------//
  //--------------------============================--------------------------//


  //write and read transaction valid signal
  logic w_trx_valid, r_trx_valid;
  //data usage signal to indicate how many bytes stored in write data fifo
  logic [DataDepth:0] w_fifo_usage;


  //get writie data numbers
  assign w_fifo_usage     = w_axi_ready_o ? w_fifo_pointer : DataBufDepth;
  //assign arbited results to output
  assign trx_addr_o       = rr_data_o.addr;
  assign trx_len_o        = rr_data_o.len;

  //when write data is enough, assert aw buffer trx valid
  assign aw_buf_trx_valid = aw_buf_valid_o && (aw_buffer_o.len + 1 <= w_fifo_usage);

  //write address valid, if at the same time write data depth is greater
  //than the write transaction burst length then transaction valid
  assign w_trx_valid      = rr_is_write == 0 ? 0 : rr_valid_o;

  assign r_trx_valid      = rr_is_write == 1 ? 0 : rr_valid_o;

  //assign with output handshake with command finite state machine
  assign trx_valid_o      = w_trx_valid | r_trx_valid;
  assign rr_ready_i       = trx_ready_i & trx_valid_o;
  assign trx_is_write_o   = rr_is_write;


endmodule
