// Hyperbus Fixture

// this code is unstable and most likely buggy
// it should not be used by anyone
/// Author: Thomas Benz <tbenz@iis.ee.ethz.ch>
`timescale 1 ns/1 ps
// Configuration register for Hyper bus CHANNEl
`define REG_RX_SADDR            5'b00000 //BASEADDR+0x00 L2 address for RX
`define REG_RX_SIZE             5'b00001 //BASEADDR+0x04 size of the software buffer in L2
`define REG_UDMA_RXCFG          5'b00010 //BASEADDR+0x08 UDMA configuration setup (RX)
`define REG_TX_SADDR            5'b00011 //BASEADDR+0x0C address of the data being transferred 
`define REG_TX_SIZE             5'b00100 //BASEADDR+0x10 size of the data being transferred
`define REG_UDMA_TXCFG          5'b00101 //BASEADDR+0x14 UDMA configuration setup (TX)
`define HYPER_CA_SETUP          5'b00110 //BASEADDR+0x18 set read/write, address space, and burst type 
`define REG_HYPER_ADDR          5'b00111 //BASEADDR+0x1C set address in a hyper ram.
`define REG_HYPER_CFG           5'b01000 //BASEADDR+0x20 set the configuration data for HyperRAM
`define STATUS                  5'b01001 //BASEADDR+0x24 status register
`define TWD_ACT_EXT             5'b01010 //BASEADDR+0x28 set 2D transfer activation
`define TWD_COUNT_EXT           5'b01011 //BASEADDR+0x2C set 2D transfer count
`define TWD_STRIDE_EXT          5'b01100 //BASEADDR+0x30 set 2D transfer stride
`define TWD_ACT_L2              5'b01101 //BASEADDR+0x28 set 2D transfer activation
`define TWD_COUNT_L2            5'b01110 //BASEADDR+0x2C set 2D transfer count
`define TWD_STRIDE_L2           5'b01111 //BASEADDR+0x30 set 2D transfer stride

// Configuration register for Hyper bus CHANNEl
// set by the axi cfg regs
`define REG_PAGE_BOUND          5'b00000 //BASEADDR+0x00 set the page boundary.
// set by the axi cfg regs
`define REG_T_LATENCY_ACCESS    5'b00001 //BASEADDR+0x04 set t_latency_access
// set by the axi cfg regs
`define REG_EN_LATENCY_ADD      5'b00010 //BASEADDR+0x08 set en_latency_additional
`define REG_T_CS_MAX            5'b00011 //BASEADDR+0x0C set t_cs_max
`define REG_T_RW_RECOVERY       5'b00100 //BASEADDR+0x10 set t_read_write_recovery
`define REG_T_RWDS_DELAY_LINE   5'b00101 //BASEADDR+0x14 set t_rwds_delay_line
`define REG_T_VARI_LATENCY      5'b00110 //BASEADDR+0x18 set t_variable_latency_check
`define N_HYPER_DEVICE          5'b00111 //BASEADDR+0x1C set the number of connected devices
`define MEM_SEL                 5'b01000 //BASEADDR+0x20 set Memory select: HyperRAM, Hyperflash, or PSRAM 00:Hyper RAM, 01: Hyper Flash, 10:PSRAM
`define TRANS_ID_ALLOC          5'b01001 //BASEADDR+0x30 set 2D transfer stride

//`define AXI_VERBOSE

`include "axi/assign.svh"
`include "axi/typedef.svh"
`include "register_interface/typedef.svh"

module fixture_hyperbus #(
    parameter int unsigned NumChips = 2,
    parameter int unsigned NumPhys = 2
);

   
    int unsigned            k, j;

    localparam time SYS_TCK  = 8ns;
    localparam time SYS_TA   = 1ns;
    localparam time SYS_TT   = SYS_TCK - 1ns;

    localparam time PHY_TCK  = 4ns;
   
    logic sys_clk      = 0;
    logic phy_clk      = 0;
    logic test_mode    = 0;
    logic rst_n        = 1;
    logic eos          = 0; // end of sim

    // -------------------- AXI drivers --------------------

    localparam AxiAw  = 32;
    localparam AxiDw  = 64;
    localparam AxiMaxSize = $clog2(AxiDw/8);
    localparam AxiIw  = 6;
    localparam RegAw  = 32;
    localparam RegDw  = 32;

    typedef axi_pkg::xbar_rule_32_t rule_t;

    typedef logic [AxiAw-1:0]   axi_addr_t;
    typedef logic [AxiDw-1:0]   axi_data_t;
    typedef logic [AxiDw/8-1:0] axi_strb_t;
    typedef logic [AxiIw-1:0]   axi_id_t;

    `AXI_TYPEDEF_AW_CHAN_T(aw_chan_t, axi_addr_t, axi_id_t, logic [0:0])
    `AXI_TYPEDEF_W_CHAN_T(w_chan_t, axi_data_t, axi_strb_t, logic [0:0])
    `AXI_TYPEDEF_B_CHAN_T(b_chan_t, axi_id_t, logic [0:0])
    `AXI_TYPEDEF_AR_CHAN_T(ar_chan_t, axi_addr_t, axi_id_t, logic [0:0])
    `AXI_TYPEDEF_R_CHAN_T(r_chan_t, axi_data_t, axi_id_t, logic [0:0])
    `AXI_TYPEDEF_REQ_T(req_t, aw_chan_t, w_chan_t, ar_chan_t)
    `AXI_TYPEDEF_RESP_T(resp_t, b_chan_t, r_chan_t)

    req_t   axi_master_req;
    resp_t  axi_master_rsp;

    AXI_BUS_DV #(
        .AXI_ADDR_WIDTH(AxiAw ),
        .AXI_DATA_WIDTH(AxiDw ),
        .AXI_ID_WIDTH  (AxiIw ),
        .AXI_USER_WIDTH(1     )
    ) axi_dv(sys_clk);

    AXI_BUS #(
        .AXI_ADDR_WIDTH(AxiAw ),
        .AXI_DATA_WIDTH(AxiDw ),
        .AXI_ID_WIDTH  (AxiIw ),
        .AXI_USER_WIDTH(1     )
    ) axi_master();

    `AXI_ASSIGN(axi_master, axi_dv)

    `AXI_ASSIGN_TO_REQ(axi_master_req, axi_master)
    `AXI_ASSIGN_FROM_RESP(axi_master, axi_master_rsp)

    typedef axi_test::axi_driver #(.AW(AxiAw ), .DW(AxiDw ), .IW(AxiIw ), .UW(1), .TA(SYS_TA), .TT(SYS_TT)) axi_drv_t;
    axi_drv_t axi_master_drv = new(axi_dv);

    axi_test::axi_ax_beat #(.AW(AxiAw ), .IW(AxiIw ), .UW(1)) ar_beat = new();
    axi_test::axi_r_beat  #(.DW(AxiDw ), .IW(AxiIw ), .UW(1)) r_beat  = new();
    axi_test::axi_ax_beat #(.AW(AxiAw ), .IW(AxiIw ), .UW(1)) aw_beat = new();
    axi_test::axi_w_beat  #(.DW(AxiDw ), .UW(1))              w_beat  = new();
    axi_test::axi_b_beat  #(.IW(AxiIw ), .UW(1))              b_beat  = new();

    // -------------------------- Regbus driver --------------------------

    typedef logic [RegAw-1:0]   reg_addr_t;
    typedef logic [RegDw-1:0]   reg_data_t;
    typedef logic [RegDw/8-1:0] reg_strb_t;

    `REG_BUS_TYPEDEF_REQ(reg_req_t, reg_addr_t, reg_data_t, reg_strb_t)
    `REG_BUS_TYPEDEF_RSP(reg_rsp_t, reg_data_t)

    logic [AxiDw-1:0] trans_wdata;
    logic [AxiDw-1:0] trans_rdata;
    axi_addr_t    temp_waddr;
    axi_addr_t    temp_raddr;
    logic [4:0]   last_waddr;
    logic [4:0]   last_raddr;
    typedef logic [AxiDw-1:0] data_t;   
    data_t        memory[bit [31:0]];
    int           read_index = 0;
    int           write_index = 0;
   
   
    reg_req_t   reg_req;
    reg_rsp_t   reg_rsp;

    REG_BUS #(
        .ADDR_WIDTH( RegAw ),
        .DATA_WIDTH( RegDw )
    ) i_rbus (
        .clk_i (sys_clk)
    );
    integer fr, fw;

    reg_test::reg_driver #(
        .AW ( RegAw  ),
        .DW ( RegDw  ),
        .TA ( SYS_TA ),
        .TT ( SYS_TT )
    ) i_rmaster = new( i_rbus );

`ifdef TARGET_POST_SYNTH_SIM
    assign reg_req = reg_req_t'{
        addr:   $isunknown(i_rbus.addr ) ? 1'b0 : i_rbus.addr ,
        write:  $isunknown(i_rbus.write) ? 1'b0 : i_rbus.write,
        wdata:  $isunknown(i_rbus.wdata) ? 1'b0 : i_rbus.wdata,
        wstrb:  $isunknown(i_rbus.wstrb) ? 1'b0 : i_rbus.wstrb,
        valid:  $isunknown(i_rbus.valid) ? 1'b0 : i_rbus.valid
    };
`else 
    assign reg_req = reg_req_t'{
        addr:   i_rbus.addr,
        write:  i_rbus.write,
        wdata:  i_rbus.wdata,
        wstrb:  i_rbus.wstrb,
        valid:  i_rbus.valid
    };
`endif
   
    assign i_rbus.rdata = reg_rsp.rdata;
    assign i_rbus.ready = reg_rsp.ready;
    assign i_rbus.error = reg_rsp.error;

    // -------------------------- UDMA test --------------------

    localparam L2_AWIDTH_NOAL = 12;
    localparam TRANS_SIZE = 16;
    localparam BYTE_WIDTH = 8;
    localparam MEM_DEPTH = 4096;
    localparam NB_CH=1;
     
    logic [31:0]            rx_data_udma_o;
    logic                   rx_valid_udma_o;
    logic                   rx_ready_udma_i;
    
    logic [31:0]            tx_data_udma_i;
    logic                   tx_valid_udma_i;
    logic                   tx_valid_udma_d;
    logic                   tx_valid_udma2_i;
    logic                   tx_ready_udma_o;
    
    logic [31:0]            cfg_data_i;
    logic [4:0]             cfg_addr_i;
    logic [NB_CH:0]         cfg_valid_i;
    logic                   cfg_rwn_i;
    logic [NB_CH:0][31:0]   cfg_data_o;
    logic [NB_CH:0]         cfg_ready_o;
    
    logic [L2_AWIDTH_NOAL-1:0] cfg_rx_startaddr_o;
    logic [TRANS_SIZE-1:0]     cfg_rx_size_o;
    logic [1:0]                cfg_rx_datasize_o;
    logic                      cfg_rx_continuous_o;
    logic                      cfg_rx_en_o;
    logic                      cfg_rx_clr_o;
    logic                      cfg_rx_en_i;
    logic                      cfg_rx_pending_i;
    logic [L2_AWIDTH_NOAL-1:0] cfg_rx_curr_addr_i;
    logic [TRANS_SIZE-1:0]     cfg_rx_bytes_left_i;
    
    logic [L2_AWIDTH_NOAL-1:0] cfg_tx_startaddr_o;
    logic [TRANS_SIZE-1:0]     cfg_tx_size_o;
    logic [1:0]                cfg_tx_datasize_o;
    logic                      cfg_tx_continuous_o;
    logic                      cfg_tx_en_o;
    logic                      cfg_tx_clr_o;
    logic                      cfg_tx_en_i;
    logic                      cfg_tx_pending_i;
    logic [L2_AWIDTH_NOAL-1:0] cfg_tx_curr_addr_i;
    logic [TRANS_SIZE-1:0]     cfg_tx_bytes_left_i;
    logic [31:0]               count;
    
    logic [BYTE_WIDTH-1:0]     data_mem [0:MEM_DEPTH-1]; // 4KB data mem
    logic [31:0]               udma_sent_word[0:MEM_DEPTH-1];
   
    logic [L2_AWIDTH_NOAL-1:0] data_mem_addr;
    logic [L2_AWIDTH_NOAL-1:0] r_tx_addr;
    logic [31:0]               mem_data_out;
    logic [31:0]               mem_data_out_d;
    logic [31:0]               data_count;
    logic [31:0]               rx_data_count;
    logic [31:0]               tran_size;
    logic [31:0]               tran_size32;
    logic [TRANS_SIZE-1:0]     r_tx_size;
    logic                      r_write_tran_en;
    logic                      r_rx_en;
    logic                      s_req_o;
    logic [31:0]               udma_rx_last_addr;
   
   // Data memory for test
   /////////////////////////////////////////////////
   //                    MEMORY                   //
   /////////////////////////////////////////////////
    assign mem_data_out = { data_mem[data_mem_addr+3], data_mem[data_mem_addr+2], data_mem[data_mem_addr+1], data_mem[data_mem_addr]};
 
    always @(posedge sys_clk or negedge rst_n)
      begin
        if(!rst_n)
          begin
            r_write_tran_en <= 0;
            r_tx_size <=0;
          end
        else
          begin
            if( cfg_tx_en_o & (data_count == 0))
              begin
                r_write_tran_en <= cfg_tx_en_o;
                r_tx_size <= cfg_tx_size_o;
              end
            else
              begin
                if(data_count >= r_tx_size) r_write_tran_en <= 0;
              end
          end
      end
    
     assign cfg_tx_bytes_left_i = (r_write_tran_en)? r_tx_size - data_count: 0;

     always  @(posedge sys_clk or negedge rst_n)
       begin
         if(!rst_n)
           begin
              data_count <=0;
              tx_valid_udma_i <= 1'b0;
           end
         else
           begin
             if(r_write_tran_en)
                 if(tx_ready_udma_o)
                   begin
                     if(tx_valid_udma_i == 1'b1 & (data_count < r_tx_size))
                       begin
                        data_count <= data_count +4;
                       end
                     else
                        if((data_count < r_tx_size))tx_valid_udma_i <= 1'b1;
                        else tx_valid_udma_i <= 1'b0;
                   end
                 else
                   begin
                     //tx_valid_udma_i <= 1'b0;
                   end
             else
               begin
                 data_count <=0;
                 tx_valid_udma_i <= 1'b0;
               end
           end
       end
    
     always @(posedge sys_clk or negedge rst_n)
       begin
         if(!rst_n)
           begin
             data_mem_addr <= 0;
           end
         else
           begin
             if( cfg_tx_en_o & data_count ==0) 
               begin
                  data_mem_addr <= cfg_tx_startaddr_o;
               end 
             else
               begin
                 if(r_write_tran_en & tx_ready_udma_o & tx_valid_udma_i)
                    data_mem_addr <= data_mem_addr +4;
               end
           end
       end
    
    assign cfg_rx_en_i = cfg_rx_en_o | r_rx_en;
    always @(posedge sys_clk or negedge rst_n)
      begin
        if(!rst_n)
          begin
            r_rx_en <= 1'b0;
          end
        else
          begin
            if(cfg_rx_en_o & (cfg_rx_size_o!=0)) r_rx_en <= 1'b1;
            else if((r_rx_en==1'b1) & (cfg_rx_bytes_left_i==0)) r_rx_en <=0;
          end
    end

    // Data check;
    assign tran_size32 = (tran_size%4==0)? tran_size/4 : tran_size/4+1;
    always @(posedge sys_clk or negedge rst_n)
      begin
        if(!rst_n)
          begin
            rx_data_count <= 0;
          end
        else
          begin
            if (cfg_rx_en_o) begin
              udma_rx_last_addr <= cfg_rx_startaddr_o + cfg_rx_size_o;
              rx_data_count <= cfg_rx_startaddr_o;
             end
            if(rx_valid_udma_o)
              begin
                if(rx_data_udma_o !=  {data_mem[rx_data_count+3], data_mem[rx_data_count+2], data_mem[rx_data_count+1], data_mem[rx_data_count]})
                  begin
                    if(rx_data_udma_o>udma_rx_last_addr) begin
                       if(cfg_rx_size_o[1:0]==3)
                         if(rx_data_udma_o[23:0]!={data_mem[rx_data_count+2], data_mem[rx_data_count+1], data_mem[rx_data_count]})
                            $fatal(1,"Error at %d. %h instead of %h", rx_data_count, rx_data_udma_o[23:0], {data_mem[rx_data_count+2], data_mem[rx_data_count+1], data_mem[rx_data_count]});
                       if(cfg_rx_size_o[1:0]==2)
                         if(rx_data_udma_o[15:0]!={data_mem[rx_data_count+1], data_mem[rx_data_count]})
                            $fatal(1,"Error at %d. %h instead of %h", rx_data_count, rx_data_udma_o[15:0], {data_mem[rx_data_count+1], data_mem[rx_data_count]});
                       if(cfg_rx_size_o[1:0]==1)
                         if(rx_data_udma_o[7:0]!={data_mem[rx_data_count]})
                            $fatal(1,"Error at %d. %h instead of %h", rx_data_count, rx_data_udma_o[7:0], data_mem[rx_data_count]);
                    end else begin
                       $fatal(1,"Error at %d. %h instead of %h", rx_data_count, rx_data_udma_o, {data_mem[rx_data_count+3], data_mem[rx_data_count+2], data_mem[rx_data_count+1], data_mem[rx_data_count]});
                    end
                  end
                if(rx_data_count == tran_size32 -1) rx_data_count <=0;
                else rx_data_count <= rx_data_count +4;
              end
          end
    end
   
  assign #(SYS_TCK/6) mem_data_out_d  =  mem_data_out;
  assign #(SYS_TCK/6) tx_valid_udma_d = tx_valid_udma_i;
   
    // -------------------------- DUT --------------------------
    wire  [NumPhys-1:0][1:0] hyper_cs_n_wire;
    wire  [NumPhys-1:0]      hyper_ck_wire;
    wire  [NumPhys-1:0]      hyper_ck_n_wire;
    wire  [NumPhys-1:0]      hyper_rwds_o;
    wire  [NumPhys-1:0]      s_hyper_rwds_i;
    wire  [NumPhys-1:0]      hyper_rwds_i;
    wire  [NumPhys-1:0]      hyper_rwds_oe;
    wire  [NumPhys-1:0]      hyper_rwds_wire;
    wire  [NumPhys-1:0]      s_hyper_rwds_wire;
    wire  [NumPhys-1:0][7:0] hyper_dq_i;
    wire  [NumPhys-1:0][7:0] hyper_dq_o;
    wire  [NumPhys-1:0]      hyper_dq_oe;
    wire  [NumPhys-1:0][7:0] hyper_dq_wire;
    wire  [NumPhys-1:0]      hyper_reset_n_wire;
             
    generate
       for (genvar i=0; i<NumPhys; i++) begin : hyperrams

          s27ks0641 #(
            /*.mem_file_name ( "s27ks0641.mem"    ),*/
            .TimingModel   ( "S27KS0641DPBHI020"    )
          ) i_s27ks0641 (
            .DQ7           ( hyper_dq_wire[i][7]      ),
            .DQ6           ( hyper_dq_wire[i][6]      ),
            .DQ5           ( hyper_dq_wire[i][5]      ),
            .DQ4           ( hyper_dq_wire[i][4]      ),
            .DQ3           ( hyper_dq_wire[i][3]      ),
            .DQ2           ( hyper_dq_wire[i][2]      ),
            .DQ1           ( hyper_dq_wire[i][1]      ),
            .DQ0           ( hyper_dq_wire[i][0]      ),
            .RWDS          ( hyper_rwds_wire[i]       ),
            .CSNeg         ( hyper_cs_n_wire[i][0]    ),
            .CK            ( hyper_ck_wire[i]         ),
            .CKNeg         ( hyper_ck_n_wire[i]       ),
            .RESETNeg      ( hyper_reset_n_wire[i]    )
          );

       end // block: hyperrams
    endgenerate
   
    // DUT
    hyperbus #(
        .NumChips       ( NumChips    ),
        .NumPhys        ( NumPhys     ),
        .AxiAddrWidth   ( AxiAw       ),
        .AxiDataWidth   ( AxiDw       ),
        .AxiIdWidth     ( AxiIw       ),
        .AxiUserWidth   ( 1           ),
        .axi_req_t      ( req_t       ),
        .axi_rsp_t      ( resp_t      ),
        .axi_aw_chan_t  ( aw_chan_t   ),
        .axi_w_chan_t   ( w_chan_t    ),
        .axi_b_chan_t   ( b_chan_t    ),
        .axi_ar_chan_t  ( ar_chan_t   ),
        .axi_r_chan_t   ( r_chan_t    ),
        .RegAddrWidth   ( RegAw       ),
        .RegDataWidth   ( RegDw       ),
        .reg_req_t      ( reg_req_t   ),
        .reg_rsp_t      ( reg_rsp_t   ),
        .IsClockODelayed( 0           ),
        .NB_CH          ( NB_CH       ),
        .axi_rule_t     ( rule_t      )
    ) i_dut (
        .clk_phy_i              ( phy_clk               ),
        .rst_phy_ni             ( rst_n                 ),
        .clk_sys_i              ( sys_clk               ),
        .rst_sys_ni             ( rst_n                 ),
        .test_mode_i            ( test_mode             ),
        .axi_req_i              ( axi_master_req        ),
        .axi_rsp_o              ( axi_master_rsp        ),
        .reg_req_i              ( reg_req               ),
        .reg_rsp_o              ( reg_rsp               ),

        .data_rx_o              ( rx_data_udma_o        ),
        .data_rx_valid_o        ( rx_valid_udma_o       ),
        .data_rx_ready_i        ( 1'b1                  ),
        
        .data_tx_i              ( mem_data_out_d        ),
        .data_tx_valid_i        ( tx_valid_udma_d       ),
        .data_tx_ready_o        ( tx_ready_udma_o       ),
        .data_tx_gnt_i          ( s_req_o               ),
        .data_tx_req_o          ( s_req_o               ),
        
        .cfg_data_i             ( cfg_data_i            ),
        .cfg_addr_i             ( cfg_addr_i            ),
        .cfg_valid_i            ( cfg_valid_i           ),
        .cfg_rwn_i              ( cfg_rwn_i             ),
        .cfg_data_o             ( cfg_data_o            ),
        .cfg_ready_o            ( cfg_ready_o           ),
        
        .cfg_rx_startaddr_o     ( cfg_rx_startaddr_o    ),
        .cfg_rx_size_o          ( cfg_rx_size_o         ),
        .data_rx_datasize_o     ( cfg_rx_datasize_o     ),
        .cfg_rx_continuous_o    ( cfg_rx_continuous_o   ),
        .cfg_rx_en_o            ( cfg_rx_en_o           ),
        .cfg_rx_clr_o           ( cfg_rx_clr_o          ),
        .cfg_rx_en_i            ( cfg_rx_en_i           ),
        .cfg_rx_pending_i       ( cfg_rx_pending_i      ),
        .cfg_rx_curr_addr_i     ( cfg_rx_curr_addr_i    ),
        .cfg_rx_bytes_left_i    ( cfg_rx_bytes_left_i   ),
        
        .cfg_tx_startaddr_o     ( cfg_tx_startaddr_o    ),
        .cfg_tx_size_o          ( cfg_tx_size_o         ),
        .data_tx_datasize_o     ( cfg_tx_datasize_o     ),
        .cfg_tx_continuous_o    ( cfg_tx_continuous_o   ),
        .cfg_tx_en_o            ( cfg_tx_en_o           ),
        .cfg_tx_clr_o           ( cfg_tx_clr_o          ),
        .cfg_tx_en_i            ( r_write_tran_en       ),
        .cfg_tx_pending_i       ( cfg_tx_pending_i      ),
        .cfg_tx_curr_addr_i     ( cfg_tx_curr_addr_i    ),
        .cfg_tx_bytes_left_i    ( cfg_tx_bytes_left_i   ),

        .evt_eot_hyper_o        (                       ),
             
        .pad_hyper_csn          ( hyper_cs_n_wire       ),
        .pad_hyper_ck           ( hyper_ck_wire         ),
        .pad_hyper_ckn          ( hyper_ck_n_wire       ),
        .pad_hyper_rwds         ( hyper_rwds_wire       ),
        .pad_hyper_reset        ( hyper_reset_n_wire    ),
        .pad_hyper_dq           ( hyper_dq_wire         )

    );

    
    generate
       for (genvar p=0; p<NumPhys; p++) begin : sdf_annotation
         initial begin
             `ifndef TARGET_POST_SYNTH_SIM
             automatic string sdf_file_path = "../models/s27ks0641/s27ks0641.sdf";
             `else
             automatic string sdf_file_path = "../../models/s27ks0641/s27ks0641.sdf";
             `endif
             $sdf_annotate(sdf_file_path, hyperrams[p].i_s27ks0641);
             $display("NumPhys:%d",NumPhys);
         end
       end
    endgenerate
   

    // -------------------------- TB TASKS --------------------------

   
     class SetConfig;
        int cfg_address;
        int cfg_data;
        int cfg_valid = 0;
        int cfg_rwn = 1;

     function new (int cfg_address, int cfg_data);
        this.cfg_address = cfg_address;
        this.cfg_data = cfg_data;
     endfunction

     task write;
        this.cfg_valid = 1;
        this.cfg_rwn = 0;
     endtask : write

     endclass: SetConfig



    // SystemVerilog "clocking block"
    // Clocking outputs are DUT inputs and vice versa
    default clocking cb_udma_hyper @(negedge sys_clk);
      default input #1step output #1ns;

       
      output cfg_data_i, cfg_addr_i, cfg_valid_i, cfg_rwn_i,  cfg_rx_pending_i, cfg_rx_curr_addr_i,cfg_tx_en_i, cfg_tx_pending_i, cfg_tx_curr_addr_i, cfg_rx_bytes_left_i;
      output tx_data_udma_i, tx_valid_udma_i;
      input cfg_data_o, cfg_ready_o, cfg_rx_startaddr_o, cfg_rx_size_o, cfg_rx_datasize_o, cfg_rx_continuous_o, cfg_rx_en_o, cfg_rx_clr_o;
      input cfg_tx_startaddr_o, cfg_tx_size_o, cfg_tx_continuous_o, cfg_tx_en_o, cfg_tx_clr_o;

    endclocking

    clocking cb_hyper_phy @(posedge phy_clk);
      default input #1step output #1ns;
      output negedge rst_n;

    endclocking

    SetConfig sconfig;

    // Initial reset
    initial begin
        rst_n = 0;

        `ifndef TARGET_POST_SYNTH_SIM
        $readmemh("../test/test_mem.dat",data_mem); 
        `else
        $readmemh("../../test/test_mem.dat",data_mem); 
        `endif
        // Set all inputs at the beginning    

        // Will be applied on negedge of clock!
        cb_udma_hyper.cfg_addr_i <=0;
        cb_udma_hyper.cfg_valid_i <= '0;
        cb_udma_hyper.cfg_data_i <= 0;

        // Will be applied 4ns after the clock!

        cb_udma_hyper.cfg_rwn_i<=0;
        cb_udma_hyper.cfg_valid_i<=0;
        cfg_rx_bytes_left_i <= 0;
        cfg_rx_pending_i<=0;
        cfg_rx_curr_addr_i<=0;
        cfg_tx_pending_i<=0;
        cfg_tx_en_i<=0;
        cfg_tx_curr_addr_i<=0;

        tran_size <= 'h200;
        axi_master_drv.reset_master();
        fr = $fopen ("axireadvalues.txt","w");
        fw = $fopen ("axiwrotevalues.txt","w");
        i_rmaster.reset_master();
        #(0.25*SYS_TCK);
        #(10*SYS_TCK);
        rst_n = 1;
    end

    // Generate clock
    initial begin
        while (!eos) begin
            sys_clk = 1;
            #(SYS_TCK/2);
            sys_clk = 0;
            #(SYS_TCK/2);
        end
        // Extra cycle after sim
        sys_clk = 1;
        #(SYS_TCK/2);
        sys_clk = 0;
        #(SYS_TCK/2);
    end

    // Generate clock
    initial begin
        while (!eos) begin
            phy_clk = 1;
            #(PHY_TCK/2);
            phy_clk = 0;
            #(PHY_TCK/2);
        end
        // Extra cycle after sim
        phy_clk = 1;
        #(PHY_TCK/2);
        phy_clk = 0;
        #(PHY_TCK/2);
    end
 

    task reset_end;
        @(posedge rst_n);
        @(posedge sys_clk);
    endtask

    // axi read task
    task read_axi;
        input axi_addr_t      raddr;
        input axi_pkg::len_t  burst_len;
        input axi_pkg::size_t size;

        @(posedge sys_clk);

        ar_beat.ax_addr  = raddr;
        ar_beat.ax_len   = burst_len;
        ar_beat.ax_burst = axi_pkg::BURST_INCR;
        ar_beat.ax_size  = size;

        if(ar_beat.ax_size>AxiMaxSize) begin
          $display("Not supported");
        end else begin
                     
          axi_master_drv.send_ar(ar_beat);
          $display("%p", ar_beat);

          temp_raddr = raddr;
          last_raddr = '0;
                
          for(int unsigned i = 0; i < burst_len + 1; i++) begin
              axi_master_drv.recv_r(r_beat);
              `ifdef AXI_VERBOSE
              $display("%p", r_beat);
              $display("%x", r_beat.r_data);
              `endif
              trans_rdata = '1;
              if (i==0) begin
                 for(k =temp_raddr[AxiMaxSize-1:0]; k<((temp_raddr[AxiMaxSize-1:0]>>size)<<size) + (2**size) ; k++) begin 
                   trans_rdata[k*8 +:8] = r_beat.r_data[(k*8) +: 8];
                 end
              end else begin
                 for(j=temp_raddr[AxiMaxSize-1:0]; j<temp_raddr[AxiMaxSize-1:0]+(2**size); j++) begin
                    trans_rdata[j*8 +:8] = r_beat.r_data[(j*8) +: 8];
                 end
              end
              $fwrite(fr, "%x %x %d\n", trans_rdata, temp_raddr, (((temp_raddr[AxiMaxSize-1:0]>>size)<<size) + (2**size)));
              if(memory[read_index]!=trans_rdata) begin
                 $fatal(1,"Error @%x (read_index: %d). Expected: %x, got: %x\n", temp_raddr, read_index, memory[read_index], trans_rdata);
              end
              if($isunknown(trans_rdata)) begin
                 $fatal(1,"Xs @%x\n",temp_raddr);
              end   
              read_index++;
              if(i==0)
                temp_raddr = ((temp_raddr>>size)<<size) + (2**size);
              else
                temp_raddr = temp_raddr + (2**size);    
              last_raddr = temp_raddr[AxiMaxSize-1:0] + (2**size);       
          end // for (int unsigned i = 0; i < burst_len + 1; i++)
        end
       
    endtask

    // axi write task
    task write_axi;
        input axi_addr_t      waddr;
        input axi_pkg::len_t  burst_len;
        input axi_pkg::size_t size;
        input logic           clear;
        input axi_strb_t      wstrb;

        @(posedge sys_clk);

        temp_waddr = waddr;
        aw_beat.ax_addr  = waddr;
        aw_beat.ax_len   = burst_len;
        aw_beat.ax_burst = axi_pkg::BURST_INCR;
        aw_beat.ax_size  = size;
       
        w_beat.w_strb   = wstrb;
        w_beat.w_last   = 1'b0;
        last_waddr = '0;

        if(aw_beat.ax_size>AxiMaxSize) begin
          $display("Not supported");
        end else begin
          $display("%p", aw_beat);

          axi_master_drv.send_aw(aw_beat);
          
          
          for(int unsigned i = 0; i < burst_len + 1; i++) begin
              if (i == burst_len) begin
                  w_beat.w_last = 1'b1;
              end
              if(clear)
                w_beat.w_data = '1;
              else
                randomize(w_beat.w_data);
              axi_master_drv.send_w(w_beat);
              trans_wdata = '1; //the memory regions where we do not write are have all ones in the hyperram.
              `ifdef AXI_VERBOSE
              $display("%p", w_beat);
              $display("%x", w_beat.w_data);
              `endif
              if (i==0) begin
                 for (k = temp_waddr[AxiMaxSize-1:0]; k<(((temp_waddr[AxiMaxSize-1:0]>>size)<<size) + (2**size)) ; k++)  begin
                   trans_wdata[k*8 +:8] = (wstrb[k]) ? w_beat.w_data[(k*8) +: 8] : '1;
                 end
              end else begin
                 for(j=temp_waddr[AxiMaxSize-1:0]; j<temp_waddr[AxiMaxSize-1:0]+(2**size); j++) begin
                    trans_wdata[j*8 +:8] = (wstrb[j]) ? w_beat.w_data[(j*8) +: 8] : '1;
                 end
              end
              $fwrite(fw, "%x %x %x %d %d \n",  w_beat.w_data, trans_wdata, temp_waddr, (((temp_waddr[AxiMaxSize-1:0]>>size)<<size) + (2**size)), write_index);
              memory[write_index]=trans_wdata;
              if($isunknown(trans_wdata)) begin
                 $fatal(1,"Xs @%x\n",temp_waddr);
              end   
              write_index++;
              if(i==0)
                temp_waddr = ((temp_waddr>>size)<<size) + (2**size);
              else
                temp_waddr = temp_waddr + (2**size);
              last_waddr = temp_waddr[AxiMaxSize-1:0] + (2**size);
          end // for (int unsigned i = 0; i < burst_len + 1; i++)
          
          axi_master_drv.recv_b(b_beat);
        end 
       
    endtask

    task WriteConfig(SetConfig sconfig, int id);

        cb_udma_hyper.cfg_addr_i <= sconfig.cfg_address;
        cb_udma_hyper.cfg_data_i <= sconfig.cfg_data;
        cb_udma_hyper.cfg_valid_i[id] <= 1;
        cb_udma_hyper.cfg_rwn_i <= 0;
        wait(cb_udma_hyper.cfg_ready_o);
        #SYS_TCK;
        cb_udma_hyper.cfg_valid_i[id] <= 0;
        #SYS_TCK;
     endtask : WriteConfig


    task LongWriteTransactionTest(int mem_address_i, int l2_address, int length_i, int id);

        automatic int mem_address;
        automatic int length;
                         
        automatic int count2=0;
        automatic int burst_size_32=0;
        if((length%4)==0) burst_size_32 = length/4;
        else burst_size_32 = length/4 +1;

        mem_address = mem_address_i;
        length = length_i;
                 
        $display("Request from tb: L3 addr: %d, l2_addr %d, length %d", mem_address_i, l2_address, length_i);
                         
        // Check the transaction is compliant
        if(NumPhys==2) begin
          if(length_i%2!=0) begin
             `ifdef UDMA_VERBOSE
             $display("Not supported. Length of writes/reads with udma need to be aligned to 16 bits");
             `endif
             length = (length_i>>1)<<1;
          end                       
        end 
                         
        if(length_i<4) begin
           `ifdef UDMA_VERBOSE
           $display("Not supported. Length of writes/reads with udma need to be aligned to > 32 bits");
           `endif
           length = 4;
        end
                         
        $display("Issued         : L3 addr: %d, l2_addr %d, length %d", mem_address, l2_address, length);

          sconfig = new(`REG_T_RWDS_DELAY_LINE,32'h00000004);
          WriteConfig(sconfig,1);
          sconfig = new(`REG_EN_LATENCY_ADD,32'h00000001);
          WriteConfig(sconfig,1);
          sconfig = new(`REG_PAGE_BOUND, 32'h00000004);
          WriteConfig(sconfig,1);
          if(NumPhys==2) begin
             sconfig = new(`MEM_SEL, 32'h00000003);
             WriteConfig(sconfig,1);
          end
          sconfig = new(`TWD_ACT_L2, 32'h000000);
          WriteConfig(sconfig,id);
          sconfig = new(`TWD_COUNT_L2, 32'h000000);
          WriteConfig(sconfig,id);
          sconfig = new(`TWD_STRIDE_L2,32'h000000);
          WriteConfig(sconfig,id);
          sconfig = new(`TWD_ACT_EXT, 32'h000000);
          WriteConfig(sconfig,id);
          sconfig = new(`TWD_COUNT_EXT, 32'h000000);
          WriteConfig(sconfig,id);
          sconfig = new(`TWD_STRIDE_EXT,32'h000000);
          WriteConfig(sconfig,id);
          
          sconfig = new(`REG_T_CS_MAX, 32'hffffffff); // un_limit burst length
          WriteConfig(sconfig,1);
          sconfig = new(`REG_TX_SADDR, l2_address); // TX Start address
          WriteConfig(sconfig,id);
          sconfig = new(`REG_TX_SIZE, length); // TX size in byte
          WriteConfig(sconfig,id);
          sconfig = new(`REG_HYPER_ADDR, mem_address); // Mem address
          WriteConfig(sconfig,id);
          sconfig = new(`HYPER_CA_SETUP, 32'h000001); // Write is declared.
          WriteConfig(sconfig,id);
          sconfig = new(`REG_UDMA_TXCFG, 32'h0000014); // Write transaction is kicked 
          WriteConfig(sconfig,id);
          
          #(SYS_TCK*burst_size_32);
          #(SYS_TCK*burst_size_32);
          
          sconfig = new(`REG_PAGE_BOUND, 32'h00000004);
          WriteConfig(sconfig,1);
          sconfig = new(`REG_UDMA_TXCFG, 32'h0000000); // Write transaction ends
          WriteConfig(sconfig,id);
          #3us;
          ReadTransaction(mem_address,l2_address,length, id);
          cb_udma_hyper.cfg_rx_bytes_left_i <= length;
          wait(rx_valid_udma_o);
          count2 = 0;
          #(SYS_TCK*burst_size_32*2);
        

    endtask : LongWriteTransactionTest

    task ReadTransaction(int mem_address, int l2_address, int length, int id);
        sconfig = new(`TWD_ACT_L2, 32'h000000);
        WriteConfig(sconfig,id);
        sconfig = new(`TWD_COUNT_L2, 32'h000000);
        WriteConfig(sconfig,id);
        sconfig = new(`TWD_STRIDE_L2,32'h000000);
        WriteConfig(sconfig,id);
        sconfig = new(`TWD_ACT_EXT, 32'h000000);
        WriteConfig(sconfig,id);
        sconfig = new(`TWD_COUNT_EXT, 32'h000000);
        WriteConfig(sconfig,id);
        sconfig = new(`TWD_STRIDE_EXT,32'h000000);
        WriteConfig(sconfig,id);

        sconfig = new(`REG_RX_SADDR, l2_address); // RX Start address
        WriteConfig(sconfig,id);
        sconfig = new(`REG_RX_SIZE, length); // TX size in byte
        WriteConfig(sconfig,id);
        sconfig = new(`REG_HYPER_ADDR, mem_address); // Mem address
        WriteConfig(sconfig,id);
        sconfig = new(`HYPER_CA_SETUP, 32'h000005); // Read is declared
        WriteConfig(sconfig,id);

        sconfig = new(`REG_UDMA_RXCFG, 32'h000014); // Read transaction is kicked
        WriteConfig(sconfig,id);

    endtask : ReadTransaction

    task RegTransaction();
 
        sconfig = new(`REG_PAGE_BOUND, 32'h00000004);
        WriteConfig(sconfig,1);
        sconfig = new(`REG_HYPER_ADDR, 32'h000000); // ID0 reg
        WriteConfig(sconfig,1);
        sconfig = new(`HYPER_CA_SETUP, 32'h000006); // Reg read is declared
        WriteConfig(sconfig,1);
        sconfig = new(`REG_RX_SIZE, 2); // Read size in byte
        WriteConfig(sconfig,1);
        sconfig = new(`REG_UDMA_RXCFG, 32'h000014); // Read transaction is kicked
        WriteConfig(sconfig,1);
        cb_udma_hyper.cfg_rx_bytes_left_i <= 2;
        wait(rx_valid_udma_o);
        cb_udma_hyper.cfg_rx_bytes_left_i <= 0;
        #(SYS_TCK*10);
        sconfig = new(`HYPER_CA_SETUP, 32'h000000); // configration is cleared
        WriteConfig(sconfig,1);
  
    
        sconfig = new(`REG_HYPER_ADDR, 32'h000001); // ID1 reg
        WriteConfig(sconfig,1);
        sconfig = new(`HYPER_CA_SETUP, 32'h000006); // Reg read
        WriteConfig(sconfig,1);
        sconfig = new(`REG_RX_SIZE, 2); // Read size in byte
        WriteConfig(sconfig,1);
        sconfig = new(`REG_UDMA_RXCFG, 32'h000014); // Read transaction is kicked
        WriteConfig(sconfig,1);
        cb_udma_hyper.cfg_rx_bytes_left_i <= 2;
        wait(rx_valid_udma_o);
        cb_udma_hyper.cfg_rx_bytes_left_i <= 0;
        #(SYS_TCK*5);
        sconfig = new(`REG_UDMA_RXCFG, 32'h000000); // Read transaction is finished
        WriteConfig(sconfig,1);
        sconfig = new(`HYPER_CA_SETUP, 32'h000000); // configration is cleared
        WriteConfig(sconfig,1);



        sconfig = new(`REG_HYPER_ADDR, 32'h000801); // Config1 reg
        WriteConfig(sconfig,0);
        sconfig = new(`HYPER_CA_SETUP, 32'h000006); // Reg read
        WriteConfig(sconfig,0);
        sconfig = new(`REG_RX_SIZE, 2); // Read size in byte
        WriteConfig(sconfig,0);
        sconfig = new(`REG_UDMA_RXCFG, 32'h000014); // Read transaction is kicked
        WriteConfig(sconfig,0);
        cb_udma_hyper.cfg_rx_bytes_left_i <= 2;
        wait(rx_valid_udma_o);
        cb_udma_hyper.cfg_rx_bytes_left_i <= 0;
        #(SYS_TCK*5);
        sconfig = new(`REG_UDMA_RXCFG, 32'h000000); // Read transaction is finished
        WriteConfig(sconfig,1);
        sconfig = new(`HYPER_CA_SETUP, 32'h000000); // configration is cleared
        WriteConfig(sconfig,1);


        sconfig = new(`REG_HYPER_ADDR, 32'h000800); // Config0 reg
        WriteConfig(sconfig,1);
        sconfig = new(`REG_HYPER_CFG, 16'b1011111100010100); // Write data setup
        WriteConfig(sconfig,1);
        sconfig = new(`HYPER_CA_SETUP, 32'h000002); // Reg Write is declared
        WriteConfig(sconfig,1);
        sconfig = new(`REG_UDMA_TXCFG, 32'h0000014); // Write transaction is kicked 
        WriteConfig(sconfig,1);
        sconfig = new(`HYPER_CA_SETUP, 32'h000000); // Reg Write finished
        WriteConfig(sconfig,1);
        #(SYS_TCK*5);

        sconfig = new(`REG_HYPER_ADDR, 32'h000800); // Config0 reg
        WriteConfig(sconfig,1);
        sconfig = new(`HYPER_CA_SETUP, 32'h000006); // Reg read
        WriteConfig(sconfig,1);
        sconfig = new(`REG_RX_SIZE, 2); // Read size in byte
        WriteConfig(sconfig,1);
        sconfig = new(`REG_UDMA_RXCFG, 32'h000014); // Read transaction is kicked
        WriteConfig(sconfig,1);
        cb_udma_hyper.cfg_rx_bytes_left_i <= 2;
        wait(rx_valid_udma_o);
        cb_udma_hyper.cfg_rx_bytes_left_i <= 0;
        #(SYS_TCK*5);
        sconfig = new(`REG_UDMA_RXCFG, 32'h000000); // Read transaction is finished
        WriteConfig(sconfig,1);
        sconfig = new(`HYPER_CA_SETUP, 32'h000000); // configration is cleared
        WriteConfig(sconfig,1);
        #(SYS_TCK*2000);
    endtask: RegTransaction

   
endmodule : fixture_hyperbus


module tristate_shim (
    input  wire out_ena_i,
    input  wire out_i,
    output wire in_o,
    inout  wire line_io
);

    assign line_io = out_ena_i ? out_i : 1'bz;
    assign in_o    = out_ena_i ? 1'bx  : line_io;

endmodule : tristate_shim
