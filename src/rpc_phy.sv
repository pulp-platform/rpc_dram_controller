// Copyright 2022 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Vaibhav Krishna <vakrishna@student.ethz.ch>
// Rui Zhou <ruzhou@student.ethz.ch>
// Chen Jinfan <jinfchen@student.ethz.ch>
// Chen Wang <chewang@student.ethz.ch>
// Jiawei Zhang <jiawzhang@student.ethz.ch>

module rpc_phy #(
  parameter int CLOCK_PERIOD = 5,
  parameter int DRAM_CMD_WIDTH = 32,
  parameter int DRAM_DB_WIDTH = 16,
  parameter int DRAM_WORD_WIDTH = 256,
  parameter int DRAM_MASK_WIDTH = 64
) (

  // ----------------------------------------------------------------------------------------------
  // ----------------------------clock and reset input  -------------------------------------------
  // ----------------------------------------------------------------------------------------------

  input logic               clk_0_i,        // input clock for all PHY operation
  input logic               clk_90_i,       // quadrature phase clock to probe
                                            // the center of the data eye
  input logic               rst_ni,         // Active Low Reset Singal of PHY Module

  input rpc_config_path_pkg::timing_cfg_reg_t   phy_timing_cfg_i,

  // ----------------------------------------------------------------------------------------------
  // ----------------------------Upstream Interface  ----------------------------------------------
  // ----------------------------------------------------------------------------------------------

  //----------------------------Command Path------------------------------
  input logic [DRAM_CMD_WIDTH-1 : 0]    cmd_i,            // Input command coming from the command cmd_fsm
  input logic               cmd_valid_i,       // Hand Shake Signal from cmd_fsm -> rpc_phy
  output logic               cmd_ready_o,       // Hand Shake Signal from cmd_fsm <- rpc_phy

  //----------------------------Data Path---------------------------------
  // Input Datapath Signal
  input logic [DRAM_WORD_WIDTH-1 :0]   data_i,           // Input data coming from DMA
  input logic [DRAM_MASK_WIDTH-1 :0]   mask_i,           // Input burst write mask coming from DMA
  output logic               data_ready_o,      // Tell that the next 256bit WORD can be pushed to the data_i path

  // Output Datapath Signal
  output logic [DRAM_WORD_WIDTH-1 :0]   data_o,           // Data Bus to DMA
  output logic               data_valid_o,     // Hand Shake Signal from dma  <- rpc_phy
  output logic               data_last_o,      // Flag indicating the last data has been trasnferred into DRAM


  // ----------------------------------------------------------------------------------------------
  // ----------------------------RPC DRAM Interface  ----------------------------------------------
  // ----------------------------------------------------------------------------------------------

  // Differential Output CLK Pair
  output logic               clk_o,             // Clock Diff + to RPC DRAM
  output logic               clk_no,            // Clock Diff - to RPC DRAM
  output logic               cs_no,             // CS# to RPC DRAM

  //----------------------------Write Path---------------------------------
  // STB
  output logic               stb_o,             // Serial Command Port STB to RPC DRAM
  // DQS
  output logic               dqs_pair_oe_o,      // DQS/DQSn PAD output enable
  output logic               dqs_pair_ie_o,      // DQS/DQSn PAD input enable
  output logic                            dqs_pair_pd_en_o,   // DQS/DQSn PAD pull down enable
  output logic               dqs_o,             // Write Data Strobe Diff + to RPC DRAM
  output logic               dqs_no,            // Write Data Strobe Diff - to RPC DRAM
  // DB[15:0]
  output logic               db_oe_o,           // CS# to RPC DRAM
  output logic                            db_ie_o,            // DB PAD input enable
  output logic                            db_pd_en_o,         // DB PAD pull down enable
  output logic [DRAM_DB_WIDTH-1 : 0]    db_o,             // Data Bus to RPC DRAM



  //----------------------------Read Path---------------------------------
  input logic               dqs_i,             // Data Strobe Diff + from RPC DRAM
  input logic               dqs_ni,            // Data Strobe Diff - from RPC DRAM
  input logic [DRAM_DB_WIDTH-1 : 0]    db_i,              // Data Bus from RPC DRAM

  input logic               phy_dqs_delay_i

);



  ////////////////////////////////////////////
  ////////// Output path control signal  /////
  ////////////////////////////////////////////

  // Output Strobe Control Signal
  logic dqs_cg_en;
  logic dqs_pair_oe_d, dqs_pair_oe_q;

  // Output Data Selection Signal
  logic [1:0] type_sel;
  logic [2:0] data_sel;
  logic mask_sel;

  // Output DB Bus multiplexing
  logic [DRAM_CMD_WIDTH-1 : 0] mask_int, data_int, db_int;



  ////////////////////////////////////////////
  ////////// INput path control signal  //////
  ////////////////////////////////////////////

  // Input DB BUS De-multiplexing
  // cdc to timing fsm
  logic cdc_dst_valid;

  // timing fsm output
  logic cdc_src_valid;
  logic [2:0] data_sel_rd;
  logic data_valid_d, data_valid_q, data_last_d, data_last_q;


  ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  /////////////////////////////////////////////////////// Timing Control Unit ///////////////////////////////////////////////////////////////////////////////
  ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  //Module Instantiations
  rpc_timing_fsm #(
    .DRAM_CMD_WIDTH(DRAM_CMD_WIDTH),
    .CLOCK_PERIOD  (CLOCK_PERIOD)
  ) i_rpc_timing_fsm (
    .clk_i (clk_0_i),
    .rst_ni(rst_ni),

    // Configuration Path
    .phy_timing_cfg_i(phy_timing_cfg_i),

    // Command Path
    .cmd_i      (cmd_i),
    .cmd_valid_i(cmd_valid_i),
    .cmd_ready_o(cmd_ready_o),

    // DB Path Selection
    .type_sel_o(type_sel),
    .data_sel_o(data_sel),
    .mask_sel_o(mask_sel),

    // Data Path Hand Shaking
    // Write Path
    .data_ready_o   (data_ready_o),
    // Read Path
    .data_valid_o   (data_valid_d),
    .data_last_o    (data_last_d),
    .data_sel_rd    (data_sel_rd),
    .cdc_dst_valid_i(cdc_dst_valid),
    .cdc_src_valid_o(cdc_src_valid),

    // Signal Timing and Sequence COntrol
    .cs_no(cs_no),
    .stb_o(stb_o),

    .dqs_cg_en_o     (dqs_cg_en),
    .dqs_pair_oe_o   (dqs_pair_oe_d),
    .dqs_pair_ie_o   (dqs_pair_ie_o),
    .dqs_pair_pd_en_o(dqs_pair_pd_en_o),

    .db_oe_o   (db_oe_o),
    .db_ie_o   (db_ie_o),
    .db_pd_en_o(db_pd_en_o)
  );


  ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  /////////////////////////////////////////////////////// Output ClocK Generation ///////////////////////////////////////////////////////////////////////////
  ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  // clk_0_i ===> delay_line ===> clk_90 ===> inv ===> clk_270

  logic clk_270;

  // Inverting clk90, clk90_n <=> clk270
  tc_clk_inverter i_tc_clk_inverter_clk_270 (
    .clk_i(clk_90_i),
    .clk_o(clk_270)
  );

  // propagate clk90 and clk90_n
  assign clk_o  = clk_90_i;
  assign clk_no = clk_270;

  // get dqs and dqs_n and propagate
  tc_clk_gating i_tc_clk_gating_dqs_o (
    .clk_i    (clk_90_i),
    .en_i     (dqs_cg_en),
    .test_en_i('0),
    .clk_o    (dqs_o)
  );

  tc_clk_inverter i_tc_clk_inverter_dqs_no (
    .clk_i(dqs_o),
    .clk_o(dqs_no)
  );


  always_ff @(posedge clk_90_i or negedge rst_ni) begin
    if (~rst_ni) begin
      dqs_pair_oe_q <= 0;
    end else begin
      dqs_pair_oe_q <= dqs_pair_oe_d;
    end
  end

  // DQS/DQS# clock output enabling
  assign dqs_pair_oe_o = dqs_pair_oe_q;

  ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  /////////////////////////////////////////////////////// PHY to RPC DRAM Output Datapath////////////////////////////////////////////////////////////////////
  ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


  //////////////////////////////////////////////////
  ////////// Internal SDR to external DDR  /////////
  //////////////////////////////////////////////////

  // Internal Clock and External Double Data Rate Clock Interface
  // db_int is a 32 bit signal used to send the data to be send out within a CLK cycle
  // The upper 16 bit is the data to be sent on positive output clk edge
  // The lower 16 bit is the data to be sent on negative output clk edge
  // clk_mux select whether to transmit upper or lower 16 bit based on output clk
`ifndef FPGA_EMUL
  for (genvar i = 0; i < DRAM_DB_WIDTH; i++) begin
    tc_clk_mux2 i_tc_clk_mux2 (
      .clk0_i   (db_int[i]),
      .clk1_i   (db_int[DRAM_DB_WIDTH+i]),
      .clk_sel_i(clk_0_i),
      .clk_o    (db_o[i])
    );
  end
`else
  for (genvar i = 0; i < DRAM_DB_WIDTH; i++) begin
    assign db_o[i] = (clk_0_i) ? db_int[DRAM_DB_WIDTH+i] : db_int[i];
  end
`endif

  //////////////////////////////////////////////////
  ////////// Data Path Pipeline  ///////////////////
  //////////////////////////////////////////////////


  // The pipeline register which reduces the critical data path from AXI Interface SRAM fifo to the RPC DB Bus output
  // AXI Interface DATA FIFO -> REG BUFFER -> MUX -> RPC DB Port

  logic [DRAM_WORD_WIDTH-1 : 0] data_i_pipe_reg_d, data_i_pipe_reg_q;
  assign data_i_pipe_reg_d = data_i;


  always_ff @(posedge clk_0_i or negedge rst_ni) begin
    if (~rst_ni) begin
      data_i_pipe_reg_q <= '0;
    end else begin
      data_i_pipe_reg_q <= data_i_pipe_reg_d;
    end
  end

  ///////////////////////////////////////////////////
  ////////// Data / Command /Mask Selection  ////////
  ///////////////////////////////////////////////////


  always_comb begin
    // RPC DRAM asks for two burst writing masks, MASK 0 and MASK1
    // One is for masking selected bytes of 1st WORD in a burst write chain
    // One is for masking selected bytes of the last WORD in a burst write chain
    // The mask_sel selects which mask should be output to RPC DRAM now
    // mask_i -- MUX --> mask_int
    // Follows little endian format, mask_sel count down from 1 to 0 inside timing_fsm WR_MASK state
    case (mask_sel)
      1'b1: mask_int = {mask_i[15:0], mask_i[31:16]};
      1'b0: mask_int = {mask_i[47:32], mask_i[63:48]};
      default: mask_int = {mask_i[15:0], mask_i[31:16]};
    endcase

    // The minimum data access quantum for RPC DRAM is a 256bit data chunk called a WORD
    // Since the DRAM has 16 bit data bus, a WORD is sliced and then transferred in 8 consecutive cycles
    // The data_sel select which slice should be transferred
    // The data order now follows Little Endian order, data_sel count down from 1 to 0 inside timing_fsm WR_DATA state
    // At rising edge, push the lower word to DB Bus
    // At falling edge, push the lower word to DB Bus
    case (data_sel)
      3'd7:    data_int = {data_i_pipe_reg_q[15:0], data_i_pipe_reg_q[31:16]};
      3'd6:    data_int = {data_i_pipe_reg_q[47:32], data_i_pipe_reg_q[63:48]};
      3'd5:    data_int = {data_i_pipe_reg_q[79:64], data_i_pipe_reg_q[95:80]};
      3'd4:    data_int = {data_i_pipe_reg_q[111:96], data_i_pipe_reg_q[127:112]};
      3'd3:    data_int = {data_i_pipe_reg_q[143:128], data_i_pipe_reg_q[159:144]};
      3'd2:    data_int = {data_i_pipe_reg_q[175:160], data_i_pipe_reg_q[191:176]};
      3'd1:    data_int = {data_i_pipe_reg_q[207:192], data_i_pipe_reg_q[223:208]};
      3'd0:    data_int = {data_i_pipe_reg_q[239:224], data_i_pipe_reg_q[255:240]};
      default: data_int = {data_i_pipe_reg_q[239:224], data_i_pipe_reg_q[255:240]};
    endcase
    // The db[15:0] is a multi-function bus used to transfer command/data/mask
    // The type_sel determines which info should be output to the DRAM now
    case (type_sel)
      2'b00:   db_int = cmd_i;
      2'b01:   db_int = data_int;
      2'b10:   db_int = mask_int;
      default: db_int = cmd_i;
    endcase
  end


  ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  ///////////////////////////////////////////////////////Begin RPC DRAM to PHY Input Datapath ///////////////////////////////////////////////////////////////
  ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  //////////////////////////////////////////////////
  ////////// Input DDR to Internal SDR  ////////////
  //////////////////////////////////////////////////

  logic [DRAM_CMD_WIDTH/2-1:0] read_low_data_d, read_low_data_q;

  always_comb begin
    read_low_data_d = read_low_data_q;
    if (dqs_i) begin
      read_low_data_d = db_i;
    end
  end

  always_ff @(posedge phy_dqs_delay_i or negedge rst_ni) begin
    if (rst_ni == 1'b0) begin
      read_low_data_q <= '0;
    end else begin
      read_low_data_q <= read_low_data_d;
    end
  end

  logic [DRAM_CMD_WIDTH-1:0] cdc_src_data;
  assign cdc_src_data = {db_i, read_low_data_q};

  /////////////////////////////////////////////////////
  //// Input clock domain to Internal Clock Domain ////
  /////////////////////////////////////////////////////

  logic src_ready_o;
  logic [DRAM_CMD_WIDTH-1:0] dst_data_o;
  logic dst_valid_o;


  cdc_fifo_gray #(
    .WIDTH      (DRAM_CMD_WIDTH),
    .LOG_DEPTH  (3),
    .SYNC_STAGES(2)
  ) i_cdc_fifo (
    // External signal coming from the RPC DRAM
    .src_rst_ni(rst_ni),
    .src_clk_i(phy_dqs_delay_i),  // dqs_i_delay is the DQS,DQS# diff pair coming from RPC DRAM
    .src_data_i (cdc_src_data),       // read_reg_q is the 32bit signal containing both DDR positive and negative edge input data
    .src_valid_i(cdc_src_valid),
    .src_ready_o(src_ready_o),

    // Internal signal to be used by internal PHY logics
    .dst_rst_ni (rst_ni),
    .dst_clk_i  (clk_0_i),      // clk_0_i is PHY internal clock
    .dst_data_o (dst_data_o),   // dst_data_o is clock synchronized input data
    .dst_valid_o(dst_valid_o),
    .dst_ready_i(1'b1)
  );



  //////////////////////////////////////////////////
  ////////// Input Data Assembling  ////////////////
  //////////////////////////////////////////////////

  // // Ignore the first output data
  // logic dst_valid_d, dst_valid_q;
  // assign dst_valid_d = dst_valid_o;

  //logic cdc_read_data_valid;

  // // For a signle 256 data, the CDC output 32 bit garbage + 8*32 bit data, so ignore the first 32bits
  // assign cdc_read_data_valid = dst_valid_q & dst_valid_o;


  // // When data is valid, in the next cycle the timing fsm will controls the data de-multiplexing
  assign cdc_dst_valid = dst_valid_o;

  // always_ff @(posedge clk_0_i or negedge rst_ni) begin
  //   if(~rst_ni) begin
  //     dst_valid_q <= '0;
  //   end else begin
  //     dst_valid_q <= dst_valid_d;
  //   end
  // end



  logic [DRAM_WORD_WIDTH-1 : 0] rd_data_q, rd_data_d;

  //A de-mux used to pack the data slices recived in 8 DQS cycles into a 256 bit WORD
  always_comb begin
    rd_data_d = rd_data_q;
    // Fetch data from the clock-domain-crossing FIFO only when it is not empty
    if (dst_valid_o == 1'b1) begin
      case (data_sel_rd)
        3'd7: rd_data_d[31 : 0] = dst_data_o;
        3'd6: rd_data_d[63 : 32] = dst_data_o;
        3'd5: rd_data_d[95 : 64] = dst_data_o;
        3'd4: rd_data_d[127:96] = dst_data_o;
        3'd3: rd_data_d[159:128] = dst_data_o;
        3'd2: rd_data_d[191:160] = dst_data_o;
        3'd1: rd_data_d[223:192] = dst_data_o;
        3'd0: rd_data_d[255:224] = dst_data_o;
      endcase
    end
  end

  always_ff @(posedge clk_0_i or negedge rst_ni) begin
    if (~rst_ni) begin
      rd_data_q <= '0;
    end else begin
      rd_data_q <= rd_data_d;
    end
  end



  always_ff @(posedge clk_0_i or negedge rst_ni) begin
    if (~rst_ni) begin
      data_valid_q <= '0;
      data_last_q  <= '0;
    end else begin
      data_valid_q <= data_valid_d;
      data_last_q  <= data_last_d;
    end
  end


  assign data_o       = rd_data_q;
  assign data_valid_o = data_valid_q;
  assign data_last_o  = data_last_q;

  // =========================
  //    Assertions
  // =========================

`ifndef SYNTHESIS
  default disable iff (~rst_ni); display_type_sel :
  assert property (@(posedge clk_0_i) $stable(type_sel))
  else begin
    $display("-------------------------------------");
    $display("PHY Module Report");
    $display("[%0tps] : PHY datapath input is", $time);
    $display("00 - CMD:		%h", cmd_i);
    $display("01 - DATA:	%h", data_i_pipe_reg_q);
    $display("10 - MASK:	%h", mask_i);
    $display("Now db is sending %d", type_sel);
    $display("-------------------------------------");
  end

`endif


endmodule
