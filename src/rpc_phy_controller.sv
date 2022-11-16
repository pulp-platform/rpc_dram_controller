// Copyright 2022 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Chen Wang <chewang@student.ethz.ch>
// Jiawei Zhang <jiawzhang@student.ethz.ch>

module rpc_phy_controller #(

  // Clock period of PHY
  parameter int CLOCK_PERIOD = 5,

  // rr arbiter input number
  parameter ARB_IN_NUM = 4,
  // rr arbiter output command width
  parameter DRAM_CMD_WIDTH = 32,

  // RPC DRAM DB Bus Width
  parameter DRAM_DB_WIDTH   = 16,

  // axi interface data path
  parameter type axi_cmd_req_t = logic,
  parameter type axi_cmd_rsp_t = logic,

  // axi interface w/r cmd path
  parameter type phy_req_t = logic,
  parameter type phy_rsp_t = logic

) (


  // ----------------------------------------------------------------------------------------------
  // ----------------------------Upstream Interface  ----------------------------------------------
  // ----------------------------------------------------------------------------------------------

  input  logic                                          clk_i,
  input  logic                                          clk90_i,
  input  logic                                          rst_ni,

  // ----------------------------------------------------------------------------------------------
  // ----------------------------Upstream Interface  ----------------------------------------------
  // ----------------------------------------------------------------------------------------------

  // Command Interface with upstream timer_management

  // Initialization Command Interface
  input  logic                                          launch_init,
  input  rpc_config_path_pkg::dram_init_cfg_reg_t       dram_init_config_i,


  // Direct Command Interface
  input   logic                                         direct_cmd_valid_i,
  input   logic[19-1:0]                                 direct_cmd_i,
  output  logic                                         direct_cmd_ready_o,

  // Refresh Timer Interface
  input   logic                                         ref_valid_i,
  input   logic[19-1:0]                                 ref_cmd_i,
  output  logic                                         ref_ready_o,

  // ZQC Timer Interface
  input   logic                                         zqc_valid_i,
  input   logic[19-1:0]                                 zqc_cmd_i,
  output  logic                                         zqc_ready_o,

  //Add init finish flag signal to timer_init_gen
  output  logic                                         rpc_init_completed_o,

  // Interface signals cmd_fsm with datapath interface
  input   axi_cmd_req_t                                 axi_cmd_req_i,
  output  axi_cmd_rsp_t                                 axi_cmd_rsp_o,

  // Interface signals phy with datapath interface
  input   phy_req_t                                     axi_data_req_i,
  input   logic[63:0]                                   write_mask_i,
  output  phy_rsp_t                                     axi_data_rsp_o,

  // Phy timing fsm configuration signal
  input rpc_config_path_pkg::timing_cfg_reg_t           phy_timing_cfg_i,

  // ----------------------------------------------------------------------------------------------
  // ----------------------------RPC DRAM Interface  ----------------------------------------------
  // ----------------------------------------------------------------------------------------------

  // Differential CLK
  output logic                                          rpc_clk_o,
  output logic                                          rpc_clk_no,

  // Chip Select
  output logic                                          rpc_cs_no,

  //Serial Command Output
  output logic                                          rpc_stb_o,

  //Output DQS for RPC DRAM WRITE Operation
  output logic                                          phy_dqs_o,
  output logic                                          phy_dqs_n_o,

  //Input DQS for RPC DRAM READ Operation
  input  logic                                          phy_dqs_i,
  input  logic                                          phy_dqs_n_i,

  //Bi-directional Tri-state Buffer Enable Signal
  output logic                                          phy_dqs_pair_oe_o,
  output logic                                          phy_dqs_pair_ie_o,
  output logic                                          phy_dqs_pair_pd_en_o,

  //----------------DB Strobe Interface--------------------
  output logic [DRAM_DB_WIDTH-1 : 0]                    phy_db_o,
  input  logic [DRAM_DB_WIDTH-1 : 0]                    phy_db_i,
  output logic                                          phy_db_oe_o,
  output logic                                          phy_db_ie_o,
  output logic                                          phy_db_pd_en_o,

  input  logic                                          phy_dqs_delay_i
);




  //////////////////////////////////////////////////////////////////////////////////////
  ////////////////////////////Command Arbiter Implementation////////////////////////////
  //////////////////////////////////////////////////////////////////////////////////////

  // Arbiter to phy signal
  logic arb_o_phy_i_valid;
  logic arb_i_phy_o_ready;
  logic [DRAM_CMD_WIDTH-1:0] arb_o_phy_i_cmd;  // Arbiter winnner command given to PHY


  rpc_cmd_fsm #(
    //parameter
    .DRAM_CMD_WIDTH(DRAM_CMD_WIDTH),
    .ARB_IN_NUM    (ARB_IN_NUM),
    .ARB_DATA_WIDTH(27)
  ) i_rpc_cmd_fsm (
    .clk_i (clk_i),
    .rst_ni(rst_ni),


    // ----------------------- Upstream -> Arbiter module interface ------------------

    // Signals interface with data_path R/W command port
    .data_path_valid_i   (axi_cmd_req_i.cmd_valid),
    .data_path_addr_i    (axi_cmd_req_i.addr),
    .data_path_len_i     (axi_cmd_req_i.len),
    .data_path_is_write_i(axi_cmd_req_i.is_write),
    .data_path_ready_o   (axi_cmd_rsp_o.cmd_ready),

    // SoC Direct Command interface
    .direct_cmd_valid_i(direct_cmd_valid_i),
    .direct_cmd_i      (direct_cmd_i),
    .direct_cmd_ready_o(direct_cmd_ready_o),


    // Initialization Command Interface
    .launch_init_i     (launch_init),
    .dram_init_config_i(dram_init_config_i),

    //Add init finish flag signal to timer_init_gen
    .rpc_init_completed_o(rpc_init_completed_o),


    // Ref Command Interface
    .ref_valid_i(ref_valid_i),
    .ref_cmd_i  (ref_cmd_i),
    .ref_ready_o(ref_ready_o),

    // ZQC Command Interface
    .zqc_valid_i(zqc_valid_i),
    .zqc_cmd_i  (zqc_cmd_i),
    .zqc_ready_o(zqc_ready_o),


    // -----------------------Arbiter -> PHY interface ------------------
    //Signals interface with phy
    .phy_ready_i(arb_i_phy_o_ready),
    .phy_valid_o(arb_o_phy_i_valid),
    .phy_cmd_o  (arb_o_phy_i_cmd)
  );

  //////////////////////////////////////////////////////////////////////////////////////
  ////////////////////////////PHY Module Implementation/////////////////////////////////
  //////////////////////////////////////////////////////////////////////////////////////


  // Bidirectional Tri-state Buffer
  // The out_ena_i signal controls the input/output mode of the buffer:
  //    1: input signal output_i will be buffered to the wire signal line_io
  //       output signal in_o will have undefined value
  //    0: input signal output_i will not affect line_io, line_io is driven by external driver
  //       output signal in_o will follow line_io value


  rpc_phy #(
    //parameter
    .CLOCK_PERIOD   (CLOCK_PERIOD),
    .DRAM_CMD_WIDTH (DRAM_CMD_WIDTH),
    .DRAM_DB_WIDTH  (DRAM_DB_WIDTH),
    .DRAM_WORD_WIDTH(256),
    .DRAM_MASK_WIDTH(64)
  ) i_rpc_phy (
    //---------------------------Sytem Input Clock and reset --------------------------
    .clk_0_i(clk_i),  
    .clk_90_i(clk90_i),
    .rst_ni (rst_ni),

    .phy_timing_cfg_i(phy_timing_cfg_i),

    //----------------------------Upstream Data/Cmd <-> PHY --------------------------

    //---------------CMD Path------------------------------

    .cmd_i      (arb_o_phy_i_cmd),
    .cmd_valid_i(arb_o_phy_i_valid),
    .cmd_ready_o(arb_i_phy_o_ready),

    //---------------Data Path------------------------------

    // Write Mode Input Path
    .data_i      (axi_data_req_i.w_data),       //Only use w_data, without using w_valid and r_ready
    .mask_i      (write_mask_i),
    .data_ready_o(axi_data_rsp_o.w_data_ready),

    // Read Mode Output Path
    .data_valid_o(axi_data_rsp_o.r_data_valid),
    .data_last_o (axi_data_rsp_o.r_data_last),
    .data_o      (axi_data_rsp_o.r_data),


    //----------------------------PHY to downstream DRAM Interface--------------------

    .clk_o (rpc_clk_o),
    .clk_no(rpc_clk_no),
    .cs_no (rpc_cs_no),

    // Serial command output port
    .stb_o(rpc_stb_o),

    //-----------------DQS Strobe Interface------------------
    //Output DQS for RPC DRAM WRITE Operation
    .dqs_o (phy_dqs_o),
    .dqs_no(phy_dqs_n_o),

    //Input DQS for RPC DRAM READ Operation
    .dqs_i (phy_dqs_i),
    .dqs_ni(phy_dqs_n_i),

    //Bi-directional Tri-state Buffer Enable Signal
    .dqs_pair_oe_o   (phy_dqs_pair_oe_o),
    .dqs_pair_ie_o   (phy_dqs_pair_ie_o),
    .dqs_pair_pd_en_o(phy_dqs_pair_pd_en_o),

    //----------------DB Strobe Interface--------------------
    .db_o      (phy_db_o),
    .db_i      (phy_db_i),
    .db_oe_o   (phy_db_oe_o),
    .db_ie_o   (phy_db_ie_o),
    .db_pd_en_o(phy_db_pd_en_o),

    .phy_dqs_delay_i
  );


endmodule
