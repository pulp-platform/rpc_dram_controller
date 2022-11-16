// Copyright 2022 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Chen Wang <chewang@student.ethz.ch>
// Jiawei Zhang <jiawzhang@student.ethz.ch>

// The top module of RPC DRAM controller which controls cmd flow from SoC upstream to Etron RPC Dram
// This module is comprised of:
//    1: rpc_config_manager
//    2: rpc_dram_controller

// Note: The Neo Soc uses byte address
//
module rpc_controller #(

  parameter int PHY_CLOCK_PERIOD = 5,

  parameter type reg_req_t = logic,
  parameter type reg_rsp_t = logic,

  parameter type phy_req_t = logic,
  parameter type phy_rsp_t = logic,

  parameter type axi_cmd_req_t = logic,
  parameter type axi_cmd_rsp_t = logic

) (

  // ----------------------------------------------------------------------------------------------
  // ----------------------------clock and reset input  -------------------------------------------
  // ----------------------------------------------------------------------------------------------

  input logic clk_i,
  input logic clk90_i,
  input logic rst_ni,

  // ----------------------------------------------------------------------------------------------
  // ----------------------------upstream interface  ----------------------------------------------
  // ----------------------------------------------------------------------------------------------
  //----------- Reg Bus Interface Port ----
  // Regbus Request Input
  input  reg_req_t                  reg_req_i,
  output reg_rsp_t                  reg_rsp_o,

  // axi cmd response port
  input  axi_cmd_req_t              axi_cmd_req_i,
  output axi_cmd_rsp_t              axi_cmd_rsp_o,

  // data path port
  input   phy_req_t                 phy_req_i,
  output  phy_rsp_t                 phy_rsp_o,
  input   logic [63:0]              write_mask_i,

  // ----------------------------------------------------------------------------------------------
  // ----------------------------module -> RPC DRAM  ----------------------------------------------
  // ----------------------------------------------------------------------------------------------

  // Controller to RPC DRAM Port
  input logic                       clk_90_i,
  output logic                      rpc_clk_o,
  output logic                      rpc_clk_no,
  output logic                      rpc_cs_no,
  output logic                      rpc_stb_o,

  // inout wire                         rpc_dqs_pad,
  // inout wire                         rpc_dqs_n_pad,
  // inout wire [16-1:0]              rpc_db_pad

  //Output DQS for RPC DRAM WRITE Operation
  output logic                      phy_dqs_o,
  output logic                      phy_dqs_n_o,

  //Input DQS for RPC DRAM READ Operation
  input  logic                      phy_dqs_i,
  input  logic                      phy_dqs_n_i,

  //Bi-directional Tri-state Buffer Enable Signal
  output logic                      phy_dqs_pair_oe_o,
  output logic                      phy_dqs_pair_ie_o,
  output logic                      phy_dqs_pair_pd_en_o,

  //----------------DB Strobe Interface--------------------
  output logic [16-1 : 0]           phy_db_o,
  input  logic [16-1 : 0]           phy_db_i,
  output logic                      phy_db_oe_o,
  output logic                      phy_db_ie_o,
  output logic                      phy_db_pd_en_o,

  output logic [rpc_config_path_pkg::DELAY_CFG_WIDTH-1:0] phy_clk_90_delay_cfg_o,
  output logic [rpc_config_path_pkg::DELAY_CFG_WIDTH-1:0] phy_dqs_delay_cfg_o,

  input  logic                      phy_dqs_delay_i
);

  //Initialization Interface
  logic mgnmt_i_ctrl_o_init_flag;
  logic mgnmt_o_ctrl_i_launch_init;
  rpc_config_path_pkg::dram_init_cfg_reg_t mgnmt_o_ctrl_i_init_config;


  // Direct Command Interface
  logic mgnmt_i_ctrl_o_direct_cmd_ready;
  logic mgnmt_o_ctrl_i_direct_cmd_valid;
  logic [19-1:0] mgnmt_o_ctrl_i_direct_cmd;

  // Ref Timer Interface
  logic mgnmt_i_ctrl_o_ref_ready;
  logic mgnmt_o_ctrl_i_ref_valid;
  logic [19-1:0] mgnmt_o_ctrl_i_ref_cmd;


  // ZQC Timer Interface
  logic mgnmt_i_ctrl_o_zqc_ready;
  logic mgnmt_o_ctrl_i_zqc_valid;
  logic [19-1:0] mgnmt_o_ctrl_i_zqc_cmd;


  // Phy Timing FSM Configuration
  rpc_config_path_pkg::timing_cfg_reg_t mgnmt_o_ctrl_i_timing_cfg;


  rpc_config_manager #(
    .REG_WIDTH      (rpc_config_path_pkg::REG_WIDTH),
    .ADDR_WIDTH     (rpc_config_path_pkg::ADDR_WIDTH),
    .CMD_FIFO_DEPTH (rpc_config_path_pkg::CMD_FIFO_DEPTH),
    .CNT_WIDTH      (rpc_config_path_pkg::CNT_WIDTH)
  ) i_rpc_config_manager (
    .clk_i (clk_i),
    .rst_ni(rst_ni),

    // Regbus Request Input
    .addr_i (reg_req_i.addr[rpc_config_path_pkg::ADDR_WIDTH-1:0]),
    .write_i(reg_req_i.write),
    .wdata_i(reg_req_i.wdata),
    .wstrb_i(reg_req_i.wstrb),
    .valid_i(reg_req_i.valid),

    // Regbus Request Output
    .error_o(reg_rsp_o.error),
    .rdata_o(reg_rsp_o.rdata),
    .ready_o(reg_rsp_o.ready),


    //Initialization
    .rpc_init_completed_i(mgnmt_i_ctrl_o_init_flag),
    .launch_dram_init_o  (mgnmt_o_ctrl_i_launch_init),
    .dram_init_config_o  (mgnmt_o_ctrl_i_init_config),


    //Direct Command
    .direct_cmd_ready_i(mgnmt_i_ctrl_o_direct_cmd_ready),
    .direct_cmd_valid_o(mgnmt_o_ctrl_i_direct_cmd_valid),
    .direct_cmd_o      (mgnmt_o_ctrl_i_direct_cmd),


    //REF Timer
    .ref_ready_i(mgnmt_i_ctrl_o_ref_ready),
    .ref_valid_o(mgnmt_o_ctrl_i_ref_valid),
    .ref_cmd_o  (mgnmt_o_ctrl_i_ref_cmd),


    //ZQC Timer
    .zqc_ready_i(mgnmt_i_ctrl_o_zqc_ready),
    .zqc_valid_o(mgnmt_o_ctrl_i_zqc_valid),
    .zqc_cmd_o  (mgnmt_o_ctrl_i_zqc_cmd),

    .phy_clk_90_delay_cfg_o,
    .phy_dqs_delay_cfg_o,

    .phy_timing_cfg_o(mgnmt_o_ctrl_i_timing_cfg)
  );


  rpc_phy_controller #(
    .CLOCK_PERIOD   (PHY_CLOCK_PERIOD),
    .ARB_IN_NUM     (4),
    .DRAM_CMD_WIDTH (32),
    .DRAM_DB_WIDTH  (16),
    .axi_cmd_req_t  (axi_cmd_req_t),
    .axi_cmd_rsp_t  (axi_cmd_rsp_t),
    .phy_req_t      (phy_req_t),
    .phy_rsp_t      (phy_rsp_t)

  ) i_rpc_phy_controller (
    .clk_i (clk_i),
    .clk90_i,
    .rst_ni(rst_ni),


    //Initialization
    .launch_init         (mgnmt_o_ctrl_i_launch_init),
    .dram_init_config_i  (mgnmt_o_ctrl_i_init_config),
    .rpc_init_completed_o(mgnmt_i_ctrl_o_init_flag),


    //Direct Command
    .direct_cmd_valid_i(mgnmt_o_ctrl_i_direct_cmd_valid),
    .direct_cmd_i      (mgnmt_o_ctrl_i_direct_cmd),
    .direct_cmd_ready_o(mgnmt_i_ctrl_o_direct_cmd_ready),

    //REF Timer
    .ref_valid_i(mgnmt_o_ctrl_i_ref_valid),
    .ref_cmd_i  (mgnmt_o_ctrl_i_ref_cmd),
    .ref_ready_o(mgnmt_i_ctrl_o_ref_ready),

    //ZQC Timer
    .zqc_valid_i(mgnmt_o_ctrl_i_zqc_valid),
    .zqc_cmd_i  (mgnmt_o_ctrl_i_zqc_cmd),
    .zqc_ready_o(mgnmt_i_ctrl_o_zqc_ready),


    // Timing FSM Configuration
    .phy_timing_cfg_i(mgnmt_o_ctrl_i_timing_cfg),

    // Data path to PHY

    .axi_cmd_req_i (axi_cmd_req_i),
    .axi_cmd_rsp_o (axi_cmd_rsp_o),
    .axi_data_req_i(phy_req_i),
    .axi_data_rsp_o(phy_rsp_o),
    .write_mask_i  (write_mask_i),

    // PHY to RPC DRAM
    //90 degree clock used to align RPC DRAM DQS and CLK
    .rpc_clk_o (rpc_clk_o),
    .rpc_clk_no(rpc_clk_no),
    .rpc_cs_no (rpc_cs_no),
    .rpc_stb_o (rpc_stb_o),

    .phy_dqs_o  (phy_dqs_o),
    .phy_dqs_n_o(phy_dqs_n_o),

    .phy_dqs_i  (phy_dqs_i),
    .phy_dqs_n_i(phy_dqs_n_i),

    .phy_dqs_pair_oe_o   (phy_dqs_pair_oe_o),
    .phy_dqs_pair_ie_o   (phy_dqs_pair_ie_o),
    .phy_dqs_pair_pd_en_o(phy_dqs_pair_pd_en_o),

    .phy_db_o      (phy_db_o),
    .phy_db_i      (phy_db_i),
    .phy_db_oe_o   (phy_db_oe_o),
    .phy_db_ie_o   (phy_db_ie_o),
    .phy_db_pd_en_o(phy_db_pd_en_o),
  
    .phy_dqs_delay_i  

  );

endmodule
