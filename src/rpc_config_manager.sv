// Copyright 2022 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Chen Wang <chewang@student.ethz.ch>
// Jiawei Zhang <jiawzhang@student.ethz.ch>

module rpc_config_manager #(
  // ---------- Reg Bus Communciation Interface --------------------------------
  parameter  int unsigned REG_WIDTH    = 32,
  parameter  int unsigned ADDR_WIDTH   = 5,
  localparam int unsigned STROBE_WIDTH = REG_WIDTH / 8,

  // ---------- Direct Command Register --------------------------------
  parameter int unsigned CMD_FIFO_DEPTH = 4,
  // Timer Internal Counter Width
  parameter int unsigned CNT_WIDTH      = 32,
  // Timer Output Command Width
  parameter int unsigned CMD_WIDTH      = 19,

  // DQS/DQS# Input Delay Line configuration port
  parameter int unsigned DELAY_CFG_WIDTH = 5

) (
  // CLK & RST
  input logic clk_i,
  input logic rst_ni,

  // ----------------------------------------------------------------------------------------------
  // ----------------------------Reg_Bus -> Config_reg interface ----------------------------------
  // ----------------------------------------------------------------------------------------------

  input logic   [ADDR_WIDTH-1:0]    addr_i,
  // write signal
  input logic                       write_i,
  input logic   [REG_WIDTH-1:0]     wdata_i,
  input logic   [STROBE_WIDTH-1:0]  wstrb_i,  // It is of no use to apply mask to the configuration register, so this one is currently omitted
  // read signal
  output logic                      error_o,
  output logic  [REG_WIDTH-1:0]     rdata_o,
  // handshaking
  input  logic                      valid_i,
  output logic                      ready_o,

  // ----------------------------------------------------------------------------------------------
  // ----------------------------Timers -> CMD_FSM ------------------------------------------------
  // ----------------------------------------------------------------------------------------------

  // if the CMD_FSM completes RPC DRAM Initilization, this signal will be pull high
  input  logic           rpc_init_completed_i,

  // config_ref initlization signal
  output logic                                           launch_dram_init_o,
  output rpc_config_path_pkg::dram_init_cfg_reg_t        dram_init_config_o,

  // direct command output config_reg -> CMD_FSM -> DRAM
  input  logic                      direct_cmd_ready_i,
  output logic                      direct_cmd_valid_o,
  output logic [CMD_WIDTH-1:0]      direct_cmd_o,

  // Ref Timer:
  input   logic                     ref_ready_i,          // Handshaking with down_stream arbiter
  output  logic                     ref_valid_o,          // Handshaking with down_stream arbiter
  output  logic [CMD_WIDTH-1:0]     ref_cmd_o,            // Handshaking with down_stream arbiter

  // Cal Timer:
  input   logic                     zqc_ready_i,          // Handshaking with down_stream arbiter
  output  logic                     zqc_valid_o,          // Handshaking with down_stream arbiter
  output  logic [CMD_WIDTH-1:0]     zqc_cmd_o,            // Handshaking with down_stream arbiter

  // ----------------------------------------------------------------------------------------------
  // ----------------------------config_reg -> PHY ------------------------------------------------
  // ----------------------------------------------------------------------------------------------
  output logic [DELAY_CFG_WIDTH-1:0]  phy_clk_90_delay_cfg_o,
  output logic [DELAY_CFG_WIDTH-1:0]  phy_dqs_i_delay_cfg_o,
  output logic [DELAY_CFG_WIDTH-1:0]  phy_dqs_ni_delay_cfg_o,

  output rpc_config_path_pkg::timing_cfg_reg_t          phy_timing_cfg_o

);


  // timer starter signal
  logic reg_o_starter_i_launch_config;
  rpc_config_path_pkg::timer_starter_cfg_reg_t reg_o_starter_i_config;

  // ref timer signal
  logic reg_o_ref_i_launch_config;
  rpc_config_path_pkg::ref_cfg_reg_t reg_o_ref_i_config;

  // zqc timer signal
  logic reg_o_zqc_i_launch_config;
  rpc_config_path_pkg::zqc_cfg_reg_t reg_o_zqc_i_config;

  // timer starter to other timer modules
  logic starter_o_timer_i_launch_init;



  config_reg #(
    .REG_WIDTH (REG_WIDTH),
    .ADDR_WIDTH(ADDR_WIDTH),

    .CMD_WIDTH     (CMD_WIDTH),
    .CMD_FIFO_DEPTH(CMD_FIFO_DEPTH),

    .DELAY_CFG_WIDTH(DELAY_CFG_WIDTH)

  ) i_config_reg (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .addr_i(addr_i),
    // write signal
    .write_i(write_i),
    .wdata_i(wdata_i),
    .wstrb_i                      (wstrb_i),  // It is of no use to apply mask to the configuration register; so this one is currently omitted
    // read signal
    .error_o(error_o),
    .rdata_o(rdata_o),
    // handshaking
    .valid_i(valid_i),
    .ready_o(ready_o),

    // config_reg -> downstream
    // config_ref initlization signal
    .launch_dram_init_o(launch_dram_init_o),
    .dram_init_config_o(dram_init_config_o),

    // direct command output config_reg -> CMD_FSM -> DRAM
    .direct_cmd_ready_i(direct_cmd_ready_i),
    .direct_cmd_valid_o(direct_cmd_valid_o),
    .direct_cmd_o      (direct_cmd_o),

    // config_reg -> starter_timer
    .launch_timer_starter_config_o(reg_o_starter_i_launch_config),
    .timer_starter_config_o       (reg_o_starter_i_config),

    // config_reg -> ref_timer
    .launch_ref_config_o(reg_o_ref_i_launch_config),
    .ref_config_o       (reg_o_ref_i_config),

    // config_reg -> zqc_timer
    .launch_zqc_config_o(reg_o_zqc_i_launch_config),
    .zqc_config_o       (reg_o_zqc_i_config),


    // config_reg -> phy
    .phy_clk_90_delay_cfg_o(phy_clk_90_delay_cfg_o),
    .phy_dqs_i_delay_cfg_o (phy_dqs_i_delay_cfg_o),
    .phy_dqs_ni_delay_cfg_o(phy_dqs_ni_delay_cfg_o),

    .phy_timing_cfg_o(phy_timing_cfg_o),

    // cmd_fsm -> phy
    .rpc_init_completed_i(rpc_init_completed_i)
  );



  timer_starter #(
    .CNT_WIDTH(CNT_WIDTH),
    .CMD_WIDTH(CMD_WIDTH)
  ) i_timer_starter (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    //init complete flag from cmd_fsm
    .rpc_init_completed_i(rpc_init_completed_i),
    //From config_reg
    .load_config_i       (reg_o_starter_i_launch_config),
    .config_i            (reg_o_starter_i_config),
    //To timers
    .init_timer_o        (starter_o_timer_i_launch_init)
  );


  ref_timer #(
    .CNT_WIDTH(CNT_WIDTH),
    .CMD_WIDTH(CMD_WIDTH)
  ) i_ref_timer (
    .clk_i        (clk_i),
    .rst_ni       (rst_ni),
    //From timer_init_gen
    .init_timer_i (starter_o_timer_i_launch_init),
    //From config_reg
    .load_config_i(reg_o_ref_i_launch_config),
    .config_i     (reg_o_ref_i_config),
    //To cmd_fsm
    .ref_ready_i  (ref_ready_i),
    .ref_valid_o  (ref_valid_o),
    .ref_cmd_o    (ref_cmd_o)
  );

  zqc_timer #(
    .CNT_WIDTH(CNT_WIDTH),
    .CMD_WIDTH(CMD_WIDTH)
  ) i_zqc_timer (
    .clk_i        (clk_i),
    .rst_ni       (rst_ni),
    //From timer_init_gen
    .init_timer_i (starter_o_timer_i_launch_init),
    //From config_reg
    .load_config_i(reg_o_zqc_i_launch_config),
    .config_i     (reg_o_zqc_i_config),
    //To cmd_fsm
    .zqc_ready_i  (zqc_ready_i),
    .zqc_valid_o  (zqc_valid_o),
    .zqc_cmd_o    (zqc_cmd_o)
  );





  // =========================
  //    Assertions
  // =========================


`ifndef SYNTHESIS

  initial
    assert (REG_WIDTH == 32)
    else begin
      $error("The Register Width must be 32!");
    end

  initial
    assert (ADDR_WIDTH == 3)
    else begin
      $error("The ADDR Width must be 3!");
    end

  initial
    assert (DELAY_CFG_WIDTH == 5)
    else begin
      $error("The DQS Delay Config Width must be 5!");
    end

  initial
    assert (CMD_WIDTH == 19)
    else begin
      $error("The CMD Width must be 19!");
    end

`endif

endmodule
