// Copyright 2022 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// rpc technology-dependent wrapper

// For both DC synthesis and FPGA implementation according to `FPGA_EMUL macro

`include "axi/typedef.svh"
`include "axi/assign.svh"
`include "register_interface/typedef.svh"

module rpc_wrapper (
  // clock and reset
`ifdef FPGA_EMUL
  input  logic            clkp_i,
  input  logic            clkn_i,
`else
  input  logic            clk_i,
`endif

  input  logic            rst_ni,

  // axi slave interface
  input  [ 5:0]           axi_aw_id_i,
  input  [ 39:0]          axi_aw_addr_i,
  input  [ 7:0]           axi_aw_len_i,
  input  [ 2:0]           axi_aw_size_i,
  input  [ 1:0]           axi_aw_burst_i,
  input                   axi_aw_lock_i,
  input  [ 3:0]           axi_aw_cache_i,
  input  [ 2:0]           axi_aw_prot_i,
  input  [ 3:0]           axi_aw_qos_i,
  input  [ 3:0]           axi_aw_region_i,
  input  [ 5:0]           axi_aw_atop_i,
  input                   axi_aw_user_i,
  input                   axi_aw_valid_i,
  output                  axi_aw_ready_o,
  input  [ 63:0]          axi_w_data_i,
  input  [ 7:0]           axi_w_strb_i,
  input                   axi_w_last_i,
  input                   axi_w_user_i,
  input                   axi_w_valid_i,
  output                  axi_w_ready_o,
  output [ 5:0]           axi_b_id_o,
  output [ 1:0]           axi_b_resp_o,
  output                  axi_b_user_o,
  output                  axi_b_valid_o,
  input                   axi_b_ready_i,
  input  [ 5:0]           axi_ar_id_i,
  input  [ 39:0]          axi_ar_addr_i,
  input  [ 7:0]           axi_ar_len_i,
  input  [ 2:0]           axi_ar_size_i,
  input  [ 1:0]           axi_ar_burst_i,
  input                   axi_ar_lock_i,
  input  [ 3:0]           axi_ar_cache_i,
  input  [ 2:0]           axi_ar_prot_i,
  input  [ 3:0]           axi_ar_qos_i,
  input  [ 3:0]           axi_ar_region_i,
  input  [ 0:0]           axi_ar_user_i,
  input                   axi_ar_valid_i,
  output                  axi_ar_ready_o,
  output [ 5:0]           axi_r_id_o,
  output [ 63:0]          axi_r_data_o,
  output [ 1:0]           axi_r_resp_o,
  output                  axi_r_user_o,
  output                  axi_r_last_o,
  output                  axi_r_valid_o,
  input                   axi_r_ready_i,

  // Regbus Request Input
  input wire [47:0]      reg_addr_i,
  input wire             reg_write_i,
  input wire [31:0]      reg_wdata_i,
  input wire [3:0]       reg_wstrb_i,
  input wire             reg_valid_i,

  // Regbus Request Output
  output wire            reg_error_o,
  output wire [31:0]     reg_rdata_o,
  output wire            reg_ready_o,

  // Controller to RPC DRAM Port
  inout  wire rpc_clk,
  inout  wire rpc_clkn,
  inout  wire rpc_csn,
  inout  wire rpc_stb,

  inout  wire rpc_dqs,
  inout  wire rpc_dqsn,
  inout  wire rpc_db0,
  inout  wire rpc_db1,
  inout  wire rpc_db2,
  inout  wire rpc_db3,
  inout  wire rpc_db4,
  inout  wire rpc_db5,
  inout  wire rpc_db6,
  inout  wire rpc_db7,
  inout  wire rpc_db8,
  inout  wire rpc_db9,
  inout  wire rpc_dba,
  inout  wire rpc_dbb,
  inout  wire rpc_dbc,
  inout  wire rpc_dbd,
  inout  wire rpc_dbe,
  inout  wire rpc_dbf
);

  logic rpc_clk_in;
  logic [rpc_config_path_pkg::DELAY_CFG_WIDTH-1:0] phy_clk_90_delay_cfg, phy_dqs_delay_cfg;

  // clock generation

`ifdef FPGA_EMUL
  // differential to single ended clock conversion
  IBUFGDS #(
    .IOSTANDARD  ("LVDS"),
    .DIFF_TERM   ("FALSE"),
    .IBUF_LOW_PWR("FALSE")
  ) i_sysclk_iobuf (
    .I (clkp_i),
    .IB(clkn_i),
    .O (rpc_clk0_in)
  );

  // clock90 generation
  xilinx_phase_shift_90 i_delay_line_clk_90 (
    .reset   (~rst_ni),
    .clk_in1 (rpc_clk0_in),
    .clk_out1(rpc_clk90_in),
    .locked  ()
  );
`else // !`ifdef FPGA_EMUL
  assign rpc_clk0_in = clk_i;

  // clk90 generation
  generic_delay_D5_O1_5P000_CG0 i_delay_line_clk_90 (
    .clk_i   (rpc_clk0_in),
    .enable_i(1'b1),
    .delay_i (phy_clk_90_delay_cfg),
    .clk_o   (rpc_clk90_in)
  );
`endif


  // DQS delay generation

  // The delay_line cell delays the input clk based on a configurable delay cfg_delay
  // If cfg_delay = 5'd31, the clk_o will be a 5ns delayed version of clk_i
  // The delay is used to shift DQS input by 90 degree so that it sits at the center of data window

  // rpc iobuf
  logic out_dqs, out_dqsn, in_dqs, in_dqsn, oe_dqs, ie_dqs, oe_db, pd_en_dqs, pd_en_db, dqs_delay;
  logic [15:0] out_db, in_db;

`ifndef FPGA_EMUL
  generic_delay_D5_O1_5P000_CG0 i_delay_line_dqs_i (
    .clk_i   (in_dqs),
    .enable_i(1'b1),
    .delay_i (phy_dqs_delay_cfg),
    .clk_o   (dqs_delay)
  );
`else  // !`ifndef FPGA_MAP
  xilinx_phase_shift_90 i_delay_line_dqs (
    .reset   (~rst_ni),
    .clk_in1 (in_dqs),
    .clk_out1(dqs_delay),
    .locked  ()
  );

  //assign dqs_ni_delay = in_dqsn;
`endif

  rpc_iobuf i_iobuf_rpc (
    // output enable
    .oe_dqs_i (oe_dqs),
    .oe_db_i  (oe_db),

    // output enable
    .ie_dqs_i (ie_dqs),
    .ie_db_i  (ie_db),

    // input from tri-state pad
    .in_dqs_o (in_dqs),
    .in_dqsn_o(in_dqsn),
    .in_db_o  (in_db),

    // output to tri-state pad
    .out_dqs_i (out_dqs),
    .out_dqsn_i(out_dqsn),
    .out_db_i  (out_db),

    .out_clk_i (out_clk),
    .out_clkn_i(out_clkn),
    .out_stb_i (out_stb),
    .out_csn_i (out_csn),

    .pd_en_dqs_i (pd_en_dqs),
    .pd_en_db_i  (pd_en_db),

    .clk (rpc_clk),
    .clkn(rpc_clkn),
    .stb (rpc_stb),
    .csn (rpc_csn),

    // tri-state signals
    .dqs (rpc_dqs),
    .dqsn(rpc_dqsn),
    .db0 (rpc_db0),
    .db1 (rpc_db1),
    .db2 (rpc_db2),
    .db3 (rpc_db3),
    .db4 (rpc_db4),
    .db5 (rpc_db5),
    .db6 (rpc_db6),
    .db7 (rpc_db7),
    .db8 (rpc_db8),
    .db9 (rpc_db9),
    .dba (rpc_dba),
    .dbb (rpc_dbb),
    .dbc (rpc_dbc),
    .dbd (rpc_dbd),
    .dbe (rpc_dbe),
    .dbf (rpc_dbf)
  );

  // parameterize rpc controller and instantiate it

  // rpc dram parameters
  localparam int unsigned DramDataWidth = 256;
  localparam int unsigned DramLenWidth = 6;
  localparam int unsigned DramAddrWidth = 20;
  localparam int unsigned BufferDepth = 4;
  // mask pin
  typedef  logic [              63:0] mask_t;
  mask_t write_mask;

  // axi parameters
  localparam int unsigned AxiIdWidth = 6;
  localparam int unsigned AxiAddrWidth = 48;
  localparam int unsigned AxiDataWidth = 64;
  localparam int unsigned AxiUserWidth = 1;
  typedef  logic [  AxiAddrWidth-1:0] axi_addr_t  ;
  typedef  logic [  AxiDataWidth-1:0] axi_data_t  ;
  typedef  logic [  AxiIdWidth  -1:0] axi_id_t    ;
  typedef  logic [AxiDataWidth/8-1:0] axi_strb_t  ;
  typedef  logic [  AxiUserWidth-1:0] axi_user_t  ;
  `AXI_TYPEDEF_ALL(axi, axi_addr_t, axi_id_t, axi_data_t, axi_strb_t, axi_user_t)
  axi_req_t axi_req;
  axi_resp_t axi_rsp;

  // reg bus configuration
  localparam  int unsigned PHY_CLOCK_PERIOD = 5;
  localparam  int unsigned REG_ADDR_WIDTH   = 48;
  localparam  int unsigned REG_DATA_WIDTH   = 32;
  localparam  int unsigned REG_STROBE_WIDTH = REG_DATA_WIDTH / 8;
  typedef logic [REG_ADDR_WIDTH-1:0] reg_addr_t;
  typedef logic [REG_DATA_WIDTH-1:0] reg_data_t;
  typedef logic [REG_STROBE_WIDTH-1:0] reg_strb_t;
  `REG_BUS_TYPEDEF_ALL(register, reg_addr_t, reg_data_t, reg_strb_t)
  register_req_t reg_req;
  register_rsp_t reg_rsp;

  rpc_top #(
    .PHY_CLOCK_PERIOD(5),

    .AxiDataWidth(AxiDataWidth),
    .AxiAddrWidth(AxiAddrWidth),
    .AxiIdWidth  (AxiIdWidth),
    .AxiUserWidth(AxiUserWidth),

    .DramDataWidth(DramDataWidth),
    .DramLenWidth (DramLenWidth),
    .DramAddrWidth(DramAddrWidth),
    .BufferDepth  (BufferDepth),

    .axi_req_t(axi_req_t),
    .axi_rsp_t(axi_resp_t),

    .reg_req_t(register_req_t),
    .reg_rsp_t(register_rsp_t)

  ) i_rpc_top (
    // clk and rst signal
    .clk_i  (rpc_clk0_in),
    .clk90_i(rpc_clk90_in),
    .rst_ni(rst_ni),

    // Axi Interface
    .axi_req_i(axi_req),
    .axi_rsp_o(axi_rsp),

    // Reg Bus Interface
    .reg_req_i(reg_req),
    .reg_rsp_o(reg_rsp),

    // Etron RPC Dram Interface
    .rpc_clk_o           (out_clk),
    .rpc_clk_no          (out_clkn),
    .rpc_cs_no           (out_csn),
    .rpc_stb_o           (out_stb),
    .phy_dqs_o           (out_dqs),
    .phy_dqs_n_o         (out_dqsn),
    .phy_dqs_i           (in_dqs),
    .phy_dqs_n_i         (in_dqsn),
    .phy_dqs_pair_oe_o   (oe_dqs),
    .phy_dqs_pair_ie_o   (ie_dqs),
    .phy_dqs_pair_pd_en_o(pd_en_dqs),
    .phy_db_o            (out_db),
    .phy_db_i            (in_db),
    .phy_db_oe_o         (oe_db),
    .phy_db_ie_o         (ie_db),
    .phy_db_pd_en_o      (pd_en_db),

    .phy_clk_90_delay_cfg_o (phy_clk_90_delay_cfg),
    .phy_dqs_delay_cfg_o    (phy_dqs_delay_cfg),

    .phy_dqs_delay_i        (dqs_delay)

  );

  // pack/explode AXI req/resp signals
  // AW
  assign axi_req.aw.id     = axi_aw_id_i;
  assign axi_req.aw.addr   = axi_aw_addr_i;
  assign axi_req.aw.len    = axi_aw_len_i;
  assign axi_req.aw.size   = axi_aw_size_i;
  assign axi_req.aw.burst  = axi_aw_burst_i;
  assign axi_req.aw.lock   = axi_aw_lock_i;
  assign axi_req.aw.cache  = axi_aw_cache_i;
  assign axi_req.aw.prot   = axi_aw_prot_i;
  assign axi_req.aw.qos    = axi_aw_qos_i;
  assign axi_req.aw.region = axi_aw_region_i;
  assign axi_req.aw.atop   = axi_aw_atop_i;
  assign axi_req.aw.user   = axi_aw_user_i;
  assign axi_req.aw_valid  = axi_aw_valid_i;
  assign axi_aw_ready_o    = axi_rsp.aw_ready;
  // W
  assign axi_req.w.data    = axi_w_data_i;
  assign axi_req.w.strb    = axi_w_strb_i;
  assign axi_req.w.last    = axi_w_last_i;
  assign axi_req.w.user    = axi_w_user_i;
  assign axi_req.w_valid   = axi_w_valid_i;
  assign axi_w_ready_o     = axi_rsp.w_ready;
  // B
  assign axi_b_id_o        = axi_rsp.b.id;
  assign axi_b_resp_o      = axi_rsp.b.resp;
  assign axi_b_user_o      = axi_rsp.b.user;
  assign axi_b_valid_o     = axi_rsp.b_valid;
  assign axi_req.b_ready   = axi_b_ready_i;
  // AR
  assign axi_req.ar.id     = axi_ar_id_i;
  assign axi_req.ar.addr   = axi_ar_addr_i;
  assign axi_req.ar.len    = axi_ar_len_i;
  assign axi_req.ar.size   = axi_ar_size_i;
  assign axi_req.ar.burst  = axi_ar_burst_i;
  assign axi_req.ar.lock   = axi_ar_lock_i;
  assign axi_req.ar.cache  = axi_ar_cache_i;
  assign axi_req.ar.prot   = axi_ar_prot_i;
  assign axi_req.ar.qos    = axi_ar_qos_i;
  assign axi_req.ar.region = axi_ar_region_i;
  assign axi_req.ar.user   = axi_ar_user_i;
  assign axi_req.ar_valid  = axi_ar_valid_i;
  assign axi_ar_ready_o    = axi_rsp.ar_ready;
  // R
  assign axi_r_id_o        = axi_rsp.r.id;
  assign axi_r_data_o      = axi_rsp.r.data;
  assign axi_r_resp_o      = axi_rsp.r.resp;
  assign axi_r_last_o      = axi_rsp.r.last;
  assign axi_r_user_o      = axi_rsp.r.user;
  assign axi_r_valid_o     = axi_rsp.r_valid;
  assign axi_req.r_ready = axi_r_ready_i;

  // pack/explode register req/resp signals
  // req
  assign reg_req = register_req_t'{
     addr: reg_addr_i,
     write: reg_write_i,
     wdata: reg_wdata_i,
     wstrb: reg_wstrb_i,
     valid: reg_valid_i
  };
  // resp
  assign reg_rdata_o = reg_rsp.rdata;
  assign reg_ready_o = reg_rsp.ready;
  assign reg_error_o = reg_rsp.error;

endmodule
