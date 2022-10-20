// Copyright 2022 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Suyang Song <susong@student.ethz.ch>
// Bowen Wang <bowwang@student.ethz.ch>
// Chen Wang <chewang@student.ethz.ch>
// Jiawei Zhang <jiawzhang@student.ethz.ch>

`include "axi/assign.svh"
`include "axi/typedef.svh"

// rpc top module synethsis wrapper
module rpc_synth_wrap #(
  parameter int unsigned AxiIdWidth    = 6,
  parameter int unsigned AxiAddrWidth  = 48,
  parameter int unsigned AxiDataWidth  = 64,
  parameter int unsigned AxiUserWidth  = 1,
  // master ports
  parameter int unsigned DramDataWidth = 256,
  parameter int unsigned DramLenWidth  = 6,
  parameter int unsigned DramAddrWidth = 20,
  parameter int unsigned BufferDepth   = 4,
  parameter int unsigned DramWordWidth = 256,


  // reg bus configuration
  parameter  int unsigned PHY_CLOCK_PERIOD = 5,
  parameter  int unsigned REG_ADDR_WIDTH   = 48,
  parameter  int unsigned REG_DATA_WIDTH   = 32,
  localparam int unsigned REG_STROBE_WIDTH = REG_DATA_WIDTH / 8,

  // type dependency
  parameter type axi_addr_t  = logic [  AxiAddrWidth-1:0],
  parameter type axi_data_t  = logic [  AxiDataWidth-1:0],
  parameter type axi_id_t    = logic [  AxiIdWidth  -1:0],
  parameter type axi_strb_t  = logic [AxiDataWidth/8-1:0],
  parameter type axi_user_t  = logic [  AxiUserWidth-1:0],
  parameter type dram_blen_t = logic [               5:0],
  parameter type dram_addr_t = logic [              19:0],
  parameter type phy_data_t  = logic [ DramWordWidth-1:0],
  parameter type cmd_addr_t  = logic [ DramAddrWidth-1:0],
  parameter type mask_t      = logic [              63:0]

) (

  // common signals
  input  logic            clk_i,
  input  logic            rst_ni,

  // axi slave port
  input  axi_id_t                     axi_aw_id_i,
  input  axi_addr_t                   axi_aw_addr_i,
  input  axi_pkg::len_t               axi_aw_len_i,
  input  axi_pkg::size_t              axi_aw_size_i,
  input  axi_pkg::burst_t             axi_aw_burst_i,
  input  logic                        axi_aw_lock_i,
  input  axi_pkg::cache_t             axi_aw_cache_i,
  input  axi_pkg::prot_t              axi_aw_prot_i,
  input  axi_pkg::qos_t               axi_aw_qos_i,
  input  axi_pkg::region_t            axi_aw_region_i,
  input  axi_pkg::atop_t              axi_aw_atop_i,
  input  axi_user_t                   axi_aw_user_i,
  input  logic                        axi_aw_valid_i,
  output logic                        axi_aw_ready_o,

  input  axi_data_t                   axi_w_data_i,
  input  axi_strb_t                   axi_w_strb_i,
  input  logic                        axi_w_last_i,
  input  axi_user_t                   axi_w_user_i,
  input  logic                        axi_w_valid_i,
  output logic                        axi_w_ready_o,

  output axi_id_t                     axi_b_id_o,
  output axi_pkg::resp_t              axi_b_resp_o,
  output axi_user_t                   axi_b_user_o,
  output logic                        axi_b_valid_o,
  input  logic                        axi_b_ready_i,

  input  axi_id_t                     axi_ar_id_i,
  input  axi_addr_t                   axi_ar_addr_i,
  input  axi_pkg::len_t               axi_ar_len_i,
  input  axi_pkg::size_t              axi_ar_size_i,
  input  axi_pkg::burst_t             axi_ar_burst_i,
  input  logic                        axi_ar_lock_i,
  input  axi_pkg::cache_t             axi_ar_cache_i,
  input  axi_pkg::prot_t              axi_ar_prot_i,
  input  axi_pkg::qos_t               axi_ar_qos_i,
  input  axi_pkg::region_t            axi_ar_region_i,
  input  axi_user_t                   axi_ar_user_i,
  input  logic                        axi_ar_valid_i,
  output logic                        axi_ar_ready_o,

  output axi_id_t                     axi_r_id_o,
  output axi_data_t                   axi_r_data_o,
  output axi_pkg::resp_t              axi_r_resp_o,
  output logic                        axi_r_last_o,
  output axi_user_t                   axi_r_user_o,
  output logic                        axi_r_valid_o,
  input  logic                        axi_r_ready_i,


  //----------- Reg Bus Interface Port ----
  // Regbus Request Input
  input logic [REG_ADDR_WIDTH-1:0]      reg_addr_i,
  input logic                           reg_write_i,
  input logic [REG_DATA_WIDTH-1:0]      reg_wdata_i,
  input logic [REG_STROBE_WIDTH-1:0]    reg_wstrb_i,
  input logic                           reg_valid_i,

  // Regbus Request Output
  output logic                          reg_error_o,
  output logic [REG_DATA_WIDTH-1:0]     reg_rdata_o,
  output logic                          reg_ready_o,


  // Controller to RPC DRAM Port
  output logic                          rpc_clk_o,
  output logic                          rpc_clk_no,
  output logic                          rpc_cs_no,
  output logic                          rpc_stb_o,

  output logic                          phy_dqs_o,
  output logic                          phy_dqs_n_o,

  input  logic                          phy_dqs_i,
  input  logic                          phy_dqs_n_i,

  output  logic                         phy_dqs_pair_oe_o,
  output  logic                         phy_dqs_pair_ie_o,
  output  logic                         phy_dqs_pair_pd_en_o,
  //----------------DB Strobe Interface--------------------
  output  logic [16-1 : 0]              phy_db_o,
  input   logic [16-1 : 0]              phy_db_i,
  output  logic                         phy_db_oe_o,
  output  logic                         phy_db_ie_o,
  output  logic                         phy_db_pd_en_o
);


  // axi port
  `AXI_TYPEDEF_AW_CHAN_T(axi_aw_t, axi_addr_t, axi_id_t, axi_user_t)
  `AXI_TYPEDEF_W_CHAN_T(axi_w_t, axi_data_t, axi_strb_t, axi_user_t)
  `AXI_TYPEDEF_B_CHAN_T(axi_b_t, axi_id_t, axi_user_t)
  `AXI_TYPEDEF_AR_CHAN_T(axi_ar_t, axi_addr_t, axi_id_t, axi_user_t)
  `AXI_TYPEDEF_R_CHAN_T(axi_r_t, axi_data_t, axi_id_t, axi_user_t)
  `AXI_TYPEDEF_REQ_T(axi_req_t, axi_aw_t, axi_w_t, axi_ar_t)
  `AXI_TYPEDEF_RESP_T(axi_resp_t, axi_b_t, axi_r_t)

  axi_req_t axi_req;
  axi_resp_t axi_rsp;

  // mask pin
  mask_t write_mask;

  // signal assignment
  // axi slave port
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

  assign axi_req.w.data    = axi_w_data_i;
  assign axi_req.w.strb    = axi_w_strb_i;
  assign axi_req.w.last    = axi_w_last_i;
  assign axi_req.w.user    = axi_w_user_i;
  assign axi_req.w_valid   = axi_w_valid_i;
  assign axi_w_ready_o     = axi_rsp.w_ready;

  assign axi_b_id_o        = axi_rsp.b.id;
  assign axi_b_resp_o      = axi_rsp.b.resp;
  assign axi_b_user_o      = axi_rsp.b.user;
  assign axi_b_valid_o     = axi_rsp.b_valid;
  assign axi_req.b_ready   = axi_b_ready_i;

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

  assign axi_r_id_o        = axi_rsp.r.id;
  assign axi_r_data_o      = axi_rsp.r.data;
  assign axi_r_resp_o      = axi_rsp.r.resp;
  assign axi_r_last_o      = axi_rsp.r.last;
  assign axi_r_user_o      = axi_rsp.r.user;
  assign axi_r_valid_o     = axi_rsp.r_valid;
  assign axi_req.r_ready   = axi_r_ready_i;



  // define the reg bus interface structure

  typedef logic [REG_ADDR_WIDTH-1:0] reg_addr_t;
  typedef logic [REG_DATA_WIDTH-1:0] reg_data_t;
  typedef logic [REG_STROBE_WIDTH-1:0] reg_strb_t;

  typedef struct packed {
    reg_addr_t addr;
    logic      write;
    reg_data_t wdata;
    reg_strb_t wstrb;
    logic      valid;
  } reg_req_t;


  typedef struct packed {
    reg_data_t rdata;
    logic      ready;
    logic      error;
  } reg_rsp_t;


  reg_req_t reg_req;
  reg_rsp_t reg_rsp;


  assign reg_req = reg_req_t'{
      addr: reg_addr_i,
      write: reg_write_i,
      wdata: reg_wdata_i,
      wstrb: reg_wstrb_i,
      valid: reg_valid_i
    };


  assign reg_rdata_o = reg_rsp.rdata;
  assign reg_ready_o = reg_rsp.ready;
  assign reg_error_o = reg_rsp.error;


  rpc #(
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

    .reg_req_t(reg_req_t),
    .reg_rsp_t(reg_rsp_t)

  ) i_rpc (
    // clk and rst signal
    .clk_i (clk_i),
    .rst_ni(rst_ni),

    // Axi Interface
    .axi_req_i(axi_req),
    .axi_rsp_o(axi_rsp),

    // Reg Bus Interface
    .reg_req_i(reg_req),
    .reg_rsp_o(reg_rsp),


    // Etron RPC Dram Interface
    .rpc_clk_o  (rpc_clk_o),
    .rpc_clk_no (rpc_clk_no),
    .rpc_cs_no  (rpc_cs_no),
    .rpc_stb_o  (rpc_stb_o),
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
    .phy_db_pd_en_o(phy_db_pd_en_o)
  );


endmodule
