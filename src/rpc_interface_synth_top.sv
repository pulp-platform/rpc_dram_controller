// Copyright 2022 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Suyang Song <susong@student.ethz.ch>
// Bowen Wang <bowwang@student.ethz.ch>

`include "axi/assign.svh"
`include "axi/typedef.svh"

module rpc_interface_synth_top #(
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
  // type dependency
  parameter type         axi_addr_t    = logic [  AxiAddrWidth-1:0],
  parameter type         axi_data_t    = logic [  AxiDataWidth-1:0],
  parameter type         axi_id_t      = logic [  AxiIdWidth  -1:0],
  parameter type         axi_strb_t    = logic [AxiDataWidth/8-1:0],
  parameter type         axi_user_t    = logic [  AxiUserWidth-1:0],
  parameter type         dram_blen_t   = logic [               5:0],
  parameter type         dram_addr_t   = logic [              19:0],
  parameter type         phy_data_t    = logic [ DramWordWidth-1:0],
  parameter type         cmd_addr_t    = logic [ DramAddrWidth-1:0],
  parameter type         mask_t        = logic [              63:0]
) (
  // common signals
  input  logic     clk_i,
  input  logic    rst_ni,

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

  // phy master port
  output logic       phy_w_data_valid_o,
  output logic       phy_r_data_ready_o,
  output phy_data_t                   phy_w_data_o,

  input  logic       phy_w_data_ready_i,
  input  logic       phy_r_data_valid_i,
  input  phy_data_t                   phy_r_data_i,
  input  logic       phy_r_data_last_i,

  // cmd master port
  output logic       cmd_valid_o,
  output logic       cmd_is_write_o,
  output dram_blen_t      cmd_len_o,
  output cmd_addr_t                   cmd_addr_o,

  input  logic       cmd_ready_i,

  output mask_t                       write_mask_o
);



  // Type define
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

  // phy port
  rpc_ctrl_pkg::phy_req_t phy_req;
  rpc_ctrl_pkg::phy_rsp_t phy_rsp;

  // cmd port
  rpc_ctrl_pkg::axi_cmd_req_t cmd_req;
  rpc_ctrl_pkg::axi_cmd_rsp_t cmd_rsp;


  // wrapped instance
  rpc_interface #(
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

    .phy_req_t(rpc_ctrl_pkg::phy_req_t),
    .phy_rsp_t(rpc_ctrl_pkg::phy_rsp_t),

    .cmd_req_t(rpc_ctrl_pkg::axi_cmd_req_t),
    .cmd_rsp_t(rpc_ctrl_pkg::axi_cmd_rsp_t)
  ) i_rpc_interface (
    .clk_i (clk_i),
    .rst_ni(rst_ni),

    .axi_req_i (axi_req),
    .axi_resp_o(axi_rsp),

    .phy_req_o(phy_req),
    .phy_rsp_i(phy_rsp),

    .cmd_req_o(cmd_req),
    .cmd_rsp_i(cmd_rsp),

    .write_mask_o(write_mask_o)
  );

  // signal assignment
  // axi slave port
  assign axi_req.aw.id        = axi_aw_id_i;
  assign axi_req.aw.addr      = axi_aw_addr_i;
  assign axi_req.aw.len       = axi_aw_len_i;
  assign axi_req.aw.size      = axi_aw_size_i;
  assign axi_req.aw.burst     = axi_aw_burst_i;
  assign axi_req.aw.lock      = axi_aw_lock_i;
  assign axi_req.aw.cache     = axi_aw_cache_i;
  assign axi_req.aw.prot      = axi_aw_prot_i;
  assign axi_req.aw.qos       = axi_aw_qos_i;
  assign axi_req.aw.region    = axi_aw_region_i;
  assign axi_req.aw.atop      = axi_aw_atop_i;
  assign axi_req.aw.user      = axi_aw_user_i;
  assign axi_req.aw_valid     = axi_aw_valid_i;
  assign axi_aw_ready_o       = axi_rsp.aw_ready;

  assign axi_req.w.data       = axi_w_data_i;
  assign axi_req.w.strb       = axi_w_strb_i;
  assign axi_req.w.last       = axi_w_last_i;
  assign axi_req.w.user       = axi_w_user_i;
  assign axi_req.w_valid      = axi_w_valid_i;
  assign axi_w_ready_o        = axi_rsp.w_ready;

  assign axi_b_id_o           = axi_rsp.b.id;
  assign axi_b_resp_o         = axi_rsp.b.resp;
  assign axi_b_user_o         = axi_rsp.b.user;
  assign axi_b_valid_o        = axi_rsp.b_valid;
  assign axi_req.b_ready      = axi_b_ready_i;

  assign axi_req.ar.id        = axi_ar_id_i;
  assign axi_req.ar.addr      = axi_ar_addr_i;
  assign axi_req.ar.len       = axi_ar_len_i;
  assign axi_req.ar.size      = axi_ar_size_i;
  assign axi_req.ar.burst     = axi_ar_burst_i;
  assign axi_req.ar.lock      = axi_ar_lock_i;
  assign axi_req.ar.cache     = axi_ar_cache_i;
  assign axi_req.ar.prot      = axi_ar_prot_i;
  assign axi_req.ar.qos       = axi_ar_qos_i;
  assign axi_req.ar.region    = axi_ar_region_i;
  assign axi_req.ar.user      = axi_ar_user_i;
  assign axi_req.ar_valid     = axi_ar_valid_i;
  assign axi_ar_ready_o       = axi_rsp.ar_ready;

  assign axi_r_id_o           = axi_rsp.r.id;
  assign axi_r_data_o         = axi_rsp.r.data;
  assign axi_r_resp_o         = axi_rsp.r.resp;
  assign axi_r_last_o         = axi_rsp.r.last;
  assign axi_r_user_o         = axi_rsp.r.user;
  assign axi_r_valid_o        = axi_rsp.r_valid;
  assign axi_req.r_ready      = axi_r_ready_i;

  // phy port
  assign phy_w_data_valid_o   = phy_req.w_data_valid;
  assign phy_r_data_ready_o   = phy_req.r_data_ready;
  assign phy_w_data_o         = phy_req.w_data;

  assign phy_rsp.w_data_ready = phy_w_data_ready_i;
  assign phy_rsp.r_data_valid = phy_r_data_valid_i;
  assign phy_rsp.r_data       = phy_r_data_i;
  assign phy_rsp.r_data_last  = phy_r_data_last_i;

  // cmd port
  assign cmd_valid_o          = cmd_req.cmd_valid;
  assign cmd_is_write_o       = cmd_req.is_write;
  assign cmd_len_o            = cmd_req.len;
  assign cmd_addr_o           = cmd_req.addr;

  assign cmd_rsp.cmd_ready    = cmd_ready_i;


endmodule
