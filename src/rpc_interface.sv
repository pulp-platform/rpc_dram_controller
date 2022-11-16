// Copyright 2022 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Suyang Song <susong@student.ethz.ch>
// Bowen Wang <bowwang@student.ethz.ch>

`include "axi/assign.svh"
`include "axi/typedef.svh"

//rpc interface: module between AXI4 bus and SRAM buffer
//3 stages: Atomic operations filter -> ID serializer -> Dataword Converter
module rpc_interface #(

  //axi data, id, address bus width
  //defined by wrapper
  parameter int unsigned AxiDataWidth = 64,
  parameter int unsigned AxiAddrWidth = 48,
  parameter int unsigned AxiIdWidth = 6,
  parameter int unsigned AxiUserWidth = 1,
  //Master port data width
  parameter int unsigned DramDataWidth = 256,
  parameter int unsigned DramLenWidth = 6,
  parameter int unsigned DramAddrWidth = 20,
  parameter int unsigned BufferDepth = 4,

  //axi port type, passed by wrapper
  //comply with data, id address bus width
  //previous axi interface data type
  parameter type axi_req_t = logic,
  parameter type axi_rsp_t = logic,

  //follow-up phy request and response signal
  parameter type phy_req_t = logic,
  parameter type phy_rsp_t = logic,
  //follow-up cmd_fsm interface
  parameter type cmd_req_t = logic,
  parameter type cmd_rsp_t = logic
) (
  input  logic      clk_i,
  input  logic      rst_ni,

  //axi port signals
  input  axi_req_t    axi_req_i,
  output axi_rsp_t       axi_resp_o,

  //master port phy and command signals
  output phy_req_t    phy_req_o,
  input  phy_rsp_t    phy_rsp_i,

  output cmd_req_t       cmd_req_o,
  input  cmd_rsp_t       cmd_rsp_i,

  output logic[63:0]     write_mask_o
);

  localparam int unsigned AxiLenWidth = 8;
  localparam int unsigned ExtraIdWidth = BufferDepth == 1 ? 1 : $clog2(BufferDepth);


  typedef logic [AxiUserWidth-1:0] user_t;
  typedef logic [AxiAddrWidth-1:0] addr_t;
  typedef logic [AxiIdWidth-1:0] id_t;
  typedef logic [AxiDataWidth-1:0] data_t;
  typedef logic [AxiDataWidth/8-1:0] strb_t;

  typedef logic [DramDataWidth-1:0] up_data_t;
  typedef logic [DramDataWidth/8-1:0] up_strb_t;
  typedef logic [AxiIdWidth + ExtraIdWidth-1:0] parl_id_t;



  //Define prepend axi request and response
  `AXI_TYPEDEF_AW_CHAN_T(parl_aw_chan_t, addr_t, parl_id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(parl_w_chan_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(parl_b_chan_t, parl_id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(parl_ar_chan_t, addr_t, parl_id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(parl_r_chan_t, data_t, parl_id_t, user_t)
  `AXI_TYPEDEF_REQ_T(parl_req_t, parl_aw_chan_t, parl_w_chan_t, parl_ar_chan_t)
  `AXI_TYPEDEF_RESP_T(parl_resp_t, parl_b_chan_t, parl_r_chan_t)


  //Define upsized axi request and response


  `AXI_TYPEDEF_AW_CHAN_T(up_aw_chan_t, addr_t, parl_id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(up_w_chan_t, up_data_t, up_strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(up_b_chan_t, parl_id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(up_ar_chan_t, addr_t, parl_id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(up_r_chan_t, up_data_t, parl_id_t, user_t)
  `AXI_TYPEDEF_REQ_T(up_req_t, up_aw_chan_t, up_w_chan_t, up_ar_chan_t)
  `AXI_TYPEDEF_RESP_T(up_resp_t, up_b_chan_t, up_r_chan_t)



  //axi request after serialized
  axi_req_t ser_out_req;
  axi_rsp_t ser_out_resp;

  //axi upsized request after upsized
  up_req_t up_req_o;
  up_resp_t up_resp_i;



  //---------------------------------------------------------------------------
  //-------------------------axi serializer to filter IDs----------------------
  //---------------------------------------------------------------------------
  //AXI serializer: Convert transactions with multiple
  //IDs into single ID and send them to controller
  axi_serializer #(

    .MaxWriteTxns(BufferDepth),
    .MaxReadTxns (BufferDepth),
    .AxiIdWidth  (AxiIdWidth),
    .axi_req_t   (axi_req_t),
    .axi_resp_t  (axi_rsp_t)
  ) i_axi_serializer (
    .clk_i (clk_i),
    .rst_ni(rst_ni),

    //accept axi request and send response with IDs
    //to axi_atop_filter without atomic operations
    .slv_resp_o(axi_resp_o),
    .slv_req_i (axi_req_i),

    //send axi request and accept axi responses without
    //both IDs or atomic operations
    .mst_resp_i(ser_out_resp),
    .mst_req_o (ser_out_req)
  );



  //---------------------------------------------------------------------------
  //----------------------------read transactions parallelizer-----------------
  //---------------------------------------------------------------------------

  parl_req_t parl_out_req;
  parl_resp_t parl_out_resp;

  axi_parallelizer #(
    .ParallelNum(BufferDepth),
    .AxiIdWidth (AxiIdWidth),
    .mst_req_t  (parl_req_t),
    .mst_resp_t (parl_resp_t),
    .slv_req_t  (axi_req_t),
    .slv_resp_t (axi_rsp_t)
  ) i_axi_parallelizer (
    .clk_i     (clk_i),
    .rst_ni    (rst_ni),
    .slv_req_i (ser_out_req),
    .slv_resp_o(ser_out_resp),
    .mst_req_o (parl_out_req),
    .mst_resp_i(parl_out_resp)
  );

  //---------------------------------------------------------------------------
  //----------------------------axi buffer upsizer-----------------------------
  //---------------------------------------------------------------------------



  typedef logic [DramDataWidth-1:0] mst_data_t;
  typedef logic [DramDataWidth/8-1:0] mst_strb_t;
  typedef logic [AxiDataWidth-1:0] slv_data_t;
  typedef logic [AxiDataWidth/8-1:0] slv_strb_t;



  axi_dw_upsizer #(
    .AxiMaxReads        (BufferDepth),
    .AxiSlvPortDataWidth(AxiDataWidth),
    .AxiMstPortDataWidth(DramDataWidth),
    .AxiAddrWidth       (AxiAddrWidth),
    .AxiIdWidth         (AxiIdWidth + ExtraIdWidth),
    .aw_chan_t          (up_aw_chan_t),
    .mst_w_chan_t       (up_w_chan_t),
    .slv_w_chan_t       (parl_w_chan_t),

    .b_chan_t (up_b_chan_t),
    .ar_chan_t(up_ar_chan_t),

    .mst_r_chan_t(up_r_chan_t),
    .slv_r_chan_t(parl_r_chan_t),

    .axi_mst_req_t (up_req_t),
    .axi_mst_resp_t(up_resp_t),

    .axi_slv_req_t (parl_req_t),
    .axi_slv_resp_t(parl_resp_t)
  ) i_axi_dw_upsizer (
    .clk_i (clk_i),
    .rst_ni(rst_ni),

    .slv_req_i (parl_out_req),
    .slv_resp_o(parl_out_resp),

    .mst_req_o (up_req_o),
    .mst_resp_i(up_resp_i)
  );


  //---------------------------------------------------------------------------
  //------------------------------buffer_wrapper-------------------------------
  //---------------------------------------------------------------------------
  cmd_req_t buf_cmd_req;
  cmd_rsp_t buf_cmd_rsp;
  phy_req_t buf_phy_req;
  phy_rsp_t buf_phy_rsp;


  buffer_wrapper #(
    .DramAddrWidth(DramAddrWidth),
    .DramLenWidth (DramLenWidth),
    .DramDataWidth(DramDataWidth),

    .BufferDepth (BufferDepth),
    .AxiAddrWidth(AxiAddrWidth),
    .AxiLenWidth (AxiLenWidth),

    .AXI_ID_WIDTH  (AxiIdWidth + ExtraIdWidth),
    .AXI_USER_WIDTH(AxiUserWidth),

    //previous axi interface data type
    .axi_req_t(up_req_t),
    .axi_rsp_t(up_resp_t),

    //follow-up phy request and response signal
    .phy_req_t(phy_req_t),
    .phy_rsp_t(phy_rsp_t),
    //follow-up cmd_fsm interface
    .cmd_req_t(cmd_req_t),
    .cmd_rsp_t(cmd_rsp_t)
  ) i_buffer_wrapper (

    .clk_i (clk_i),
    .rst_ni(rst_ni),

    /////////////////////////////////
    /////axi4 interface wrapper slave
    /////////////////////////////////
    .axi_req_i(up_req_o),
    .axi_rsp_o(up_resp_i),

    /////////////////////////////////
    ////phy and fsm interface ///////
    /////////////////////////////////
    .phy_req_o(buf_phy_req),
    .phy_rsp_i(buf_phy_rsp),

    .cmd_req_o(buf_cmd_req),
    .cmd_rsp_i(buf_cmd_rsp)
  );


  assign phy_req_o = buf_phy_req;

  //---------------------------------------------------------------------------
  //------------------------------cmd_splitter---------------------------------
  //---------------------------------------------------------------------------
  //command splitter: deal with crossing 2K boundary issue

  logic [1:0] split_req_type;

  cmd_splitter #(
    .DramAddrWidth(DramAddrWidth),
    .DramLenWidth (DramLenWidth),

    .cmd_req_t(cmd_req_t),
    .cmd_rsp_t(cmd_rsp_t)
  ) i_cmd_splitter (
    .clk_i (clk_i),
    .rst_ni(rst_ni),

    //command splitter response port
    .cmd_req_i(buf_cmd_req),
    .cmd_rsp_o(buf_cmd_rsp),

    //command splitter master port
    //directly to the command output
    .cmd_req_o(cmd_req_o),
    .cmd_rsp_i(cmd_rsp_i),

    //split command mask output
    .split_req_o(split_req_type)
  );

  //---------------------------------------------------------------------------
  //----------------------------write_mask_generator---------------------------
  //---------------------------------------------------------------------------

  logic [63:0] write_strb_o;

  write_mask_generator #(

    .BufDepth (BufferDepth),
    .StrbWidth(DramDataWidth / 8)
  ) i_write_mask_generator (

    // input clk_i and reset_ni
    .clk_i (clk_i),
    .rst_ni(rst_ni),

    // data from write channel
    .w_last_i (up_req_o.w.last),
    .w_valid_i(up_req_o.w_valid),
    .w_ready_i(up_resp_i.w_ready),

    .w_strobe_i(up_req_o.w.strb),
    .len       (cmd_req_o.len),

    // data from cmd splitter
    .is_write_i (cmd_req_o.is_write),
    .cmd_valid_i(cmd_req_o.cmd_valid),
    .cmd_ready_i(cmd_rsp_i.cmd_ready),
    .split_req_i(split_req_type),

    // output mask directly go to output
    .w_mask_o(write_strb_o)
  );

  assign write_mask_o[63:32] = ~write_strb_o[31:0];
  assign write_mask_o[31:0]  = ~write_strb_o[63:32];

  //---------------------------------------------------------------------------
  //----------------------------read_last_mask---------------------------------
  //---------------------------------------------------------------------------
  read_mask_generator #(
    .phy_rsp_t(phy_rsp_t)
  ) i_read_mask_generator (
    .clk_i (clk_i),
    .rst_ni(rst_ni),

    //command transaction handshake signals
    .cmd_valid_i(cmd_req_o.cmd_valid),
    .cmd_ready_i(cmd_rsp_i.cmd_ready),

    //signals indicating attribute of executing transaction
    .split_req_i(split_req_type),
    .is_write_i (cmd_req_o.is_write),

    //read data path
    .phy_rsp_i(phy_rsp_i),
    .phy_rsp_o(buf_phy_rsp)
  );


`ifndef SYNTHESIS
  default disable iff (~rst_ni); write_transaction_sent :
  assert property (
    	@(posedge clk_i)
    	!(cmd_req_o.cmd_valid && cmd_rsp_i.cmd_ready && cmd_req_o.is_write)
    )
  else begin
    $display("-------------------------------------");
    $display("RPC Interface Module report:");
    $display("[%0tps] :controller is receiving one write transaction->addr: %h len: %d", $time,
             $sampled(cmd_req_o.addr), $sampled(cmd_req_o.len));
  end

  read_transaction_sent :
  assert property (
    	@(posedge clk_i)
    	!(cmd_req_o.cmd_valid && cmd_rsp_i.cmd_ready && !cmd_req_o.is_write)
    )
  else begin
    $display("-------------------------------------");
    $display("RPC Interface Module report:");
    $display("[%0tps] :controller is receiving one read transaction->addr: %h len: %d", $time,
             $sampled(cmd_req_o.addr), $sampled(cmd_req_o.len));
  end

  write_data_sent :
  assert property (@(posedge clk_i) !(phy_req_o.w_data_valid && phy_rsp_i.w_data_ready))
  else begin
    $display("-------------------------------------");
    $display("RPC Interface Module report:");
    $display("[%0tps] :controller has received write word-> data: %h ", $time, $sampled(
             phy_req_o.w_data));
    $display("-------------------------------------");
  end

  read_data_receive :
  assert property (@(posedge clk_i) !(phy_req_o.r_data_ready && phy_rsp_i.r_data_valid))
  else begin
    $display("-------------------------------------");
    $display("RPC Interface Module report:");
    $display("[%0tps] :controller is sending single read word -> data: %h ", $time, $sampled(
             phy_rsp_i.r_data));
  end

`endif


endmodule
