// rpc top module for fpga synthesis

module rpc_fpga_top (

    // clock and reset
    input  logic            clkp_i,
    input  logic            clkn_i,
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
    output wire rpc_clk_o,
    output wire rpc_clk_no,
    output wire rpc_cs_no,
    output wire rpc_stb_o,

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

  logic       rpc_clk;

  // differential to single ended clock conversion
  IBUFGDS #(
    .IOSTANDARD  ("LVDS" ),
    .DIFF_TERM   ("FALSE"),
    .IBUF_LOW_PWR("FALSE")
  ) i_sysclk_iobuf (
    .I (clkp_i),
    .IB(clkn_i),
    .O (rpc_clk)
  );

  // rpc iobuf
  logic out_dqs, out_dqsn, in_dqs, in_dqsn, o_dqs, oe_dqsn, oe_db;
  logic [15:0] out_db, in_db;

  iobuf_rpc_fpga i_iobuf_rpc(
    // output enable
    .oe_dqs_i(oe_dqs),
    .oe_dqsn_i(oe_dqsn),
    .oe_db_i(oe_db),

    // input from tri-state pad
    .in_dqs_o(in_dqs),
    .in_dqsn_o(in_dqsn),
    .in_db_o(in_db),

    // output to tri-state pad
    .out_dqs_i(out_dqs),
    .out_dqsn_i(out_dqsn),
    .out_db_i(out_db),

    // tri-state signals
    .dqs(rpc_dqs),
    .dqsn(rpc_dqsn),
    .db0(rpc_db0),
    .db1(rpc_db1),
    .db2(rpc_db2),
    .db3(rpc_db3),
    .db4(rpc_db4),
    .db5(rpc_db5),
    .db6(rpc_db6),
    .db7(rpc_db7),
    .db8(rpc_db8),
    .db9(rpc_db9),
    .dba(rpc_dba),
    .dbb(rpc_dbb),
    .dbc(rpc_dbc),
    .dbd(rpc_dbd),
    .dbe(rpc_dbe),
    .dbf(rpc_dbf)
  );

  // parameterize rpc controller and instantiate it
  localparam int unsigned AxiIdWidth = 6;
  localparam int unsigned AxiAddrWidth = 48;
  localparam int unsigned AxiDataWidth = 64;
  localparam int unsigned AxiUserWidth = 1;

  localparam int unsigned DramDataWidth = 256;
  localparam int unsigned DramLenWidth = 6;
  localparam int unsigned DramAddrWidth = 20;
  localparam int unsigned BufferDepth = 4;

  localparam int unsigned PHY_CLOCK_PERIOD = 5;

  rpc_synth_wrap #(
    .AxiDataWidth     (AxiDataWidth),
    .AxiAddrWidth     (AxiAddrWidth),
    .AxiIdWidth       (AxiIdWidth),
    .AxiUserWidth     (AxiUserWidth),

    .DramDataWidth    (DramDataWidth),
    .DramLenWidth     (DramLenWidth),
    .DramAddrWidth    (DramAddrWidth),
    .BufferDepth      (BufferDepth),

    .PHY_CLOCK_PERIOD (PHY_CLOCK_PERIOD)
  ) i_rpc_wrap (

    // common signals
    .clk_i(rpc_clk),
    .rst_ni,

    // axi slave port
    .axi_aw_id_i,
    .axi_aw_addr_i,
    .axi_aw_len_i,
    .axi_aw_size_i,
    .axi_aw_burst_i,
    .axi_aw_lock_i,
    .axi_aw_cache_i,
    .axi_aw_prot_i,
    .axi_aw_qos_i,
    .axi_aw_region_i,
    .axi_aw_atop_i,
    .axi_aw_user_i,
    .axi_aw_valid_i,
    .axi_aw_ready_o,
    .axi_w_data_i,
    .axi_w_strb_i,
    .axi_w_last_i,
    .axi_w_user_i,
    .axi_w_valid_i,
    .axi_w_ready_o,
    .axi_b_id_o,
    .axi_b_resp_o,
    .axi_b_user_o,
    .axi_b_valid_o,
    .axi_b_ready_i,
    .axi_ar_id_i,
    .axi_ar_addr_i,
    .axi_ar_len_i,
    .axi_ar_size_i,
    .axi_ar_burst_i,
    .axi_ar_lock_i,
    .axi_ar_cache_i,
    .axi_ar_prot_i,
    .axi_ar_qos_i,
    .axi_ar_region_i,
    .axi_ar_user_i,
    .axi_ar_valid_i,
    .axi_ar_ready_o,
    .axi_r_id_o,
    .axi_r_data_o,
    .axi_r_resp_o,
    .axi_r_last_o,
    .axi_r_user_o,
    .axi_r_valid_o,
    .axi_r_ready_i,

    // Regbus Request Input
    .reg_addr_i,
    .reg_write_i,
    .reg_wdata_i,
    .reg_wstrb_i,
    .reg_valid_i,

    // Regbus Request Output
    .reg_error_o,
    .reg_rdata_o,
    .reg_ready_o,

    // Controller to RPC DRAM Port
    .rpc_clk_o (rpc_clk_o),
    .rpc_clk_no(rpc_clk_no),
    .rpc_cs_no (rpc_cs_no),
    .rpc_stb_o (rpc_stb_o),
    .phy_dqs_o (out_dqs),
    .phy_dqs_n_o (out_dqsn),
    .phy_dqs_i (in_dqs),
    .phy_dqs_n_i (in_dqsn),
    .phy_dqs_pair_oe_o (oe_dqs),
    .phy_dqs_pair_ie_o (), // unconnected, assume pad -> dut path always enabled
    .phy_dqs_pair_pd_en_o (), // unconnected, assume pad -> dut path always enabled
    .phy_db_o (out_db),
    .phy_db_i (in_db),
    .phy_db_oe_o (oe_db),
    .phy_db_ie_o (),  // unconnected, assume pad -> dut path always enabled
    .phy_db_pd_en_o () // unconnected, assume pad -> dut path always enabled
  );


endmodule
