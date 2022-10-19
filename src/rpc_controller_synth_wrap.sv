// Copyright 2022 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Chen Wang <chewang@student.ethz.ch>
// Jiawei Zhang <jiawzhang@student.ethz.ch>

// The wrapper used to perform the context-free independent synthesis of rpc_controller_top
// Do not use this module for other purpose!!

module rpc_controller_synth_wrap #(
    parameter int unsigned PHY_CLOCK_PERIOD = 5,

    parameter int unsigned REG_ADDR_WIDTH = 5,
    parameter int unsigned REG_DATA_WIDTH = 32,
    localparam int unsigned REG_STORBE_WIDTH = REG_DATA_WIDTH/8,

    //----------- AXI Interface Port Defination -----------------------
    //RPC DRAM word: 256bits = 32byte -> log2(32) = 5
    parameter int unsigned DRAM_ALIGN_POS  = 5,
    //bank + row + column address = 20bits wide
    parameter int unsigned DRAM_ADDR_WIDTH = 20,
    //Dram word width
    parameter int unsigned DRAM_WORD_WIDTH = 256,
    //Mast width
    parameter int unsigned DRAM_MASK_WIDTH = 64
  )(
    // ----------------------------------------------------------------------------------------------
    // ----------------------------clock and reset input  -------------------------------------------
    // ----------------------------------------------------------------------------------------------

      input logic                         clk_i,
      input logic                         rst_ni,

    // ----------------------------------------------------------------------------------------------
    // ----------------------------upstream interface  ----------------------------------------------
    // ----------------------------------------------------------------------------------------------
      //----------- Reg Bus Interface Port ----
      // Regbus Request Input
      input logic [REG_ADDR_WIDTH-1:0]      addr_i, 
      input logic                           write_i,  
      input logic [REG_DATA_WIDTH-1:0]      wdata_i,  
      input logic [REG_STORBE_WIDTH-1:0]    wstrb_i,  
      input logic                           valid_i, 

      // Regbus Request Output
      output logic                          error_o,
      output logic [REG_DATA_WIDTH-1:0]     rdata_o, 
      output logic                          ready_o, 

      //----------- AXI Interface Port ------- 
      // Phy req port
      input logic                           phy_req_w_data_valid_i,
      input logic                           phy_req_r_data_ready,
      input logic [DRAM_WORD_WIDTH-1:0]     phy_req_w_data,

      // Phy rsp port
      output logic                          phy_rsp_w_data_ready,
      output logic                          phy_rsp_r_data_valid,
      output logic [DRAM_WORD_WIDTH-1:0]    phy_rsp_r_data,
      output logic                          phy_rsp_r_data_last,

      // axi cmd request port
      input logic                           cmd_req_cmd_valid,
      input logic                           cmd_req_is_write,
      input logic [DRAM_ALIGN_POS-1 :0]     cmd_req_len,
      input logic [DRAM_ADDR_WIDTH-1:0]     cmd_req_addr,

      // axi cmd response port
      output logic                          cmd_rsp_cmd_ready,

      // data mask port
      input logic [DRAM_MASK_WIDTH-1:0]     write_mask_i,

    // ----------------------------------------------------------------------------------------------
    // ----------------------------module -> RPC DRAM  ----------------------------------------------
    // ----------------------------------------------------------------------------------------------

      // Controller to RPC DRAM Port
      output logic                          rpc_clk_o,    
      output logic                          rpc_clk_no,  
      output logic                          rpc_cs_no,    
      output logic                          rpc_stb_o,    

      output logic                          phy_dqs_o,
      output logic                          phy_dqs_n_o, 

      input  logic                          phy_dqs_i,  
      input  logic                          phy_dqs_n_i, 

      output logic                          phy_dqs_oe_o,  
      output logic                          phy_dqs_n_oe_o, 

      output logic [16-1 : 0]               phy_db_o,
      input  logic [16-1 : 0]               phy_db_i,  
      output logic                          phy_db_oe_o    
  );



  // define the reg bus interface structure

  typedef logic [REG_ADDR_WIDTH-1:0]   reg_addr_t;
  typedef logic [REG_DATA_WIDTH-1:0]   reg_data_t;
  typedef logic [REG_STORBE_WIDTH-1:0] reg_strb_t;

  typedef struct packed {
    reg_addr_t  addr;
    logic       write;
    reg_data_t  wdata;
    reg_strb_t  wstrb;
    logic       valid;
  } reg_req_t;


  typedef struct packed {
    reg_data_t  rdata;
    logic       ready;
    logic       error;
  } reg_rsp_t;


  reg_req_t   reg_bus_req;
  reg_rsp_t   reg_bus_rsp;


  assign reg_bus_req = reg_req_t'{
      addr:   addr_i,
      write:  write_i,
      wdata:  wdata_i,
      wstrb:  wstrb_i,
      valid:  valid_i
  };


  assign rdata_o = reg_bus_rsp.rdata;
  assign ready_o = reg_bus_rsp.ready;
  assign error_o = reg_bus_rsp.error;


  // define the port connected to the AXI interface
  rpc_ctrl_pkg::axi_cmd_req_t cmd_req;
  rpc_ctrl_pkg::axi_cmd_rsp_t cmd_rsp;
  rpc_ctrl_pkg::phy_req_t phy_req;
  rpc_ctrl_pkg::phy_rsp_t phy_rsp;

  assign phy_req = '{
    w_data_valid: phy_req_w_data_valid_i,
    r_data_ready: phy_req_r_data_ready,
    w_data:       phy_req_w_data
    };

  assign phy_rsp = '{
    w_data_ready: phy_rsp_w_data_ready,
    r_data_valid: phy_rsp_r_data_valid,
    r_data:       phy_rsp_r_data,
    r_data_last:  phy_rsp_r_data_last
  };

  assign cmd_req = '{
    cmd_valid:    cmd_req_cmd_valid,
    is_write:     cmd_req_is_write,
    len:          cmd_req_len,
    addr:         cmd_req_addr
  };

  assign cmd_rsp.cmd_ready = cmd_rsp_cmd_ready;


  rpc_controller #(
      .PHY_CLOCK_PERIOD       (PHY_CLOCK_PERIOD),
      .reg_req_t              (reg_req_t),
      .reg_rsp_t              (reg_rsp_t),
      .phy_req_t              (rpc_ctrl_pkg::phy_req_t),
      .phy_rsp_t              (rpc_ctrl_pkg::phy_rsp_t),
      .axi_cmd_req_t          (rpc_ctrl_pkg::axi_cmd_req_t),
      .axi_cmd_rsp_t          (rpc_ctrl_pkg::axi_cmd_rsp_t)
    ) i_rpc_controller (

        // ---------- lock and reset input ----------
      .clk_i                  (clk_i                  ),
      .rst_ni                 (rst_ni                 ),

      // ---------- upstream reg bus interface -------
      .reg_req_i              (reg_bus_req            ),
      .reg_rsp_o              (reg_bus_rsp            ),

      // ---------- axi -> dram datapath  -------------
      .phy_req_i              (phy_req                ),
      .phy_rsp_o              (phy_rsp                ),
      .write_mask_i           (write_mask_i           ),

      // ---------- axi -> dram w/r cmd path  ---------
      .axi_cmd_req_i          (cmd_req                ),
      .axi_cmd_rsp_o          (cmd_rsp                ),

      // ---------- to RPC DRAM -----------------------
      .rpc_clk_o              (rpc_clk_o              ),
      .rpc_clk_no             (rpc_clk_no             ),
      .rpc_cs_no              (rpc_cs_no              ),
      .rpc_stb_o              (rpc_stb_o              ),

      .phy_dqs_o              (phy_dqs_o              ),
      .phy_dqs_n_o            (phy_dqs_n_o            ),

      .phy_dqs_i              (phy_dqs_i              ),
      .phy_dqs_n_i            (phy_dqs_n_i            ),

      .phy_dqs_oe_o           (phy_dqs_oe_o           ),
      .phy_dqs_n_oe_o         (phy_dqs_n_oe_o         ),

      .phy_db_o               (phy_db_o               ),
      .phy_db_i               (phy_db_i               ),
      .phy_db_oe_o            (phy_db_oe_o            )             
    );






endmodule
