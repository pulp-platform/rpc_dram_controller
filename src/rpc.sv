// Copyright 2022 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Suyang Song <susong@student.ethz.ch>
// Bowen Wang <bowwang@student.ethz.ch>
// Chen Wang <chewang@student.ethz.ch>
// Jiawei Zhang <jiawzhang@student.ethz.ch>

// Top RPC DRAM Interface Module
// Internal interface:
//         1.Standard AXI Interface for Data Transmission
//              axi_req_i
//              axi_rsp_o
//         2.Standard REG BUS Interface for Configuration
//              reg_req_i
//              reg_rsp_o     
//        
// External interface:
//         DRAM Interface ports connected to IO PAD
module rpc #(
    parameter int PHY_CLOCK_PERIOD = 5,

    //axi data, id, address bus width
    //defined by wrapper
    parameter int unsigned AxiDataWidth = 64,
    parameter int unsigned AxiAddrWidth = 48,
    parameter int unsigned AxiIdWidth   = 6,
    parameter int unsigned AxiUserWidth = 1,
    //Master port data width
    parameter int unsigned DramDataWidth = 256,
    parameter int unsigned DramLenWidth  = 6,
    parameter int unsigned DramAddrWidth = 20,
    parameter int unsigned BufferDepth   = 4,
    
    //axi port type, passed by wrapper
    //comply with data, id address bus width
    //previous axi interface data type
    parameter type axi_req_t  = logic,
    parameter type axi_rsp_t  = logic,

    parameter type reg_req_t = logic,
    parameter type reg_rsp_t = logic

)(
    
    // ----------------------------------------------------------------------------------------------
    // ----------------------------clock and reset input  -------------------------------------------
    // ----------------------------------------------------------------------------------------------
      input logic                         clk_i,
      input logic                         rst_ni,

    // ----------------------------------------------------------------------------------------------
    // ----------------------------upstream interface  ----------------------------------------------
    // ----------------------------------------------------------------------------------------------
      // axi interface 
      input   axi_req_t                   axi_req_i,
      output  axi_rsp_t                   axi_rsp_o,

      // reg bus interface
      input   reg_req_t                   reg_req_i,
      output  reg_rsp_t                   reg_rsp_o, 
    // ----------------------------------------------------------------------------------------------
    // ----------------------------RPC DRAM interface  ----------------------------------------------
    // ----------------------------------------------------------------------------------------------

      // Controller to RPC DRAM Port
      output  logic                       rpc_clk_o,    
      output  logic                       rpc_clk_no,  
      output  logic                       rpc_cs_no,    
      output  logic                       rpc_stb_o,    

      //Output DQS for RPC DRAM WRITE Operation
      output  logic                       phy_dqs_o,
      output  logic                       phy_dqs_n_o, 

      //Input DQS for RPC DRAM READ Operation
      input   logic                       phy_dqs_i,  
      input   logic                       phy_dqs_n_i, 

      //Bi-directional Tri-state Buffer Enable Signal
      output  logic                       phy_dqs_pair_oe_o,  
      output  logic                       phy_dqs_pair_ie_o,
      output  logic                       phy_dqs_pair_pd_en_o, 

      //----------------DB Strobe Interface--------------------
      output  logic [16-1 : 0]            phy_db_o,
      input   logic [16-1 : 0]            phy_db_i,  
      output  logic                       phy_db_oe_o,
      output  logic                       phy_db_ie_o,
      output  logic                       phy_db_pd_en_o
);


// inter connection signals
  
rpc_ctrl_pkg::phy_req_t         phy_req;
rpc_ctrl_pkg::phy_rsp_t         phy_rsp;

rpc_ctrl_pkg::axi_cmd_req_t     cmd_req;
rpc_ctrl_pkg::axi_cmd_rsp_t     cmd_rsp;

logic[63:0] write_mask;

  // wrapped instance
  rpc_interface #(
      .AxiDataWidth   (AxiDataWidth),
      .AxiAddrWidth   (AxiAddrWidth),
      .AxiIdWidth     (AxiIdWidth),
      .AxiUserWidth   (AxiUserWidth),

      .DramDataWidth  (DramDataWidth),
      .DramLenWidth   (DramLenWidth),
      .DramAddrWidth  (DramAddrWidth),
      .BufferDepth    (BufferDepth),

      .axi_req_t      (axi_req_t),
      .axi_rsp_t      (axi_rsp_t),

      .phy_req_t      (rpc_ctrl_pkg::phy_req_t),
      .phy_rsp_t      (rpc_ctrl_pkg::phy_rsp_t),

      .cmd_req_t      (rpc_ctrl_pkg::axi_cmd_req_t),
      .cmd_rsp_t      (rpc_ctrl_pkg::axi_cmd_rsp_t)
  ) i_rpc_interface (
      .clk_i          (clk_i),
      .rst_ni         (rst_ni),

      .axi_req_i      (axi_req_i),
      .axi_resp_o     (axi_rsp_o),

      .phy_req_o      (phy_req),
      .phy_rsp_i      (phy_rsp),

      .cmd_req_o      (cmd_req),
      .cmd_rsp_i      (cmd_rsp),

      .write_mask_o   (write_mask)
  );



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
      .reg_req_i              (reg_req_i              ),
      .reg_rsp_o              (reg_rsp_o              ),

      // ---------- axi -> dram datapath  -------------
      .phy_req_i              (phy_req                ),
      .phy_rsp_o              (phy_rsp                ),
      .write_mask_i           (write_mask             ),

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

      .phy_dqs_pair_oe_o      (phy_dqs_pair_oe_o      ),
      .phy_dqs_pair_ie_o      (phy_dqs_pair_ie_o      ),
      .phy_dqs_pair_pd_en_o   (phy_dqs_pair_pd_en_o   ),

      .phy_db_o               (phy_db_o               ),
      .phy_db_i               (phy_db_i               ),
      .phy_db_oe_o            (phy_db_oe_o            ),
      .phy_db_ie_o            (phy_db_ie_o            ),
      .phy_db_pd_en_o         (phy_db_pd_en_o         )
    );

endmodule 