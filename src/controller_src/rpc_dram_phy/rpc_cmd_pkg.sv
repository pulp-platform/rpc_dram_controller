// Copyright 2022 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Chen Wang <chewang@student.ethz.ch>
// Jiawei Zhang <jiawzhang@student.ethz.ch>

package rpc_cmd_pkg;

  // ---------- decoded cmd type based   --------------------------
  localparam int unsigned CMD_INVALID 	= 0;
  localparam int unsigned CMD_RESET 	  = 1;
  localparam int unsigned CMD_PRE   	  = 2;
  localparam int unsigned CMD_MRS		    = 3;
  localparam int unsigned CMD_ACT		    = 4;
  localparam int unsigned CMD_WR		    = 5;
  localparam int unsigned CMD_RD		    = 6;
  localparam int unsigned CMD_REF		    = 7;
  localparam int unsigned CMD_ZQC		    = 8;


  //---------- ZQC Mode --------------------------------
  localparam int unsigned ZQC_ZQINIT 	= 0;
  localparam int unsigned ZQC_ZQCL 		= 1;
  localparam int unsigned ZQC_ZQCS   	= 2;
  localparam int unsigned ZQC_ZQRESET	= 3;

endpackage // rpc_cmd_pkg