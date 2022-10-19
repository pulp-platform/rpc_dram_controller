// Copyright 2022 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Thomas Benz <tbenz@iis.ee.ethz.ch>
// Paul Scheffler <paulsc@iis.ee.ethz.ch>
//
// Based on work of:
// Fabian Schuiki <fschuiki@iis.ee.ethz.ch>
// Florian Zaruba <zarubaf@iis.ee.ethz.ch>

(* no_ungroup *)
(* no_boundary_optimization *)
module generic_delay_D5_O1_5P000_CG0 (
  input  logic       clk_i,
  input  logic       enable_i,
  input  logic [5-1:0] delay_i,
  output logic [1-1:0] clk_o
);


  timeunit 1ps;
  timeprecision 1fs;

  logic enable_latched;
  logic clk;
  
  assign clk = clk_i;

  always @(clk) clk_o[0] <= #(real'(delay_i)*5.000ns/31) clk;

endmodule
