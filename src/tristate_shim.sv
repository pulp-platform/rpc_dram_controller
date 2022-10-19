// Copyright 2022 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Vaibhav Krishna <vakrishna@student.ethz.ch>
// Rui Zhou <ruzhou@student.ethz.ch>
// Chen Jinfan <jinfchen@student.ethz.ch>

module tristate_shim (
    input  wire out_ena_i,
    input  wire out_i,
    output wire in_o,
    inout  wire line_io
);

    assign line_io = out_ena_i ? out_i : 1'bz;
    assign in_o    = out_ena_i ? 1'bx  : line_io;

endmodule : tristate_shim
