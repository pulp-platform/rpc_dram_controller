// Copyright 2022 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Chen Wang <chewang@student.ethz.ch>
// Jiawei Zhang <jiawzhang@student.ethz.ch>

module rpc_cmd_decoder #(
  parameter int DRAM_CMD_WIDTH = 32
) (
  input logic [DRAM_CMD_WIDTH-1:0] cmd_i,
  output logic [3:0] cmd_decoded_o,
  output logic [5:0] burst_length_o,
  output logic [1:0] zqc_mode_o,
  output logic [3:0] ref_bank_num_o
);


  always_comb begin

    cmd_decoded_o  = rpc_cmd_pkg::CMD_INVALID;
    burst_length_o = '0;
    zqc_mode_o     = '0;
    ref_bank_num_o = 4'd4;

    // ------------ RESET -----------
    if (cmd_i == {1'b0, 12'b0, 3'b000, 15'b0, 1'b1}) begin
      cmd_decoded_o = rpc_cmd_pkg::CMD_RESET;

      // ------------ PRE -----------
    end else if (cmd_i[18:16] == 3'b100 && cmd_i[0] == 1'b0) begin
      cmd_decoded_o = rpc_cmd_pkg::CMD_PRE;

      // ------------ MRS -----------
    end else if (cmd_i[18:16] == 3'b010 && cmd_i[0] == 1'b0) begin
      cmd_decoded_o = rpc_cmd_pkg::CMD_MRS;

      // ------------ ACT -----------
    end else if (cmd_i[18:16] == 3'b101 && cmd_i[0] == 1'b0) begin
      cmd_decoded_o = rpc_cmd_pkg::CMD_ACT;

      // ------------ WR -----------
    end else if (cmd_i[18:16] == 3'b001 && cmd_i[0] == 1'b0) begin
      cmd_decoded_o  = rpc_cmd_pkg::CMD_WR;
      burst_length_o = cmd_i[26:21];

      // ------------ RD -----------
    end else if (cmd_i[18:16] == 3'b000 && cmd_i[0] == 1'b0) begin
      cmd_decoded_o  = rpc_cmd_pkg::CMD_RD;
      burst_length_o = cmd_i[26:21];

      // ------------ REF -----------
    end else if (cmd_i[18:16] == 3'b110 && cmd_i[0] == 1'b0) begin
      cmd_decoded_o  = rpc_cmd_pkg::CMD_REF;
      ref_bank_num_o = cmd_i[25] + cmd_i[24] + cmd_i[23] + cmd_i[22];

      // ------------ ZQC -----------
    end else if (cmd_i[18:16] == 3'b001 && cmd_i[0] == 1'b1) begin
      cmd_decoded_o = rpc_cmd_pkg::CMD_ZQC;
      zqc_mode_o    = cmd_i[31:30];
    end else begin
      cmd_decoded_o = rpc_cmd_pkg::CMD_INVALID;
    end

  end


endmodule
