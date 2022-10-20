//-----------------------------------------------------------------------------
// Title         : PAD frame for RPC controller, FPGA mapping
//-----------------------------------------------------------------------------
// File          : padframe_rpc_fpga.sv
//-----------------------------------------------------------------------------
// Description :
// pad frame to have in/out tri-state signals exposed for fpga mapping to fmc.
//-----------------------------------------------------------------------------
// Copyright (C) 2013-2022 ETH Zurich, University of Bologna
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//-----------------------------------------------------------------------------

module iobuf_rpc_fpga (

  // OUTPUT ENABLE SIGNALS TO THE PADS
  input logic  oe_dqs_i,
  input logic  oe_dqsn_i,
  input logic  oe_db_i,

  // INPUTS SIGNALS FROM THE PADS
  output logic in_dqs_o,
  output logic in_dqsn_o,
  input logic [15:0]  in_db_o,

  // OUTPUT SIGNALS TO THE PADS
  input logic  out_dqs_i,
  input logic  out_dqsn_i,
  input logic  [15:0] out_db_i,

  // PMB PADS INOUT WIRES
  inout wire   dqs,
  inout wire   dqsn,
  inout wire   db0,
  inout wire   db1,
  inout wire   db2,
  inout wire   db3,
  inout wire   db4,
  inout wire   db5,
  inout wire   db6,
  inout wire   db7,
  inout wire   db8,
  inout wire   db9,
  inout wire   dba,
  inout wire   dbb,
  inout wire   dbc,
  inout wire   dbd,
  inout wire   dbe,
  inout wire   dbf
);

  // dqs, dqsn
  IOBUF #(
    .DRIVE       (12),
    .IBUF_LOW_PWR("FALSE"),
    .IOSTANDARD  ("DEFAULT"),
    .SLEW        ("FAST")
  ) i_dqsn_iobuf (
    .O (in_dqsn_o),
    .IO(dqsn),
    .I (out_dqsn_i),
    .T (~oe_dqsn_i)
  );

  IOBUF #(
    .DRIVE       (12),
    .IBUF_LOW_PWR("FALSE"),
    .IOSTANDARD  ("DEFAULT"),
    .SLEW        ("FAST")
  ) i_dqs_iobuf (
    .O (in_dqs_o),
    .IO(dqs),
    .I (out_dqs_i),
    .T (~oe_dqs_i)
  );

  // db
  IOBUF #(
    .DRIVE       (12),
    .IBUF_LOW_PWR("FALSE"),
    .IOSTANDARD  ("DEFAULT"),
    .SLEW        ("FAST")
  ) i_db0_iobuf (
    .O (in_db_o[0]),
    .IO(db0),
    .I (out_db_i[0]),
    .T (~oe_db_i)
  );
  IOBUF #(
    .DRIVE       (12),
    .IBUF_LOW_PWR("FALSE"),
    .IOSTANDARD  ("DEFAULT"),
    .SLEW        ("FAST")
  ) i_db1_iobuf (
    .O (in_db_o[1]),
    .IO(db1),
    .I (out_db_i[1]),
    .T (~oe_db_i)
  );
  IOBUF #(
    .DRIVE       (12),
    .IBUF_LOW_PWR("FALSE"),
    .IOSTANDARD  ("DEFAULT"),
    .SLEW        ("FAST")
  ) i_db2_iobuf (
    .O (in_db_o[2]),
    .IO(db2),
    .I (out_db_i[2]),
    .T (~oe_db_i)
  );
  IOBUF #(
    .DRIVE       (12),
    .IBUF_LOW_PWR("FALSE"),
    .IOSTANDARD  ("DEFAULT"),
    .SLEW        ("FAST")
  ) i_db3_iobuf (
    .O (in_db_o[3]),
    .IO(db3),
    .I (out_db_i[3]),
    .T (~oe_db_i)
  );
  IOBUF #(
    .DRIVE       (12),
    .IBUF_LOW_PWR("FALSE"),
    .IOSTANDARD  ("DEFAULT"),
    .SLEW        ("FAST")
  ) i_db4_iobuf (
    .O (in_db_o[4]),
    .IO(db4),
    .I (out_db_i[4]),
    .T (~oe_db_i)
  );
  IOBUF #(
    .DRIVE       (12),
    .IBUF_LOW_PWR("FALSE"),
    .IOSTANDARD  ("DEFAULT"),
    .SLEW        ("FAST")
  ) i_db5_iobuf (
    .O (in_db_o[5]),
    .IO(db5),
    .I (out_db_i[5]),
    .T (~oe_db_i)
  );
  IOBUF #(
    .DRIVE       (12),
    .IBUF_LOW_PWR("FALSE"),
    .IOSTANDARD  ("DEFAULT"),
    .SLEW        ("FAST")
  ) i_db6_iobuf (
    .O (in_db_o[6]),
    .IO(db6),
    .I (out_db_i[6]),
    .T (~oe_db_i)
  );
  IOBUF #(
    .DRIVE       (12),
    .IBUF_LOW_PWR("FALSE"),
    .IOSTANDARD  ("DEFAULT"),
    .SLEW        ("FAST")
  ) i_db7_iobuf (
    .O (in_db_o[7]),
    .IO(db7),
    .I (out_db_i[7]),
    .T (~oe_db_i)
  );
  IOBUF #(
    .DRIVE       (12),
    .IBUF_LOW_PWR("FALSE"),
    .IOSTANDARD  ("DEFAULT"),
    .SLEW        ("FAST")
  ) i_db8_iobuf (
    .O (in_db_o[8]),
    .IO(db8),
    .I (out_db_i[8]),
    .T (~oe_db_i)
  );
  IOBUF #(
    .DRIVE       (12),
    .IBUF_LOW_PWR("FALSE"),
    .IOSTANDARD  ("DEFAULT"),
    .SLEW        ("FAST")
  ) i_db9_iobuf (
    .O (in_db_o[9]),
    .IO(db9),
    .I (out_db_i[9]),
    .T (~oe_db_i)
  );
  IOBUF #(
    .DRIVE       (12),
    .IBUF_LOW_PWR("FALSE"),
    .IOSTANDARD  ("DEFAULT"),
    .SLEW        ("FAST")
  ) i_dba_iobuf (
    .O (in_db_o[10]),
    .IO(dba),
    .I (out_db_i[10]),
    .T (~oe_db_i)
  );
  IOBUF #(
    .DRIVE       (12),
    .IBUF_LOW_PWR("FALSE"),
    .IOSTANDARD  ("DEFAULT"),
    .SLEW        ("FAST")
  ) i_dbb_iobuf (
    .O (in_db_o[11]),
    .IO(dbb),
    .I (out_db_i[11]),
    .T (~oe_db_i)
  );
  IOBUF #(
    .DRIVE       (12),
    .IBUF_LOW_PWR("FALSE"),
    .IOSTANDARD  ("DEFAULT"),
    .SLEW        ("FAST")
  ) i_dbc_iobuf (
    .O (in_db_o[12]),
    .IO(dbc),
    .I (out_db_i[12]),
    .T (~oe_db_i)
  );
  IOBUF #(
    .DRIVE       (12),
    .IBUF_LOW_PWR("FALSE"),
    .IOSTANDARD  ("DEFAULT"),
    .SLEW        ("FAST")
  ) i_dbd_iobuf (
    .O (in_db_o[13]),
    .IO(dbd),
    .I (out_db_i[13]),
    .T (~oe_db_i)
  );
  IOBUF #(
    .DRIVE       (12),
    .IBUF_LOW_PWR("FALSE"),
    .IOSTANDARD  ("DEFAULT"),
    .SLEW        ("FAST")
  ) i_dbe_iobuf (
    .O (in_db_o[14]),
    .IO(dbe),
    .I (out_db_i[14]),
    .T (~oe_db_i)
  );
  IOBUF #(
    .DRIVE       (12),
    .IBUF_LOW_PWR("FALSE"),
    .IOSTANDARD  ("DEFAULT"),
    .SLEW        ("FAST")
  ) i_dbf_iobuf (
    .O (in_db_o[15]),
    .IO(dbf),
    .I (out_db_i[15]),
    .T (~oe_db_i)
  );

endmodule
