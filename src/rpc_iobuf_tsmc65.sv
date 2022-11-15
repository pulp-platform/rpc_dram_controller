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

module rpc_iobuf (

  input logic  oe_dqs_i,
  input logic  oe_db_i,

  input logic  ie_dqs_i,
  input logic  ie_db_i,

  output logic in_dqs_o,
  output logic in_dqsn_o,
  output logic [15:0] in_db_o,

  input logic  out_dqs_i,
  input logic  out_dqsn_i,
  input logic  [15:0] out_db_i,

  input logic  out_clk_i,
  input logic  out_clkn_i,
  input logic  out_stb_i,
  input logic  out_csn_i,

  input logic  pd_en_dqs_i,
  input logic  pd_en_db_i,

  inout wire   clk,
  inout wire   clkn,
  inout wire   stb,
  inout wire   csn,

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

  PDDW0408CDG i_pad_clk  (
    .I        (out_clk_i),
    .OEN      (1'b0),
    .DS       (1'b1),
    .C        (),
    .IE       (1'b0),
    .PE       (1'b0),
    .PAD      (clk)
  );


  PDDW0408CDG i_pad_clk_n  (
    .I        (out_clkn_i),
    .OEN      (1'b0),
    .DS       (1'b1),
    .C        (),
    .IE       (1'b0),
    .PE       (1'b0),
    .PAD      (clkn)
  );


  PDDW0408CDG i_pad_stb  (
    .I        (out_stb_i),
    .OEN      (1'b0),
    .DS       (1'b1),
    .C        (),
    .IE       (1'b0),
    .PE       (1'b0),
    .PAD      (stb)
  );


  PDDW0408CDG i_pad_cs_n  (
    .I        (out_csn_i),
    .OEN      (1'b0),
    .DS       (1'b1),
    .C        (),
    .IE       (1'b0),
    .PE       (1'b0),
    .PAD      (csn)
  );

  PDDW0408CDG i_pad_dqs  (
    .I        (out_dqs_i   ),
    .OEN      (~oe_dqs_i   ),
    .DS       (1'b1        ),
    .C        (in_dqs_o    ),
    .IE       (ie_dqs_i    ),
    .PE       (pd_en_dqs_i ),
    .PAD      (dqs         )
  );

  PDUW0408CDG i_pad_dqsn  (
    .I        (out_dqsn_i ),
    .OEN      (~oe_dqs_i  ),
    .DS       (1'b1        ),
    .C        (in_dqsn_o   ),
    .IE       (ie_dqs_i   ),
    .PE       (pd_en_dqs_i ),
    .PAD      (dqsn        )
  );

  PDDW0408CDG i_pad_db0  (
      .I    (out_db_i[0] ),
      .OEN  (~oe_db_i    ),
      .DS   (1'b1        ),
      .C    (in_db_o[0] ),
      .IE   (ie_db_i     ),
      .PE   (pd_en_db_i  ),
      .PAD  (db0         )
  );

  PDDW0408CDG i_pad_db1  (
      .I    (out_db_i[1] ),
      .OEN  (~oe_db_i    ),
      .DS   (1'b1        ),
      .C    (in_db_o[1] ),
      .IE   (ie_db_i     ),
      .PE   (pd_en_db_i  ),
      .PAD  (db1         )
  );

  PDDW0408CDG i_pad_db2  (
      .I    (out_db_i[2] ),
      .OEN  (~oe_db_i    ),
      .DS   (1'b1        ),
      .C    (in_db_o[2] ),
      .IE   (ie_db_i     ),
      .PE   (pd_en_db_i  ),
      .PAD  (db2         )
  );
  PDDW0408CDG i_pad_db3  (
      .I    (out_db_i[3] ),
      .OEN  (~oe_db_i    ),
      .DS   (1'b1        ),
      .C    (in_db_o[3] ),
      .IE   (ie_db_i     ),
      .PE   (pd_en_db_i  ),
      .PAD  (db3         )
  );
  PDDW0408CDG i_pad_db4  (
      .I    (out_db_i[4] ),
      .OEN  (~oe_db_i    ),
      .DS   (1'b1        ),
      .C    (in_db_o[4] ),
      .IE   (ie_db_i     ),
      .PE   (pd_en_db_i  ),
      .PAD  (db4         )
  );
  PDDW0408CDG i_pad_db5  (
      .I    (out_db_i[5] ),
      .OEN  (~oe_db_i    ),
      .DS   (1'b1        ),
      .C    (in_db_o[5] ),
      .IE   (ie_db_i     ),
      .PE   (pd_en_db_i  ),
      .PAD  (db5         )
  );
  PDDW0408CDG i_pad_db6  (
      .I    (out_db_i[6] ),
      .OEN  (~oe_db_i    ),
      .DS   (1'b1        ),
      .C    (in_db_o[6] ),
      .IE   (ie_db_i     ),
      .PE   (pd_en_db_i  ),
      .PAD  (db6         )
  );
  PDDW0408CDG i_pad_db7  (
      .I    (out_db_i[7] ),
      .OEN  (~oe_db_i    ),
      .DS   (1'b1        ),
      .C    (in_db_o[7] ),
      .IE   (ie_db_i     ),
      .PE   (pd_en_db_i  ),
      .PAD  (db7         )
  );
  PDDW0408CDG i_pad_db8  (
      .I    (out_db_i[8] ),
      .OEN  (~oe_db_i    ),
      .DS   (1'b1        ),
      .C    (in_db_o[8] ),
      .IE   (ie_db_i     ),
      .PE   (pd_en_db_i  ),
      .PAD  (db8         )
  );
  PDDW0408CDG i_pad_db9  (
      .I    (out_db_i[9] ),
      .OEN  (~oe_db_i    ),
      .DS   (1'b1        ),
      .C    (out_db_i[9] ),
      .IE   (ie_db_i     ),
      .PE   (pd_en_db_i  ),
      .PAD  (db9         )
  );
  PDDW0408CDG i_pad_dba  (
      .I    (out_db_i[10]),
      .OEN  (~oe_db_i    ),
      .DS   (1'b1        ),
      .C    (in_db_o[10] ),
      .IE   (ie_db_i     ),
      .PE   (pd_en_db_i  ),
      .PAD  (dba         )
  );
  PDDW0408CDG i_pad_dbb  (
      .I    (out_db_i[11]),
      .OEN  (~oe_db_i    ),
      .DS   (1'b1        ),
      .C    (in_db_o[11] ),
      .IE   (ie_db_i     ),
      .PE   (pd_en_db_i  ),
      .PAD  (dbb         )
  );
  PDDW0408CDG i_pad_dbc  (
      .I    (out_db_i[12]),
      .OEN  (~oe_db_i    ),
      .DS   (1'b1        ),
      .C    (in_db_o[12] ),
      .IE   (ie_db_i     ),
      .PE   (pd_en_db_i  ),
      .PAD  (dbc         )
  );
  PDDW0408CDG i_pad_dbd  (
      .I    (out_db_i[13]),
      .OEN  (~oe_db_i    ),
      .DS   (1'b1        ),
      .C    (in_db_o[13] ),
      .IE   (ie_db_i     ),
      .PE   (pd_en_db_i  ),
      .PAD  (dbd         )
  );
  PDDW0408CDG i_pad_dbe  (
      .I    (out_db_i[14]),
      .OEN  (~oe_db_i    ),
      .DS   (1'b1        ),
      .C    (in_db_o[14] ),
      .IE   (ie_db_i     ),
      .PE   (pd_en_db_i  ),
      .PAD  (dbe         )
  );
  PDDW0408CDG i_pad_dbf  (
      .I    (out_db_i[15]),
      .OEN  (~oe_db_i    ),
      .DS   (1'b1        ),
      .C    (in_db_o[15] ),
      .IE   (ie_db_i     ),
      .PE   (pd_en_db_i  ),
      .PAD  (dbf         )
  );
endmodule
