// Copyright 2022 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Suyang Song <susong@student.ethz.ch>
// Bowen Wang <bowwang@student.ethz.ch>

//sram_wrapper: module wrapping sram
//				to make it work as a data fifo
module sram_wrapper #(
  parameter int unsigned DramDataWidth = 256,
  parameter int unsigned SramDataWidth = DramDataWidth,
  parameter int unsigned BufferDepth   = 4,
  parameter int unsigned DramLenWidth  = 6,

  localparam int unsigned SramNumWords = BufferDepth << DramLenWidth,
  localparam int unsigned AddrWidth    = (SramNumWords > 32'd1) ? $clog2(SramNumWords) : 32'd1
) (
  input logic clk_i,
  input logic rst_ni,

  //slave handshake signal
  input  logic w_valid_i,
  output logic w_ready_o,

  //master  handshake signal
  input  logic r_ready_i,
  output logic r_valid_o,

  input  logic [DramDataWidth-1:0] w_data_i,
  output logic [DramDataWidth-1:0] r_data_o,
  output logic [AddrWidth      :0]    usage_o
);

  //assertions
`ifndef SYNTHESIS
  initial begin : wrapper_assertions
    assert (DramDataWidth % SramDataWidth == 0)
    else $warning("Parameter DramDataWidth/SramDataWidth has to be integer!");
    assert (BufferDepth > 0)
    else $warning("Parameter BufferDepth has to be greater than zero!");
  end
`endif


  localparam int unsigned SramNum = DramDataWidth / SramDataWidth;



  //generate multiple sram in parallel
  // for (genvar i = 0; i < SramNum; i++) begin: gen_sram
  // 	tc_sram #(
  // 	  .NumWords		( SramNumWords  ),
  // 	  .DataWidth 	( SramDataWidth ),
  // 	  .ByteWidth    ( SramDataWidth ),
  // 	  .NumPorts		( 32'd2    ),
  // 	  .Latency		( 1'b1     ),
  // 	  .SimInit		( "random" ),
  // 	  .PrintSimCfg	( 1'b1     ),
  // 	)i_tc_sram(

  // 	  .clk_i	(clk_i),
  // 	  .rst_ni	(rst_ni),
  // 	  .be_i, 	('1),

  // 	  //1: master taken by AXI  0: slave taken by phy
  // 	  //signals shared by multiple sram instances
  // 	  .addr_i	({mst_addr_q[AddrWidth-1:0], slv_addr_q[AddrWidth-1:0]}),
  // 	  .req_i	({mst_req 				 , slv_req }),
  // 	  .we_i		({1'b1    				 , 1'b0  }),

  // 	  //data port: master write data / slave read data
  // 	  .wdata_i	({mst_wdata[i], '0          }),
  // 	  .rdata_o  ({            , slv_rdata[i]})
  // 	);
  // end

  logic w_req, r_req;
  //write and read controller
  logic [AddrWidth:0] w_addr_q, w_addr_d;
  logic [AddrWidth:0] r_addr_q, r_addr_d;
  logic [AddrWidth:0] r_next_addr, r_curt_addr;

  logic [DramDataWidth-1:0] dummy_data_o;


`ifdef TARGET_TSMC65

  tc_sram #(
    .NumWords (SramNumWords),
    .DataWidth(DramDataWidth)
  ) i_tc_sram_neo (

    .clk_i ({clk_i, clk_i}),
    .rst_ni({rst_ni, rst_ni}),
    .be_i  ({32'hffffffff, 32'hffffffff}),

    //signals shared by multiple sram instances
    .addr_i({r_curt_addr[AddrWidth-1:0], w_addr_q[AddrWidth-1:0]}),
    .req_i ({r_req, w_req}),
    .we_i  ({1'b0, 1'b1}),
    .impl_i(1'b1),

    //data port: master write data / slave read data
    .wdata_i({256'b0, w_data_i}),
    .rdata_o({r_data_o, dummy_data_o})
  );

`else
  tc_sram #(
    .NumWords   (256),
    .DataWidth  (256),
    .ByteWidth  (256),
    .NumPorts   (32'd2),
    .Latency    (32'b1),
    .SimInit    ("random"),
    .PrintSimCfg(1'b1)
  ) i_tc_sram (

    .clk_i (clk_i),
    .rst_ni(rst_ni),
    .be_i  ({1'b1, 1'b1}),

    //signals shared by multiple sram instances
    .addr_i({r_curt_addr[AddrWidth-1:0], w_addr_q[AddrWidth-1:0]}),
    .req_i ({r_req, w_req}),
    .we_i  ({1'b0, 1'b1}),

    //data port: master write data / slave read data
    .wdata_i({256'b0, w_data_i}),
    .rdata_o({r_data_o, dummy_data_o})
  );
`endif


  //handshake signals
  logic full, empty;
  logic r_valid_q, r_valid_d;
  logic w_handshake, r_handshake;

  //fifo empty and full signal
  assign empty = (w_addr_q == r_addr_q) ? 1 : 0;
  assign full  	= (w_addr_q[AddrWidth-1:0] != r_addr_q[AddrWidth-1:0]) ? 0 :
				   	  (w_addr_q[AddrWidth]     == r_addr_q[AddrWidth]    ) ? 0 : 1;

  //usage_o: indicate how many words stored in SRAM already
  assign usage_o = w_addr_q - r_addr_q;

  //next address: for 1 latency prefetch
  assign r_next_addr = r_addr_q + 1'b1;

  //handshake signal
  assign r_handshake = r_ready_i & r_valid_o;
  assign w_handshake = w_ready_o & w_valid_i;

  assign w_ready_o = ~full;
  assign r_valid_o = r_valid_q;


  assign r_curt_addr = (!empty & !r_valid_o) ? r_addr_q : r_next_addr;

  //master address controller
  always_comb begin : w_addr_controller
    w_addr_d = w_addr_q;
    r_addr_d = r_addr_q;
    w_req    = 1'b0;
    r_req    = 1'b0;

    //if write handshake succeses, write address increments
    if (w_handshake) begin
      w_addr_d = w_addr_q + 1'b1;
      w_req    = 1'b1;
    end

    //if read handshake successes, read address increments
    if (r_handshake) begin
      r_addr_d = r_addr_q + 1'b1;
      r_req    = 1'b1;
    end

    if (!empty & !r_valid_o) begin
      r_req = 1'b1;
    end
  end


  //read data valid signal
  always_comb begin : r_data_valid
    r_valid_d = r_valid_q;

    //if next address fetches nonvalid data
    //diassert read data valid signal
    if ((r_next_addr == w_addr_q) && r_handshake) begin
      r_valid_d = 1'b0;
    end

    if (!empty & !r_valid_o) begin
      r_valid_d = 1'b1;
    end

  end

  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
      w_addr_q  <= '0;
      r_addr_q  <= '0;
      r_valid_q <= '0;
    end else begin
      w_addr_q  <= w_addr_d;
      r_addr_q  <= r_addr_d;
      r_valid_q <= r_valid_d;
    end
  end

endmodule
