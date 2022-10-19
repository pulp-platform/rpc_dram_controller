// Copyright 2022 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Suyang Song <susong@student.ethz.ch>
// Bowen Wang <bowwang@student.ethz.ch>

//read_parallelizer : module parallelizes transaction with same IDs to support outstanding
//					  read after upsizer
module axi_parallelizer #(
	parameter int unsigned ParallelNum = 4,
	parameter int unsigned AxiIdWidth  = 6,

	parameter type mst_req_t   = logic,
	parameter type mst_resp_t  = logic,
	parameter type slv_req_t   = logic,
	parameter type slv_resp_t  = logic
)(
	input  clk_i,
	input  rst_ni,

	input   slv_req_t       slv_req_i,
	output  slv_resp_t      slv_resp_o,
	output  mst_req_t       mst_req_o,
	input   mst_resp_t      mst_resp_i
);
	
	localparam int unsigned PreIdWidth = ParallelNum == 1 ? 1 : $clog2(ParallelNum);
	typedef logic[PreIdWidth-1:0] preid_t;
	//preid counter up to Parallel Num
	preid_t pre_rid_q, pre_wid_q;
	preid_t pre_rid_d, pre_wid_d;
	logic   read_handshake;
	logic   write_handshake;
	
	//ID prepend and truncate
	always_comb begin 

		mst_req_o.aw_valid   = slv_req_i.aw_valid;
		mst_req_o.w_valid    = slv_req_i.w_valid;
		mst_req_o.b_ready    = slv_req_i.b_ready;
		mst_req_o.ar_valid   = slv_req_i.ar_valid;
	    mst_req_o.r_ready    = slv_req_i.r_ready;

	    slv_resp_o.aw_ready  = mst_resp_i.aw_ready;
	    slv_resp_o.ar_ready  = mst_resp_i.ar_ready;
	    slv_resp_o.w_ready   = mst_resp_i.w_ready;
	    slv_resp_o.b_valid   = mst_resp_i.b_valid;
	    slv_resp_o.r_valid   = mst_resp_i.r_valid;

	   	mst_req_o.aw         = {pre_wid_q, slv_req_i.aw};
	   	mst_req_o.ar         = {pre_rid_q, slv_req_i.ar};
	   	mst_req_o.w          = slv_req_i.w;

	    slv_resp_o.r.id       = mst_resp_i.r.id[AxiIdWidth-1:0] ;
	   	slv_resp_o.r.data     = mst_resp_i.r.data ;
	   	slv_resp_o.r.resp     = mst_resp_i.r.resp ;
	   	slv_resp_o.r.last     = mst_resp_i.r.last ;
	   	slv_resp_o.r.user     = mst_resp_i.r.user ;

		slv_resp_o.b.id       = mst_resp_i.b.id[AxiIdWidth-1:0] ;
	   	slv_resp_o.b.resp     = mst_resp_i.b.resp ;
	   	slv_resp_o.b.user     = mst_resp_i.b.user ;

	end

	assign  read_handshake  = mst_req_o.ar_valid & mst_resp_i.ar_ready;
	assign  write_handshake = mst_req_o.aw_valid & mst_resp_i.aw_ready;
	
	always_comb begin
		pre_rid_d = pre_rid_q;
		pre_wid_d = pre_wid_q;

		if(read_handshake) begin   
			pre_rid_d = pre_rid_q + 1'b1 ;
			if(pre_rid_q == ParallelNum-1) begin 
				pre_rid_d = '0;
			end
		end 

		if(write_handshake) begin   
			pre_wid_d = pre_wid_q + 1'b1 ;
			if(pre_wid_q == ParallelNum-1) begin 
				pre_wid_d = '0;
			end
		end 
	end 

	always_ff @(posedge clk_i or negedge rst_ni) begin
		if(!rst_ni) begin 
			pre_rid_q <= '0;
			pre_wid_q <= '0;
		end else begin 
			pre_rid_q <= pre_rid_d;
			pre_wid_q <= pre_wid_d;
		end 
	end

endmodule 