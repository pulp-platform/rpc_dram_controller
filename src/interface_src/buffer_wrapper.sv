// Copyright 2022 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Suyang Song <susong@student.ethz.ch>
// Bowen Wang <bowwang@student.ethz.ch>

//buffer wrapper: wrap response buffer and request buffer
//				  interact with previous axi4 stage
//				  interact with follow-up phy and command finite state machine stage
module buffer_wrapper#(
	
	parameter int unsigned DramAddrWidth = 20,
	parameter int unsigned DramLenWidth  = 6,
	parameter int unsigned DramDataWidth = 256,

	parameter int unsigned BufferDepth   = 4,
	parameter int unsigned AxiAddrWidth  = 48,
	parameter int unsigned AxiLenWidth   = 8,

	parameter int unsigned AXI_ID_WIDTH  = 6,
	parameter int unsigned AXI_USER_WIDTH= 1,
	
	//previous axi interface data type
	parameter type axi_req_t  = logic,
	parameter type axi_rsp_t  = logic,

	//follow-up phy request and response signal
	parameter type phy_req_t  = logic,
	parameter type phy_rsp_t  = logic,
	//follow-up cmd_fsm interface
	parameter type cmd_req_t  = logic,
	parameter type cmd_rsp_t  = logic
)(

	input clk_i,
	input rst_ni,

	/////////////////////////////////
    /////axi4 interface wrapper slave
    /////////////////////////////////
    input  axi_req_t 	axi_req_i,
    output axi_rsp_t 	axi_rsp_o,

    /////////////////////////////////
    ////phy and fsm interface ///////
    /////////////////////////////////
    output  phy_req_t	phy_req_o,
    input   phy_rsp_t   phy_rsp_i,

    output  cmd_req_t   cmd_req_o,
    input   cmd_rsp_t	cmd_rsp_i
);
	
	
	//signal indicates arbiter output is write command
	//burst length of dram and 
	logic trx_is_write;
	logic trx_valid;
	logic trx_ready;
	logic [DramLenWidth-1:0] trx_len;


	//response ready generated by R and B Channel
	logic buf_resp_ready;
	logic cmd_valid, cmd_ready;

	assign cmd_req_o.is_write  = trx_is_write;
	assign cmd_req_o.len  	   = trx_len;
	assign cmd_valid 		   = trx_valid && buf_resp_ready;
	assign cmd_req_o.cmd_valid = cmd_valid;
	assign cmd_ready 		   = cmd_rsp_i.cmd_ready;
	assign trx_ready 		   = cmd_ready;

	//Unsupport AXI response signals assign
	//assign axi_rsp_o.r.id 	   = '0;
	assign axi_rsp_o.r.user    = 0;
	assign axi_rsp_o.r.resp    = axi_pkg::RESP_OKAY;

	buffer_req #(
		.DramAddrWidth(DramAddrWidth),
		.DramLenWidth (DramLenWidth),
		.DramDataWidth(DramDataWidth),
		.BufferDepth  (BufferDepth),
		
		.AxiAddrWidth (AxiAddrWidth),
		.AxiLenWidth  (AxiLenWidth)
	) i_buffer_req (
		.clk_i      (clk_i),
		.rst_ni 	(rst_ni),

		//write buffer signals
		.aw_addr_i 		(axi_req_i.aw.addr),
		.aw_len_i 		(axi_req_i.aw.len),
		.aw_axi_valid_i (axi_req_i.aw_valid),
		.aw_axi_ready_o (axi_rsp_o.aw_ready),

		//read buffer signals
		.ar_addr_i  	(axi_req_i.ar.addr),
		.ar_len_i   	(axi_req_i.ar.len),
		.ar_axi_valid_i (axi_req_i.ar_valid),
		.ar_axi_ready_o (axi_rsp_o.ar_ready),

		//write data signals
		.w_data_i      (axi_req_i.w.data),
		// .w_strobe_i    (axi_req_i.w.strb),
		.w_data_o      (phy_req_o.w_data),
		// .w_strobe_o	   (phy_req_o.w_strb),

		.w_axi_valid_i (axi_req_i.w_valid),
		.w_axi_ready_o (axi_rsp_o.w_ready),
		.w_buf_valid_o (phy_req_o.w_data_valid),
		.w_buf_ready_i (phy_rsp_i.w_data_ready),

		//transaction output
		.trx_valid_o   (trx_valid),
		.trx_ready_i   (trx_ready),
		.trx_is_write_o(trx_is_write),
		.trx_addr_o    (cmd_req_o.addr),
		.trx_len_o     (trx_len)
	);

	buffer_resp #(
		.DramDataWidth (DramDataWidth),
		.DramLenWidth  (DramLenWidth),

		.BufferDepth   (BufferDepth),
		.AXI_ID_WIDTH  (AXI_ID_WIDTH),
		.AXI_USER_WIDTH(AXI_USER_WIDTH)
	) i_buffer_resp (
		.clk_i 		(clk_i),
		.rst_ni     (rst_ni),

		//signals come from request arbiter
		.trx_is_write_i  (trx_is_write),
		.trx_len_i		 (trx_len),
		.buf_resp_ready_o(buf_resp_ready),

		//signals in B channel
		.b_user_o        (axi_rsp_o.b.user),
		.b_id_o          (axi_rsp_o.b.id),
		.b_resp_o        (axi_rsp_o.b.resp),
		.b_axi_ready_i	 (axi_req_i.b_ready),
		.b_axi_valid_o	 (axi_rsp_o.b_valid),

		//signals come from command finite state machine handshake
		.cmd_valid_i	 (cmd_valid),
		.cmd_ready_i     (cmd_ready),

		//signals in R channel
		.r_axi_data_o    (axi_rsp_o.r.data),
		.r_axi_last_o    (axi_rsp_o.r.last),
		.r_axi_id_o      (axi_rsp_o.r.id),
		.r_axi_valid_o   (axi_rsp_o.r_valid),
		.r_axi_ready_i   (axi_req_i.r_ready),
		
		.r_phy_data_i    (phy_rsp_i.r_data),
		.r_phy_last_i    (phy_rsp_i.r_data_last),
		.r_buf_valid_i   (phy_rsp_i.r_data_valid),
		.r_buf_ready_o   (phy_req_o.r_data_ready)
	);




endmodule