// Copyright 2022 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Suyang Song <susong@student.ethz.ch>
// Bowen Wang <bowwang@student.ethz.ch>

module write_mask_generator #(

	parameter  BufDepth  = 4,
	parameter  StrbWidth = 32
	) (

	// input 
	input logic  clk_i,
	input logic  rst_ni,

	// data from write channel
	input logic  w_last_i,
	input logic  w_valid_i,
	input logic  w_ready_i,

	input logic  [31:0] w_strobe_i,

	// data from cmd splitter
	input logic  is_write_i,
	input logic  cmd_valid_i,
	input logic  cmd_ready_i,
	input logic [1:0] split_req_i,
	input logic [5:0] len,

	// output mask
	output logic [63:0] w_mask_o 
	);

	typedef struct packed{
			logic[31:0] first_mask;
			logic[31:0] last_mask;
		} w_mask_t;

	//write mask fifo input and output
	w_mask_t w_mask_fifo_i, w_mask_fifo_o;

	// fifo input logic
	logic        w_first_d, w_first_q;
	logic [31:0] w_first_mask_d, w_first_mask_q;
	logic        w_handshake;

	assign w_mask_fifo_i.first_mask = ((w_first_q == 'b1) && (w_last_i == 'b1)) ? w_strobe_i : w_first_mask_q;
	assign w_mask_fifo_i.last_mask  = w_strobe_i;

	assign w_handshake = w_valid_i && w_ready_i;

	always_comb begin
		w_first_d = w_first_q;
		w_first_mask_d = w_first_mask_q;

		if (w_last_i && w_handshake) begin
			w_first_d = 'b1;
		end else if ( !w_last_i && w_handshake) begin
			w_first_d = 'b0;
		end 

		if (w_first_q && w_handshake) begin
			w_first_mask_d = w_strobe_i;
		end 
	end

	// temp mask reg
	logic w_fifo_pop, cmd_handshake;
	logic [63:0] pre_mask_d, pre_mask_q;

	assign pre_mask_d = (w_fifo_pop) ? w_mask_fifo_o : pre_mask_q;

	// temp cmd_reg_type
	logic [1:0]  temp_split_req_d, temp_split_req_q;
	assign temp_split_req_d = (cmd_handshake && is_write_i) ? split_req_i : temp_split_req_q;

	// handshake from cmd splitter
	assign cmd_handshake = cmd_ready_i  && cmd_valid_i;
	assign w_fifo_pop    = cmd_handshake && is_write_i
						   && (split_req_i == 2'b01 || split_req_i == 2'b00 );
	
	logic [5:0] len_d, len_q;
	assign len_d = (cmd_handshake) ? len : len_q;
	always_comb begin
		// len_d = len_q;
		w_mask_o = '0;
		unique case(temp_split_req_q)
			2'b00: begin 
				w_mask_o = pre_mask_q; 
			end

			2'b01: begin          	// first splitted cmd, higher 32 bits are first mask
				if (len_q == 0) begin
					w_mask_o[31:0]  = pre_mask_q[63:32];
				end else begin
					w_mask_o[31:0]  = 32'hffff_ffff;
				end
				
				w_mask_o[63:32] = pre_mask_q[63:32];
			end

			2'b10: begin			// second splitted cmd
				w_mask_o[31:0]  = pre_mask_q[31:0];
				if (len_q == 0) begin
					w_mask_o[63:32] = pre_mask_q[31:0];
				end else begin
					w_mask_o[63:32] = 32'hffff_ffff;
				end
				
			end
			default: w_mask_o = '0;
		endcase // temp_split_req_q
	end
	//write mask buffer
    stream_fifo #(
        .DATA_WIDTH ( StrbWidth * 2 ),
        .DEPTH      ( BufDepth+1  ),
        .T          ( w_mask_t   )
    ) i_mask_channel_fifo (
        .clk_i      (clk_i),
        .rst_ni     (rst_ni),
        
        //TODO: support DFT
        .flush_i    (1'b0),
        .testmode_i (1'b0),

        //slave interface port
        .data_i     (w_mask_fifo_i),
        .valid_i    (w_handshake && w_last_i),
        .ready_o    (),

        //master interface port
        .usage_o    (),
        .data_o     (w_mask_fifo_o),
        .valid_o    (),
        .ready_i    (w_fifo_pop)
    );

    always_ff @(posedge clk_i, negedge rst_ni) begin
    	if (!rst_ni) begin
    		w_first_q <= 1'b1;
    		w_first_mask_q <= '0;
    		pre_mask_q <= '0;
    		temp_split_req_q <= 2'b00;
    		len_q <= '0;
    	end else begin
    		w_first_q <= w_first_d;
    		w_first_mask_q <= w_first_mask_d;
    		pre_mask_q <= pre_mask_d;
    		temp_split_req_q <= temp_split_req_d;
    		len_q <= len_d;
		end
	end

endmodule : write_mask_generator
