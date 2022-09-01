// Copyright 2022 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Suyang Song <susong@student.ethz.ch>
// Bowen Wang <bowwang@student.ethz.ch>

//read last mask generator:
//when executing command is read and is splitted
//first last should be masked until the second one arrived
module read_mask_generator #(
    parameter type phy_rsp_t = logic
)(
    input  logic clk_i,
    input  logic rst_ni,

    //command transaction handshake signals
    input  logic cmd_valid_i,
    input  logic cmd_ready_i,

    //signals indicating attribute of executing transaction
    input  logic [1:0] split_req_i, 
    input  logic       is_write_i,

    //read data path
    input  phy_rsp_t  phy_rsp_i,
    output phy_rsp_t  phy_rsp_o
);

    logic counter_d, counter_q;

    //asserted when there is a successful read transaction
    logic read_enable;

    assign read_enable = cmd_valid_i && cmd_ready_i 
                         && ~is_write_i ;
    
    //passthrough handsahke signals from input to output
    assign phy_rsp_o.w_data_ready = phy_rsp_i.w_data_ready;
    assign phy_rsp_o.r_data_valid = phy_rsp_i.r_data_valid;
    assign phy_rsp_o.r_data       = phy_rsp_i.r_data;


    always_comb begin 
        counter_d = counter_q;
        if(read_enable) begin
            // if current transaction is first page
            // should not return last to this transaction
            if(split_req_i == 2'b01) begin
                counter_d = 1'b1;
            end else begin 
                counter_d = 1'b0;
            end 
        end 
    end 

    always_comb begin 
        phy_rsp_o.r_data_last = phy_rsp_i.r_data_last;
        if (counter_q == 1) begin 
            phy_rsp_o.r_data_last = 1'b0;
        end else begin 
            phy_rsp_o.r_data_last = phy_rsp_i.r_data_last;
        end
    end 

    always_ff @(posedge clk_i, negedge rst_ni) begin
        if(!rst_ni) begin
            counter_q <= 0;
        end else begin 
            counter_q <= counter_d;
        end
    end 

endmodule



