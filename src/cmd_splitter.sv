// Copyright 2022 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Suyang Song <susong@student.ethz.ch>
// Bowen Wang <bowwang@student.ethz.ch>

//TODO: Could realize pipeline handshake structure which would reduce a cycle
//command splitter: AXI4 specifies command should not cross 4KB boundary,
//                  while downstream DRAM only support 2KB boundary access
//                  thus need a module to convert command crossing 4KB to 2KB
module cmd_splitter #(
  parameter DramAddrWidth = 20,
  parameter DramLenWidth  = 6,

  parameter type cmd_req_t = logic,
  parameter type cmd_rsp_t = logic
) (
  input  clk_i,
  input  rst_ni,
  //master interface
  output cmd_req_t    cmd_req_o,
  input  cmd_rsp_t    cmd_rsp_i,
  //slave interface
  input  cmd_req_t    cmd_req_i,
  output cmd_rsp_t    cmd_rsp_o,
  //split request 00: non_splitted
  //01: first splitted beat 10:second splitted beat
  output logic [1:0]  split_req_o

);

  //define 4 states finit state machine
  typedef enum logic [1:0] {
    IDLE,
    FIRST_PAGE,
    SECOND_PAGE,
    SINGLE_PAGE
  } state_t;


  state_t state_d, state_q;
  cmd_req_t cmd_req_d, cmd_req_q;

  logic cmd_i_valid, cmd_o_ready;
  logic cmd_o_valid, cmd_i_ready;
  logic handshake_i, handshake_o;
  logic is_crs_boundary;
  logic [DramAddrWidth-1:0] addr_splitted;
  logic [DramLenWidth-1:0] len_splitted;

  assign cmd_i_valid     = cmd_req_i.cmd_valid;
  assign cmd_i_ready     = cmd_rsp_i.cmd_ready;

  //tell if active transaction crosses 2KB boundary
  //i.e. if address + len will cause #12 change
  //when it comes to word address, meaning #(12-5) in address invariant
  assign is_crs_boundary = 7'(cmd_req_i.addr + cmd_req_i.len) >> 6 ^ 7'(cmd_req_i.addr) >> 6;


  //input  interface handshake assign
  assign handshake_i     = cmd_i_valid && cmd_o_ready;
  //output interface handshake assign
  assign handshake_o     = cmd_o_valid && cmd_i_ready;

  //finite state machine combinational logic
  //control if active command cross 2KB boundary
  //navigate it into two seperate branches:
  //SINGLE PAGE: just transfer one page command
  //FIRST and SECOND PAGE: divide one command into seperate two

  always_comb begin
    state_d       = state_q;
    cmd_req_d     = cmd_req_q;
    cmd_o_valid   = 1'b0;
    cmd_o_ready   = 1'b0;
    addr_splitted = '0;
    len_splitted  = '0;
    split_req_o   = '0;
    unique case (state_q)
      //IDLE: default state has no valid command to downstream
      //upon input interface handshake, switch to either FIRST_PAGE
      //or SINGLE_PAGE state and store current command
      IDLE: begin
        cmd_o_valid = 1'b0;
        cmd_o_ready = 1'b1;
        split_req_o = 2'b0;
        if (handshake_i) begin
          //if successfully handshake, store cmd in register
          cmd_req_d = cmd_req_i;
          if (is_crs_boundary) state_d = FIRST_PAGE;
          else state_d = SINGLE_PAGE;
        end
      end

      FIRST_PAGE: begin
        cmd_o_valid   = 1'b1;
        cmd_o_ready   = 1'b0;
        split_req_o   = 2'b01;
        //pass through address for the first page
        addr_splitted = cmd_req_q.addr;
        //2KB boudnary - starting address = burst length
        len_splitted  = 6'b111111 - 6'(cmd_req_q.addr);
        if (handshake_o) begin
          state_d = SECOND_PAGE;

          //debug information
          // `ifndef SYNTHESIS
          // $display("addr:%h | len: %d -> firstpage: addr:%h | len:%d",
          //       cmd_req_q.addr,cmd_req_q.len,addr_splitted,len_splitted);
          // `endif
        end

      end

      SECOND_PAGE: begin
        cmd_o_valid   = 1'b1;
        cmd_o_ready   = cmd_i_ready;
        split_req_o   = 2'b10;
        //pass aligned address + 7'b1_000000 to second address
        addr_splitted = (cmd_req_q.addr + 7'b1_000000) >> 6 << 6;
        //2KB boudnary - starting address = burst length
        len_splitted  = cmd_req_q.len + 6'(cmd_req_q.addr) - 6'b111111 - 1;
        if (handshake_o) begin
          state_d = IDLE;
          //pipeline handshake: if input handshake at the same time
          if (handshake_i) begin
            cmd_req_d = cmd_req_i;
            if (is_crs_boundary) state_d = FIRST_PAGE;
            else state_d = SINGLE_PAGE;
          end

          //debug information
          // `ifndef SYNTHESIS
          //     $display("addr:%h | len: %d -> secondpage: addr:%h | len:%d",
          //           cmd_req_q.addr,cmd_req_q.len,addr_splitted,len_splitted);
          // `endif
        end

      end

      SINGLE_PAGE: begin
        cmd_o_valid   = 1'b1;
        cmd_o_ready   = cmd_i_ready;
        split_req_o   = 2'b00;
        //directly pass addr and len to downstream
        addr_splitted = cmd_req_q.addr;
        len_splitted  = cmd_req_q.len;

        //pipeline handshake: if input handshake at the same time
        if (handshake_o) begin
          state_d = IDLE;
          if (handshake_i) begin
            cmd_req_d = cmd_req_i;
            if (is_crs_boundary) state_d = FIRST_PAGE;
            else state_d = SINGLE_PAGE;
          end
        end

        //debug information
        // `ifndef SYNTHESIS
        //     $display("addr:%h | len: %d -> singlepage: addr:%h | len:%d",
        //           cmd_req_q.addr,cmd_req_q.len,addr_splitted,len_splitted);
        // `endif

      end
    endcase
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin

    if (~rst_ni) begin
      state_q   <= IDLE;
      cmd_req_q <= '0;
    end else begin
      state_q   <= state_d;
      cmd_req_q <= cmd_req_d;
    end
  end


  //assign output signals to interface
  assign cmd_rsp_o.cmd_ready = cmd_o_ready;
  assign cmd_req_o.is_write  = cmd_req_q.is_write;
  assign cmd_req_o.cmd_valid = cmd_o_valid;
  assign cmd_req_o.len       = len_splitted;
  assign cmd_req_o.addr      = addr_splitted;

endmodule
