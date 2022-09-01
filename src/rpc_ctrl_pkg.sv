// Copyright 2022 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Suyang Song <susong@student.ethz.ch>
// Bowen Wang <bowwang@student.ethz.ch>
// Chen Wang <chewang@student.ethz.ch>
// Jiawei Zhang <jiawzhang@student.ethz.ch>

// RPC Controller package
// This file is used to define all the common structs, typdef, localparam
// between RPC AXI4-compliant interface and downstream RPC phy
package rpc_ctrl_pkg;

    //RPC DRAM word: 256bits = 32byte -> log2(32) = 5
    localparam unsigned DramAlignPos  = 5;
    //bank + row + column address = 20bits wide
    localparam unsigned DramAddrWidth = 20;
    //Dram word width
    localparam unsigned DramWordWidth = 256;
    //Mast width
    localparam unsigned MaskWidth = 64;

    typedef logic[5:0]  dram_blen_t;
    typedef logic[19:0] dram_addr_t;

    ///////////////////////////////
    /////////phy interface///////// 
    ///////////////////////////////
    typedef struct packed{
        logic   w_data_valid;
        logic   r_data_ready;
        logic   [DramWordWidth-1:0]     w_data;
    } phy_req_t;


    typedef struct packed{
        logic   w_data_ready;
        logic   r_data_valid;
        logic [DramWordWidth-1:0]     r_data;
        logic   r_data_last;
    } phy_rsp_t;

    ///////////////////////////////
    //////cmd_fsm interface//////// 
    ///////////////////////////////
    typedef struct packed{
        logic   cmd_valid;
        logic   is_write;
        //dram word busrt len: total size = 256*len
        dram_blen_t  len; 
        logic [DramAddrWidth-1:0]   addr; 
    } axi_cmd_req_t;  

    typedef struct packed{
        logic  cmd_ready;
    } axi_cmd_rsp_t;


endpackage
