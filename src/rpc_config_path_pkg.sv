// Copyright 2022 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Chen Wang <chewang@student.ethz.ch>
// Jiawei Zhang <jiawzhang@student.ethz.ch>

package rpc_config_path_pkg;

  // ---------- Register unit width --------------------------------
  localparam int unsigned REG_WIDTH = 32;

  // ---------- Reg Bus Communciation Interface --------------------------------
  localparam int unsigned ADDR_WIDTH = 8;             // Address width determined by the number of configuration registers inside
  localparam int unsigned BUS_WIDTH = REG_WIDTH;
  localparam int unsigned STROBE_WIDTH = BUS_WIDTH/8;



  // ---------- starting address of register configuration  --------------------------
  // ---------- to align with soc strcture, the address represents byte location -----
  localparam int unsigned ADDR_BYTE_BASE          = 4;
  localparam int unsigned ADDR_INIT_CFG           = 0 * ADDR_BYTE_BASE;
  localparam int unsigned ADDR_INIT_COMP          = 1 * ADDR_BYTE_BASE;
  localparam int unsigned ADDR_DIRECT_CMD         = 2 * ADDR_BYTE_BASE;
  localparam int unsigned ADDR_TIMER_STARTER      = 3 * ADDR_BYTE_BASE;
  localparam int unsigned ADDR_REF_TIMER          = 4 * ADDR_BYTE_BASE;
  localparam int unsigned ADDR_ZQC_TIMER          = 5 * ADDR_BYTE_BASE;
  localparam int unsigned ADDR_DELAY_CFG_CLK_90   = 6 * ADDR_BYTE_BASE;
  localparam int unsigned ADDR_DELAY_CFG_DQS_I    = 7 * ADDR_BYTE_BASE;
  localparam int unsigned ADDR_DELAY_CFG_DQS_NI   = 8 * ADDR_BYTE_BASE;


  localparam int unsigned ADDR_TIMING_CONFIG_START            = 9 * ADDR_BYTE_BASE;
  localparam int unsigned NUM_TIMING_CONFIG                   = 21;
  localparam int unsigned ADDR_TIMING_CONFIG_END              = ADDR_TIMING_CONFIG_START + 4*NUM_TIMING_CONFIG -1;

  // Power Up
  localparam int unsigned ADDR_OFFSET_N_PU_CLK_STABLE         = 0;
  localparam int unsigned ADDR_OFFSET_N_PU_WAIT_RST_COMP      = 1;
  localparam int unsigned ADDR_OFFSET_N_PU_STB_RESET          = 2;

  localparam int unsigned ADDR_OFFSET_N_CS_SU_HO              = 3;

  // DB Postamble
  localparam int unsigned ADDR_OFFSET_N_WPST                  = 4;

  // Precharge
  localparam int unsigned ADDR_OFFSET_N_PRE                   = 5;
  // MRS
  localparam int unsigned ADDR_OFFSET_N_MOD                   = 6;
  // ACT
  localparam int unsigned ADDR_OFFSET_N_RCD                   = 7;


  // Write Configuration
  localparam int unsigned ADDR_OFFSET_N_WR_WAIT_CL            = 8;
  localparam int unsigned ADDR_OFFSET_N_WR_ALIGN_WPST         = 9;
  localparam int unsigned ADDR_OFFSET_N_WR_BESL_AFTER_WPST    = 10;

  // Read Configuration
  localparam int unsigned ADDR_OFFSET_N_RD_WAIT_PREAMBLE      = 11;
  localparam int unsigned ADDR_OFFSET_N_RD_BESL               = 12;

  // Refresh Command Timing
  localparam int unsigned ADDR_OFFSET_N_REF_4                 = 13;
  localparam int unsigned ADDR_OFFSET_N_REF_3                 = 14;
  localparam int unsigned ADDR_OFFSET_N_REF_2                 = 15;
  localparam int unsigned ADDR_OFFSET_N_REF_1                 = 16;

  // ZQC Command Timing
  localparam int unsigned ADDR_OFFSET_N_ZQINIT                = 17;
  localparam int unsigned ADDR_OFFSET_N_ZQCL                  = 18;
  localparam int unsigned ADDR_OFFSET_N_ZQCS                  = 19;
  localparam int unsigned ADDR_OFFSET_N_ZQRESET               = 20;


  // ---------- Register bit functionality defination --------------------------
  
 
  //////////////////////////////////////////////////////
  ////////////Direct Command Register///////////////////
  //////////////////////////////////////////////////////

  localparam int unsigned CMD_TYPE_WIDTH = 2;
  localparam int unsigned CMD_FIELD = 17;
  localparam int unsigned CMD_FIFO_DEPTH = 4;

  typedef struct packed {
  logic [CMD_TYPE_WIDTH-1:0]                          cmd_type;
  logic [CMD_FIELD-1:0]                               cmd_field;
  logic [REG_WIDTH-CMD_TYPE_WIDTH-CMD_FIELD-1:0]      dont_care;
  } direct_command_reg_t;



  //////////////////////////////////////////////////////
  ////////////DRAM Initialization Register//////////////
  //////////////////////////////////////////////////////

  // Define the initialization configuration register
  typedef struct packed {
    logic [3-1:0]   odt;
    logic [4-1:0]   zout;
    logic [3-1:0]   nwr;
    logic [3-1:0]   cl;
    logic           tm;
    logic           odt_pd;
    logic           csr_fx;
    logic           stb_odt;
    logic [15-1:0]  dont_care;
  } dram_init_cfg_reg_t;

  //////////////////////////////////////////////////////
  ////////////Timer Starter Register////////////////////
  //////////////////////////////////////////////////////
  
  // Starter / Ref Timer / ZQC timer counter depth
  localparam int unsigned INTERVAL_SETTING_WIDTH = 25;


  // Define the timer_starter configuration register
  typedef struct packed {
    logic mode;
    logic [REG_WIDTH - INTERVAL_SETTING_WIDTH -2:0]   dont_care;
    logic [INTERVAL_SETTING_WIDTH-1:0]                interval;
  } timer_starter_cfg_reg_t;

  // Start default setting
  localparam timer_starter_cfg_reg_t TIMER_STARTER_DEFAULT_SETTING = '{mode: 1'b0, dont_care:'0, interval:2000};
  // Timer Internal Counter Width
  localparam int unsigned CNT_WIDTH = 32;
  // Timer Output Command Width 
  localparam int unsigned CMD_WIDTH = 19;
  localparam int unsigned DEFALUT_INIT_DELAY = 40; 


  //////////////////////////////////////////////////////
  ////////////Refresh Timer ////////////////////////////
  //////////////////////////////////////////////////////

  // Define the refresh timer configuration register bit defination
  typedef struct packed {
    logic         enable;
    logic [2-1:0] ref_refop;
    logic [4-1:0] ref_bank_list;
    logic [INTERVAL_SETTING_WIDTH -1:0] interval;
  } ref_cfg_reg_t;

  // Timer Default Setting
  localparam ref_cfg_reg_t REF_TIMER_DEFAULT_SETTING = '{enable: 1'b1, ref_refop: 2'b00, ref_bank_list:4'b1111, interval:2000};

  // Timer Internal Counter Width
  localparam REF_TIMER_CNT_WIDTH = 32;

  // Timer Output Command Width
  localparam REF_TIMER_CMD_WIDTH = 19;


  //////////////////////////////////////////////////////
  ////////////ZQC Timer Register////////////////////////
  //////////////////////////////////////////////////////

  // Define the ZQ Calibration configutation register
  typedef struct packed {
    logic         enable;
    logic [2-1:0] zqc_op;
    logic [4-1:0] dont_care;
    logic [INTERVAL_SETTING_WIDTH -1:0] interval;
  } zqc_cfg_reg_t;


  localparam zqc_cfg_reg_t ZQC_TIMER_DEFAULT_SETTING = '{enable: 1'b1, zqc_op: 2'b10, dont_care:4'b0000, interval:2000};

  // Timer Internal Counter Width
  localparam ZQC_TIMER_CNT_WIDTH = 32;

  // Timer Output Command Width
  localparam ZQC_TIMER_CMD_WIDTH = 19;


  //////////////////////////////////////////////////////
  ////////Delay Line Configuration Register/////////////
  //////////////////////////////////////////////////////
  
  // Configuration Port Width
  localparam int unsigned DELAY_CFG_WIDTH = 5;

  typedef struct packed {
    logic [REG_WIDTH - DELAY_CFG_WIDTH -1:0]                dont_care;
    logic [DELAY_CFG_WIDTH-1:0]                             delay_cfg;
  } delay_line_cfg_reg_t;

  localparam delay_line_cfg_reg_t CLK_90_DELAY_DEFAULT_SETTING = '{dont_care:'0, delay_cfg:5'd8};
  localparam delay_line_cfg_reg_t DQS_I_DELAY_DEFAULT_SETTING  = '{dont_care:'0, delay_cfg:5'd8};
  localparam delay_line_cfg_reg_t DQS_NI_DELAY_DEFAULT_SETTING = '{dont_care:'0, delay_cfg:5'd8};


  //////////////////////////////////////////////////////
  ////////Timing Configuration Register ////////////////
  //////////////////////////////////////////////////////


  typedef logic [NUM_TIMING_CONFIG-1:0][REG_WIDTH-1 :0] timing_cfg_reg_t ;

endpackage

