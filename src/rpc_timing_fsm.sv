// Copyright 2022 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Vaibhav Krishna <vakrishna@student.ethz.ch>
// Rui Zhou <ruzhou@student.ethz.ch>
// Chen Jinfan <jinfchen@student.ethz.ch>
// Chen Wang <chewang@student.ethz.ch>
// Jiawei Zhang <jiawzhang@student.ethz.ch>

module rpc_timing_fsm #(
  parameter int DRAM_CMD_WIDTH = 32,
  parameter int CLOCK_PERIOD   = 5    // Maximum Clock is 5ns i.e. 200MHz
) (

  // --------- Clk and RST Signal---------
  input  logic                        clk_i,
  input  logic                        rst_ni,


  // --------- Input Configuration --------

  input rpc_config_path_pkg::timing_cfg_reg_t   phy_timing_cfg_i,

  // --------- cmd_fsm -> Phy_timing_fsm Handshaking Interface ---------
  // Use to receive DRAM access command e.g. READ/WRITE/  REQ/ZQC etc.
  input  logic                        cmd_valid_i,
  output logic                        cmd_ready_o,
  input  logic  [DRAM_CMD_WIDTH-1:0]  cmd_i,

  // ---------Phy_timing_fsm -> DMA Interface------------
  // Use to receive the DATA from upstream DMA

  // Write Mode Signal
  output logic                        data_ready_o,    // Indicate PHY can acceppt new data

  // Read Mode Signal
  output logic                        data_valid_o,    // Indicate new has been pushed into the PHY from DRAM
  output logic                        data_last_o,     // Inficate the last


  // --------- Phy_timing_fsm -> PHY Interface ------------
  // The DRAM PHY receive a WORD from DMA, then based on the following signal it chop and send the data in sequence to the DRAM via DB[15:0] bus

  output logic                        mask_sel_o,       // Select whether the first word mask or the last word mask should be downloaded into the dram
  output logic   [2:0]                data_sel_o,       // Select the 32bit data from a WORD, which will be transmitted in a rising CLK edge and a rising CLK edge (DDR)
  output logic   [1:0]                type_sel_o,       // Select wether data or command or mask should be output to the DRAM via DB[15:0] bus

  // Cross Domain FIFO Signal used to receive data from DRAM in Read Mode
  input  logic                        cdc_dst_valid_i,
  output logic                        cdc_src_valid_o,
  output logic   [2:0]                data_sel_rd,      // Used to select received data


  // ------ PHY -> DRAM CLK Interface -----------
  output logic                        cs_no,                // Chip Select Port to the RPC DRAM
  output logic                        stb_o,                // Serical Command Port to the RPC DRAM

  output logic                        dqs_cg_en_o,          // Clock Gating Enable of DQS Signal
  output logic                        dqs_pair_oe_o,        // DQS/DQSn IO PAD output enable active high signal
  output logic                        dqs_pair_ie_o,        // DQS/DQSn IO PAD input enable active high signal
  output logic                        dqs_pair_pd_en_o,     // Pull Down Enable for DQS/DQSn signal

  output logic                        db_oe_o,              // DB Bus PAD output enabling
  output logic                        db_ie_o,              // Input Enable for DB signal
  output logic                        db_pd_en_o            // Pull Down Enable for DB signal

);
  // define the states for this state machine
  typedef enum logic [7:0] {
    IDLE,

    EN_CS_WAIT_NEW_CMD,

    // -------------States for power-up initlization------------------------
    PU_WAIT_BEFORE_INIT,
    PU_STB_RESET,
    PU_DIS_STB,
    PU_WAIT_RST_COMPLETE,

    // -------------States for one-shot command-----------------------------
    CMD_EN_CS,
    CMD_ALIGN_TPPD,
    CMD_EN_STB,
    CMD_EN_DQS,
    CMD_SEND_DB,
    CMD_ALIGN_WPST,

    //-------------states for refresh command-------------
    REF_WAIT_COMPLETE,
    REF_HOLD_CS,

    //-------------Write Mode related state-------------
    WR_WAIT_CL,
    WR_EN_DQS,
    WR_MASK,
    WR_DATA,
    WR_ALIGN_WPST,

    //-------------Read Mode related state-------------
    RD_WAIT_PREAMBLE,
    RD_PAD_EN,
    RD_WAIT,
    RD_DATA
  } state;


  ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  ///////////////////////////////////////////////////////Configuration Decoder //////////////////////////////////////////////////////////////////////////////
  ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  logic [31:0] n_cs_su_ho;
  assign n_cs_su_ho = phy_timing_cfg_i[rpc_config_path_pkg::ADDR_OFFSET_N_CS_SU_HO];


  // -------------------------------Power up initlization timing config-------------------------------
  logic [31:0] n_pu_clock_stable, n_pu_wait_rst_comp, n_pu_stb_reset;
  assign n_pu_clock_stable = phy_timing_cfg_i[rpc_config_path_pkg::ADDR_OFFSET_N_PU_CLK_STABLE];
  assign n_pu_wait_rst_comp = phy_timing_cfg_i[rpc_config_path_pkg::ADDR_OFFSET_N_PU_WAIT_RST_COMP];
  assign n_pu_stb_reset = phy_timing_cfg_i[rpc_config_path_pkg::ADDR_OFFSET_N_PU_STB_RESET];

  // -------------------------------DB Postamble-------------------------------
  logic [31:0] n_wpst;
  assign n_wpst = phy_timing_cfg_i[rpc_config_path_pkg::ADDR_OFFSET_N_WPST];

  // -------------------------------Pre Charge------------------------
  logic [31:0] n_pre;
  assign n_pre = phy_timing_cfg_i[rpc_config_path_pkg::ADDR_OFFSET_N_PRE];

  // -------------------------------MRS-------------------------------
  logic [31:0] n_mod;
  assign n_mod = phy_timing_cfg_i[rpc_config_path_pkg::ADDR_OFFSET_N_MOD];

  // -------------------------------ACT-------------------------------
  logic [31:0] n_rcd;
  assign n_rcd = phy_timing_cfg_i[rpc_config_path_pkg::ADDR_OFFSET_N_RCD];


  // -------------------------------WR Timing Control-------------------------------
  logic [31:0] n_wr_wait_cl;
  assign n_wr_wait_cl = phy_timing_cfg_i[rpc_config_path_pkg::ADDR_OFFSET_N_WR_WAIT_CL];

  logic [31:0] n_align_wr_wpst;
  assign n_align_wr_wpst = phy_timing_cfg_i[rpc_config_path_pkg::ADDR_OFFSET_N_WR_ALIGN_WPST];

  logic [31:0] n_wr_besl_after_wpst;
  assign n_wr_besl_after_wpst = phy_timing_cfg_i[rpc_config_path_pkg::ADDR_OFFSET_N_WR_BESL_AFTER_WPST];


  // -------------------------------RD Timing Control-------------------------------
  logic [31:0] n_rd_wait_preamble;
  assign n_rd_wait_preamble = phy_timing_cfg_i[rpc_config_path_pkg::ADDR_OFFSET_N_RD_WAIT_PREAMBLE];

  logic [31:0] n_rd_besl;
  assign n_rd_besl = phy_timing_cfg_i[rpc_config_path_pkg::ADDR_OFFSET_N_RD_BESL];


  // -------------------------------Ref-------------------------------
  logic [31:0] n_ref_4, n_ref_3, n_ref_2, n_ref_1;
  assign n_ref_4 = phy_timing_cfg_i[rpc_config_path_pkg::ADDR_OFFSET_N_REF_4];
  assign n_ref_3 = phy_timing_cfg_i[rpc_config_path_pkg::ADDR_OFFSET_N_REF_3];
  assign n_ref_2 = phy_timing_cfg_i[rpc_config_path_pkg::ADDR_OFFSET_N_REF_2];
  assign n_ref_1 = phy_timing_cfg_i[rpc_config_path_pkg::ADDR_OFFSET_N_REF_1];


  // -------------------------------ZQC-------------------------------
  logic [31:0] n_zqinit, n_zqcl, n_zqcs, n_zqreset;
  assign n_zqinit  = phy_timing_cfg_i[rpc_config_path_pkg::ADDR_OFFSET_N_ZQINIT];
  assign n_zqcl    = phy_timing_cfg_i[rpc_config_path_pkg::ADDR_OFFSET_N_ZQCL];
  assign n_zqcs    = phy_timing_cfg_i[rpc_config_path_pkg::ADDR_OFFSET_N_ZQCS];
  assign n_zqreset = phy_timing_cfg_i[rpc_config_path_pkg::ADDR_OFFSET_N_ZQRESET];



  ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  ///////////////////////////////////////////////////////Command Decoder ////////////////////////////////////////////////////////////////////////////////////
  ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


  logic [3:0] cmd_decoded;
  logic [5:0] burst_length;
  logic [1:0] zqc_mode;
  logic [3:0] ref_bank_num;



  rpc_cmd_decoder #(
    .DRAM_CMD_WIDTH(32)
  ) i_cmd_decoder (
    .cmd_i         (cmd_i),
    .cmd_decoded_o (cmd_decoded),
    .burst_length_o(burst_length),
    .zqc_mode_o    (zqc_mode),
    .ref_bank_num_o(ref_bank_num)
  );


  ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  ///////////////////////////////////////////////////////Timing FSM//////////////////////////////////////////////////////////////////////////////////////////
  ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////




  state state_q, state_d;

  logic [31:0] cnt_q, cnt_d;  // logically, 256 cycle to remain in the same state at maximum
  logic [2 : 0] tPPD_cnt_q, tPPD_cnt_d;

  ///////////
  // Logic //
  ///////////
  always_comb begin
    // ----------- Upstream control ---------------

    //Output command mux
    type_sel_o       = 2'b00;
    mask_sel_o       = 1'b0;
    data_sel_o       = 3'b000;



    //Read mode CDC Enabling
    cdc_src_valid_o  = 1'b0;
    //Read mode hand shaking
    data_ready_o     = 1'b0;
    //Read mode data de-mux
    data_sel_rd      = 3'b111;


    // Write mode hand shaking
    data_valid_o     = 1'b0;
    data_last_o      = 1'b0;

    //----------- Downstream control signal given to IO PAD ---------------
    //CSn and STB directly connects to RPC DRAM
    cs_no            = 1'b1;
    stb_o            = 1'b1;

    //Data Bus IO PAD control
    db_oe_o          = 1'b0;
    db_ie_o          = 1'b0;
    db_pd_en_o       = 1'b0;

    //DQS bus IO PAD control
    dqs_cg_en_o      = 1'b0;
    dqs_pair_ie_o    = 1'b0;
    dqs_pair_oe_o    = 1'b0;
    dqs_pair_pd_en_o = 1'b0;

    // The default state for all the controlling signals are "disbaled";
    cmd_ready_o      = 1'b0;
    dqs_cg_en_o      = 1'b0;

    // ----------- FSM supporting counters and states -----------
    state_d          = state_q;
    cnt_d            = cnt_q;
    tPPD_cnt_d       = tPPD_cnt_q + 1;


    case (state_q)
      // ready if in idle state, wait for a valid DRAM control command
      IDLE: begin
        // In ideal state, the FSM is ready to pick up new command, other signals are in "disabled" state
        cmd_ready_o           = 1'b1;    // assert cmd_ready_o to high to accept new command from upstream command arbiter

        cs_no = 1'b1;
        stb_o = 1'b1;

        dqs_cg_en_o = 1'b0;
        dqs_pair_ie_o = 1'b0;
        dqs_pair_oe_o = 1'b0;

        db_oe_o = 1'b0;
        db_ie_o = 1'b0;

        // In the IDLE state, the timing FSM module will listen to the upstream to pick up any valid new command
        // If the command is a Power Up initialization, then it wll jump to the PU_WAIT_BEFORE_INIT State
        // If the command is a normal DRAM operation command, it will jump to CMD_EN_CS to pull-down the CS#
        if (cmd_valid_i) begin
          // If receives reset command, jump to the initlization sequnece
          if (cmd_decoded == rpc_cmd_pkg::CMD_RESET) begin
            state_d = PU_WAIT_BEFORE_INIT;
            cnt_d   = n_pu_clock_stable - 1;
          end else begin
            state_d = CMD_EN_CS;
            cnt_d   = n_cs_su_ho - 1;
          end
        end else begin
          state_d = IDLE;
        end
      end


      ////////////////////////////////////////////////////////////////////////////////////////////////////////////////
      ///////////////////////// Power Up Sequnece Related State //////////////////////////////////////////////////////
      ////////////////////////////////////////////////////////////////////////////////////////////////////////////////
      // At the beginning of power-up sequence, both the CLK and STB should stay high for a 200us, before it can pull any signal down to reset the DRAM
      // This timing can be found at "Power-Up Initialization Sequence" of RPC DRAM Datasheet
      // After finishing this waiting time, the PHY should follow the regular command sending sequence
      PU_WAIT_BEFORE_INIT: begin
        cmd_ready_o   = 1'b0;
        cs_no         = 1'b1;
        stb_o         = 1'b1;

        dqs_cg_en_o   = 1'b0;
        dqs_pair_ie_o = 1'b0;
        dqs_pair_oe_o = 1'b0;

        db_oe_o       = 1'b0;
        db_ie_o       = 1'b0;

        //Let the FSM to be in CMD_EN_CS state for 2 cycles to pull down the CS# for 2 CLK
        if (cnt_q == 0) begin
          state_d = CMD_EN_CS;
          cnt_d   = n_cs_su_ho - 1;
        end else begin
          state_d = PU_WAIT_BEFORE_INIT;
          cnt_d   = cnt_q - 1;
        end
      end


      // In the power up reset state, the parallel reset commmand has been send out
      // At the same time the timing_fsm need to pull the STB low to send all two consecutive 8-cycles serial reset (see RPC DRAM Datasheet Figure 4-1 Power-Up Initialization Sequence)
      // Once completed, the timing_fsm will jump to the PU_DIS_STB state to disable (pull high) STB signal

      PU_STB_RESET: begin
        cmd_ready_o   = 1'b0;

        cs_no         = 1'b0;
        stb_o         = 1'b0;

        dqs_cg_en_o   = 1'b0;
        dqs_pair_oe_o = 1'b0;
        dqs_pair_ie_o = 1'b0;

        db_oe_o       = 1'b0;
        db_ie_o       = 1'b0;

        if (cnt_q == 0) begin
          cnt_d   = n_cs_su_ho - 1;
          state_d = PU_DIS_STB;
        end else begin
          state_d = PU_STB_RESET;
          cnt_d   = cnt_q - 1;
        end
      end


      //After Sending two 8 cycle serial reset command, the FSM runs into this mode to reset the STB to high state
      PU_DIS_STB: begin
        cmd_ready_o   = 1'b0;

        cs_no         = 1'b0;  // CS Enabled
        stb_o         = 1'b1;

        dqs_cg_en_o   = 1'b0;  // DQS Clock Gating Disabled
        dqs_pair_oe_o = 1'b0;  // DQS Output Enabled
        dqs_pair_ie_o = 1'b0;

        db_oe_o       = 1'b0;
        db_ie_o       = 1'b0;
        if (cnt_q == '0) begin
          // If the input command is Reset, then jump to the PU_WAIT_RST_COMPLETE state to wait until reset complete, tRESET = 5us
          if (cmd_decoded == rpc_cmd_pkg::CMD_RESET) begin
            state_d = PU_WAIT_RST_COMPLETE;
            // Because it already takes 16 cycles for reset and 3 cycle for disabling STB
            cnt_d   = n_pu_wait_rst_comp - 1;
            // If the input command is not a valid one, return to the IDLE state
          end else begin
            state_d = IDLE;
          end
        end else begin
          state_d = PU_DIS_STB;
          cnt_d   = cnt_q - 1;
        end
      end

      // If the input command is Reset, then jump to the PU_WAIT_RST_COMPLETE state to wait until reset complete, tRESET = 5us
      PU_WAIT_RST_COMPLETE: begin
        cmd_ready_o   = 1'b0;

        cs_no         = 1'b1;
        stb_o         = 1'b1;

        dqs_cg_en_o   = 1'b0;
        dqs_pair_oe_o = 1'b0;
        dqs_pair_ie_o = 1'b0;

        db_oe_o       = 1'b0;
        db_ie_o       = 1'b0;

        if (cnt_q == 0) begin
          state_d = IDLE;
        end else begin
          cnt_d   = cnt_q - 1;
          state_d = PU_WAIT_RST_COMPLETE;
        end
      end


      ////////////////////////////////////////////////////////////////////////////////////////////////////////////////
      ///////////////////////// Normal Comand Transimission State  ///////////////////////////////////////////////////
      ////////////////////////////////////////////////////////////////////////////////////////////////////////////////
      //This state pull the CS# pin to 0 to enable the chip select for DRAM IO buffer
      //It will stay for 2 CLK i.e. pull the CS# down for 2 CLK before generating other signal pattern
      //Then it will hold in the CMD_ALIGN_TPPD state to ensure that there is 8 CLK interval between two consecutive command
      CMD_EN_CS: begin
        cmd_ready_o   = 1'b0;

        cs_no         = 1'b0;  // CS Enabled
        stb_o         = 1'b1;

        dqs_cg_en_o   = 1'b0;
        dqs_pair_oe_o = 1'b0;
        dqs_pair_ie_o = 1'b0;

        db_oe_o       = 1'b0;
        db_ie_o       = 1'b0;

        if (cnt_q == 0) begin
          state_d = CMD_ALIGN_TPPD;
        end else begin
          cnt_d   = cnt_q - 1;
          state_d = CMD_EN_CS;
        end
      end


      //In this state, this fsm will determine how many cycles should it wait until Refresh completes
      //It will then jump to REF_WAIT_COMPLETE state to wait for Refresh completes
      REF_HOLD_CS: begin
        cmd_ready_o   = 1'b0;

        cs_no         = 1'b0;  // CS Enabled
        stb_o         = 1'b1;

        dqs_cg_en_o   = 1'b0;
        dqs_pair_oe_o = 1'b0;
        dqs_pair_ie_o = 1'b0;

        db_oe_o       = 1'b0;
        db_ie_o       = 1'b0;

        // Based on the to-be-refreshed bank list, determine the number of waiting CLK cycles
        case (ref_bank_num)
          3'b001:  cnt_d = n_ref_1;
          3'b010:  cnt_d = n_ref_2;
          3'b011:  cnt_d = n_ref_3;
          3'b100:  cnt_d = n_ref_4;
          default: cnt_d = n_ref_4;
        endcase

        // Go to the disable state to wait for DRAM Refresh completion
        state_d = REF_WAIT_COMPLETE;
      end

      //Wait until the refresh has completed, the jump to the EN_CS_WAIT_NEW_CMD state to wait new valid command
      REF_WAIT_COMPLETE: begin
        cmd_ready_o   = 1'b0;

        cs_no         = 1'b1;  // CS Enabled
        stb_o         = 1'b1;

        dqs_cg_en_o   = 1'b0;
        dqs_pair_oe_o = 1'b0;
        dqs_pair_ie_o = 1'b0;

        db_oe_o       = 1'b0;
        db_ie_o       = 1'b0;

        if (cnt_q == 0) begin
          state_d = EN_CS_WAIT_NEW_CMD;
        end else begin
          cnt_d   = cnt_q - 1;
          state_d = REF_WAIT_COMPLETE;
        end
      end


      // The timing fsm enters this state when a one-shot dram command e.g. ACT/PRE/MRS/ZQC has been send out
      // it will wait for the previous command to be completed based on the required waiting time
      // then coming to the CMD_ALIGN_TPPD to synchonize new input command with 8n CLK period
      EN_CS_WAIT_NEW_CMD: begin
        cmd_ready_o      = 1'b0;

        cs_no            = 1'b0;  // CS Enabled
        stb_o            = 1'b1;

        dqs_cg_en_o      = 1'b0;
        dqs_pair_oe_o    = 1'b0;
        dqs_pair_ie_o    = 1'b0;
        dqs_pair_pd_en_o = 1'b0;

        db_oe_o          = 1'b0;
        db_ie_o          = 1'b0;
        db_pd_en_o       = 1'b0;


        if (cnt_q == 0) begin
          cmd_ready_o = 1'b1;
          if (cmd_valid_i) begin
            state_d = CMD_ALIGN_TPPD;
          end else begin
            state_d = EN_CS_WAIT_NEW_CMD;
          end
        end else begin
          state_d = EN_CS_WAIT_NEW_CMD;
          cnt_d   = cnt_q - 1;
        end

      end

      //This state is used to synchornize all the commands so consecutive one has 8 CLK delay
      //tPPD_CNT_q ca is a 3 bit auto-incrementing counter, which can be considered as a 1/8 CLK divier
      //This state will ensure that the parallel command sending align with the "0" value of this counter
      CMD_ALIGN_TPPD: begin
        cmd_ready_o   = 1'b0;

        cs_no         = 1'b0;  // CS Enabled
        stb_o         = 1'b1;

        dqs_cg_en_o   = 1'b0;
        dqs_pair_oe_o = 1'b0;
        dqs_pair_ie_o = 1'b0;

        db_oe_o       = 1'b0;
        db_ie_o       = 1'b0;

        if (tPPD_cnt_q == '0) begin
          state_d = CMD_EN_STB;
        end else begin
          state_d = CMD_ALIGN_TPPD;
        end
      end

      //This state is used to enable (pull down) both the STB and CS# signal
      //It is used to meet the 1-item of the following Parallel Command Timing Requirement:
      //  1: the STB should be pull down for 2 CLK before sending command on DB bus
      //  2: (handled by CMD_EN_DQS) a DQS preamble should be issued at least 1 CLK before sending command on DB bus
      CMD_EN_STB: begin
        cmd_ready_o   = 1'b0;

        cs_no         = 1'b0;  // CS Enabled
        stb_o         = 1'b0;

        dqs_cg_en_o   = 1'b0;
        dqs_pair_oe_o = 1'b0;
        dqs_pair_ie_o = 1'b0;

        db_oe_o       = 1'b0;
        db_ie_o       = 1'b0;

        state_d       = CMD_EN_DQS;
      end


      //This state is used to enable the clock gating of DQS signal while keeping the STB and CS# signal low
      //It is used to meet the 2-item of the following Parallel Command Timing Requirement:
      //  1: (handled by CMD_EN_STB) the STB should be pull down for 2 CLK before sending command on DB bus
      //  2: a DQS preamble should be issued at least 1 CLK before sending command on DB bus

      CMD_EN_DQS: begin
        cmd_ready_o   = 1'b0;

        cs_no         = 1'b0;  // CS Enabled
        stb_o         = 1'b0;

        dqs_cg_en_o   = 1'b1;  // DQS Clock Gating Enabled
        dqs_pair_oe_o = 1'b1;  // DQS Output Enabled
        dqs_pair_ie_o = 1'b0;

        db_oe_o       = 1'b0;
        db_ie_o       = 1'b0;

        state_d       = CMD_SEND_DB;
      end



      // In this state the timing FSM will set type_sel_o to pass the command to the DRAM in PHY module
      // Then based on the command type it will determine the command waiting time
      CMD_SEND_DB: begin
        // send cmd to data bus according to cmd
        type_sel_o    = 2'b00;  // Pass the command port to the DB port to output cmd to DRAM

        cmd_ready_o   = 1'b0;

        cs_no         = 1'b0;  // CS Enabled
        stb_o         = 1'b1;

        dqs_cg_en_o   = 1'b1;  // DQS Clock Gating Enabled
        dqs_pair_oe_o = 1'b1;  // DQS Output Enabled
        dqs_pair_ie_o = 1'b0;

        db_oe_o       = 1'b1;
        db_ie_o       = 1'b0;

        // If the input command is Power-Up reset, keep the STB low
        if (cmd_decoded == rpc_cmd_pkg::CMD_RESET) begin
          stb_o = 1'b0;
        end

        // Next State
        cnt_d   = n_wpst - 1;
        state_d = CMD_ALIGN_WPST;
      end


      // In this state the DQS/DQS# will hold on logic '0' and '1' respectively, then it will jump to states based on different input command
      // This is state is used to fulfill the WPST requirement of RPC DRAM
      CMD_ALIGN_WPST: begin
        cmd_ready_o   = 1'b0;

        cs_no         = 1'b0;  // CS Enabled
        stb_o         = 1'b1;

        dqs_cg_en_o   = 1'b0;  // DQS Clock Gating Disabled
        dqs_pair_oe_o = 1'b1;  // DQS Output Enabled
        dqs_pair_ie_o = 1'b0;

        db_oe_o       = 1'b0;
        db_ie_o       = 1'b0;


        if (cmd_decoded == rpc_cmd_pkg::CMD_RESET) begin
          stb_o = '0;

        end

        if (cnt_q == '0) begin  // tWPST_completes
          /////////////////////////////////////////////////
          //////// Handling Power Up Reset Command ////////
          /////////////////////////////////////////////////
          //If the upstream command is power up reset command, then the FSM will jumpt to the power up reset state
          //To perform power-up reset, the PHY must output a "PU Reset Entry", which contains a parallel reset and 2 consecutive serial reset(pull STB low for 2 * 8CLK)
          //Count from the beginning of parallel packet transition, it takes extra 15 cycles to pull the STB signal low
          if (cmd_decoded == rpc_cmd_pkg::CMD_RESET) begin
            // if reset signal is set, then the STB has to keep low (see Power-Up Initialization Sequnece of RPC DRAM data sheet)
            state_d = PU_STB_RESET;
            cnt_d   = n_pu_stb_reset - 1;

            /////////////////////////////////////////////////
            //////// Handling PRE Command ///////////////////
            /////////////////////////////////////////////////
            // If the command is Pre charge, as Precharge is a one-shot command, this FSM will wait in the next state until the PRE completes
            // Waiting Time is controlled by N_RP
          end else if (cmd_decoded == rpc_cmd_pkg::CMD_PRE) begin
            cnt_d   = n_pre - 1;
            state_d = EN_CS_WAIT_NEW_CMD;


            /////////////////////////////////////////////////
            //////// Handling MRS Command ///////////////////
            /////////////////////////////////////////////////
            // If the command is Mode Register Set,as MRS is a one-shot command, this FSM will wait in the next state until MRS completes
            // Waiting Time is controlled by N_MOD
          end else if (cmd_decoded == rpc_cmd_pkg::CMD_MRS) begin
            cnt_d   = n_mod - 1;
            state_d = EN_CS_WAIT_NEW_CMD;

            /////////////////////////////////////////////////
            //////// Handling ACT Command ///////////////////
            /////////////////////////////////////////////////
            // If the command is Activiate,as ACT is a one-shot command, this FSM will wait in the next state until ACT completes
            // Waiting Time is controlled by N_MOD
          end else if (cmd_decoded == rpc_cmd_pkg::CMD_ACT) begin
            cnt_d   = n_rcd - 1;
            state_d = EN_CS_WAIT_NEW_CMD;

            /////////////////////////////////////////////////
            //////// Handling WR Command ////////////////////
            /////////////////////////////////////////////////

            // If the command is WRITE, this FSM will disable STB in the coming CLK and wait for 4 CLKs
            // See Back-Back Parallel Command (with Parallel Burst Write) of RPC DRAM Datasheet
          end else if (cmd_decoded == rpc_cmd_pkg::CMD_WR) begin
            state_d = WR_WAIT_CL;
            cnt_d   = n_wr_wait_cl - 1;

            /////////////////////////////////////////////////
            //////// Handling RD Command ////////////////////
            /////////////////////////////////////////////////

            // If the command is READ
          end else if (cmd_decoded == rpc_cmd_pkg::CMD_RD) begin
            state_d = RD_WAIT_PREAMBLE;
            cnt_d   = n_rd_wait_preamble - 1;

            /////////////////////////////////////////////////
            //////// Handling REF Command ///////////////////
            /////////////////////////////////////////////////

            // If the command is REFRESH
          end else if (cmd_decoded == rpc_cmd_pkg::CMD_REF) begin
            state_d = REF_HOLD_CS;

            /////////////////////////////////////////////////
            //////// Handling ZQC Command ///////////////////
            /////////////////////////////////////////////////
            // If the command is ZQ Calibration,as ZQC is a one-shot command, this FSM will wait in the next state until ZQC completes
            // Waiting Time is controlled based on the detailed calibration mode i.e. whether it is long/short/initial calibration
          end else if (cmd_decoded == rpc_cmd_pkg::CMD_ZQC) begin
            state_d = EN_CS_WAIT_NEW_CMD;
            case (zqc_mode)
              rpc_cmd_pkg::ZQC_ZQINIT: begin
                cnt_d = n_zqinit;
              end
              rpc_cmd_pkg::ZQC_ZQCL: begin
                cnt_d = n_zqcl;
              end
              rpc_cmd_pkg::ZQC_ZQCS: begin
                cnt_d = n_zqcs;
              end
              rpc_cmd_pkg::ZQC_ZQRESET: begin
                cnt_d = n_zqreset;
              end
            endcase

            /////////////////////////////////////////////////
            //////// Default Handling ///////////////////////
            /////////////////////////////////////////////////

            // If the input command is not a valid one, return to the IDLE state
          end else begin
            state_d = IDLE;
          end

        end else begin
          state_d = CMD_ALIGN_WPST;
          cnt_d   = cnt_q - 1;
        end  // tWPST_completes
      end


      WR_WAIT_CL: begin
        cmd_ready_o   = 1'b0;

        cs_no         = 1'b0;  // CS Enabled
        stb_o         = 1'b1;

        dqs_cg_en_o   = 1'b0;  // DQS Clock Gating Disabled
        dqs_pair_oe_o = 1'b0;  // DQS Output Enabled
        dqs_pair_ie_o = 1'b0;

        db_oe_o       = 1'b0;
        db_ie_o       = 1'b0;

        // If both of the two mask has been sent out, in the coming state the phy will push data into the RPC DRAM
        if (cnt_q == 0) begin
          state_d = WR_EN_DQS;
        end else begin
          state_d = WR_WAIT_CL;
          cnt_d   = cnt_q - 1;
        end
      end


      //Enable the DQS for 1 cycle to generate the toggled DQS signal which will be used as a DQS preamble
      //The preamble tells that the write mask will be given in the coming CLK cycle
      // See Back-Back Parallel Command (with Parallel Burst Write) of RPC DRAM Datasheet
      WR_EN_DQS: begin
        cmd_ready_o   = 1'b0;

        cs_no         = 1'b0;  // CS Enabled
        stb_o         = 1'b1;

        dqs_cg_en_o   = 1'b1;  // DQS Clock Gating Disabled
        dqs_pair_oe_o = 1'b1;  // DQS Output Enabled
        dqs_pair_ie_o = 1'b0;

        db_oe_o       = 1'b0;
        db_ie_o       = 1'b0;

        // Next State
        state_d       = WR_MASK;
        cnt_d         = 19'd1;
      end


      //In this state the two 32bit Mask will be output to the DRAM via DB Bus
      // 1:In the first cycle, the "First Word Mask" will be output to the DRAM
      // 2:In the second cycle, the "Last Word Mask" will be output to the DRAM
      // Once mask sending completes, this fsm will jump to the WR_DATA state to control data writing
      WR_MASK: begin
        mask_sel_o    = cnt_q;  //Select the 32bit mask from the 64 bit input total mask signal
        type_sel_o    = 2'b10;  //Select type pass the Mask Data out to the DRAM in PHY module

        cmd_ready_o   = 1'b0;

        cs_no         = 1'b0;  // CS Enabled
        stb_o         = 1'b1;

        dqs_cg_en_o   = 1'b1;  // DQS Clock Gating Disabled
        dqs_pair_oe_o = 1'b1;  // DQS Output Enabled
        dqs_pair_ie_o = 1'b0;

        db_oe_o       = 1'b1;
        db_ie_o       = 1'b0;

        // If both of the two mask has been sent out, in the coming state the phy will push data into the RPC DRAM
        if (cnt_q == 0) begin
          state_d = WR_DATA;
          // The cmd_i[26:21] stores the burst count of WORDs for one Write Transaction
          // If burst count is 2, there will be 2 consecutive write operation
          // As each word (256 bit) takes 8 clk to write, the counter ceiling will be: 8 * BC + 7
          cnt_d   = (burst_length << 3) + 3'd7;
        end else begin
          state_d = WR_MASK;
          cnt_d   = cnt_q - 1;
        end
      end


      //Write Data Transfer State
      //Select_type is used to pass the upstream data to RPC DRAM via DB Bus
      //In this state the cnt_q will be used to select which 32 bit among a 256 bit is to be pushed into the DRAM
      //If in this cycle the PHY is sending the last 2nd 32bit to the DRAM, then assert ready_dma to ask the upstream for new word  preparation
      WR_DATA: begin

        data_sel_o    = cnt_q[2:0];  //Select which 32 bit slice to be pushed
        type_sel_o    = 2'b01;  //Select Data to DRAM path

        data_ready_o  = 1'b0;

        cmd_ready_o   = 1'b0;

        cs_no         = 1'b0;  // CS Enabled
        stb_o         = 1'b1;

        dqs_cg_en_o   = 1'b1;  // DQS Clock Gating Disabled
        dqs_pair_oe_o = 1'b1;  // DQS Output Enabled
        dqs_pair_ie_o = 1'b0;

        db_oe_o       = 1'b1;
        db_ie_o       = 1'b0;


        // Send out data_ready_o to ask DRAM to prepare new WORD data
        if (cnt_q[2:0] == 3'b1) begin
          data_ready_o = 1;
        end
        // If the data transimision has completed, then jump to EN_CS_ACCPECT_CMD state to wait until the writing has been completed
        // Waiting Time is controlled by N_WR
        // TODO: Now N_WR is replaced by N_W_BESL, check if it is correct
        if (cnt_q == 0) begin
          state_d = WR_ALIGN_WPST;
          cnt_d             = n_align_wr_wpst -1;  //Assert DQS low, DQS# high for N_WPST CLK to satisfy tWPST timing constraint
        end else begin
          state_d = WR_DATA;
          cnt_d   = cnt_q - 1;
        end
      end


      // In this state the DQS/DQS# will hold on logic '0' and '1' respectively, then it will jump to states based on different input command
      // This is state is used to fulfill the WPST requirement after bursting write data
      WR_ALIGN_WPST: begin
        cmd_ready_o   = 1'b0;

        cs_no         = 1'b0;  // CS Enabled
        stb_o         = 1'b1;

        dqs_cg_en_o   = 1'b0;  // DQS Clock Gating Disabled
        dqs_pair_oe_o = 1'b1;  // DQS Output Enabled
        dqs_pair_ie_o = 1'b0;

        db_oe_o       = 1'b0;
        db_ie_o       = 1'b0;

        if (cnt_q == 0) begin
          state_d = EN_CS_WAIT_NEW_CMD;
          cnt_d   = n_wr_besl_after_wpst - 1;  //
        end else begin
          state_d = WR_ALIGN_WPST;
          cnt_d   = cnt_q - 1;
        end
      end


      // This state takes place after sending out Read Command, it will enable the internal pull down of DQS and DB pad, to ensure there is no High-Z on the DB bus before DRAM controls the bus
      // If the High-Z is sensed at the IO pad, the TSMC IO pad may pass a 'x' value into the PHY module db_in and dqs_in input, leading to unpredictable behavior
      RD_WAIT_PREAMBLE: begin
        cmd_ready_o      = 1'b0;

        cs_no            = 1'b0;  // CS Enabled
        stb_o            = 1'b1;

        dqs_cg_en_o      = 1'b0;
        dqs_pair_oe_o    = 1'b0;
        dqs_pair_ie_o    = 1'b0;
        dqs_pair_pd_en_o = 1'b0;  // Pull Down Enabled

        db_oe_o          = 1'b0;
        db_ie_o          = 1'b0;
        db_pd_en_o       = 1'b1;  // Pull down Enabled

        if (cnt_q == 0) begin
          state_d = RD_PAD_EN;
        end else begin
          state_d = RD_WAIT_PREAMBLE;
          cnt_d   = cnt_q - 1;
        end
      end


      // In this state the Input PAD is enabled, when input is enabled, the DQSn pair will read a 0->1 as the PAD has already been pulled down in the previous state
      // It set the Valid signal of CDC source side to 0
      RD_PAD_EN: begin
        cmd_ready_o      = 1'b0;

        cs_no            = 1'b0;  // CS Enabled
        stb_o            = 1'b1;

        dqs_cg_en_o      = 1'b0;
        dqs_pair_oe_o    = 1'b0;
        dqs_pair_ie_o    = 1'b1;  // Input Enabled
        dqs_pair_pd_en_o = 1'b0;  // Pull Down Enabled

        db_oe_o          = 1'b0;
        db_ie_o          = 1'b1;  // Input Enabled
        db_pd_en_o       = 1'b0;  // Pull down Enabled

        state_d          = RD_WAIT;
      end


      //Read waiting state: wait until valid data comes from the RPC DRAM
      //When the FIFO recives data from RPC DRAM, this timing fsm will jump to the RD_DATA state
      //Because the DQS is controlled by the DRAM, this dqs_cg_en_o must be disabled
      RD_WAIT: begin
        cmd_ready_o      = 1'b0;

        cdc_src_valid_o  = 1'b1;  //Enabling CDC input

        cs_no            = 1'b0;  // CS Enabled
        stb_o            = 1'b1;

        dqs_cg_en_o      = 1'b0;
        dqs_pair_oe_o    = 1'b0;
        dqs_pair_ie_o    = 1'b1;  // Input Enabled
        dqs_pair_pd_en_o = 1'b0;

        db_oe_o          = 1'b0;
        db_ie_o          = 1'b1;  // Input Enabled
        db_pd_en_o       = 1'b1;  // Pull down Enabled



        // If the FIFO starts to recevie valid data, jump to RD_DATA state
        if (cdc_dst_valid_i == 1) begin
          state_d = RD_DATA;
          // The cmd_i[26:21] stores the burst count of WORDs for one READ Transaction
          // If burst count is 2, there will be 2 consecutive READ operation
          // As each word (256 bit) requires 8 clk to read, the counter ceiling will be: 8 * BC + 7
          cnt_d   = (burst_length << 3) + 3'd6;
        end else begin
          state_d = RD_WAIT;
        end
      end

      //Read Data Transfer State
      //data_sel_rd is used to put the received 32bit data to the correct location of a 256bit register to reconstruct a 256bit WORD inside PHY
      //In this state the cnt_q will be used to push the recived data to 1 of 8 32bit locations inside the 256bit register
      //If the phy has received the last 32bit data chrunk, it will inform the upstream that a valid word can be picked up
      //If the phy starts to receive the last WORD of this BURST READ operation, this fsm will inform the upstream that the PHY is receiving the last WORD
      RD_DATA: begin

        cdc_src_valid_o  = 1'b1;  //Enabling CDC input
        data_sel_rd      = cnt_q[2:0];
        data_valid_o     = 1'b0;
        data_last_o      = 1'b0;

        cmd_ready_o      = 1'b0;

        cs_no            = 1'b0;  // CS Enabled
        stb_o            = 1'b1;

        dqs_cg_en_o      = 1'b0;
        dqs_pair_oe_o    = 1'b0;
        dqs_pair_ie_o    = 1'b1;  // Input Enabled
        dqs_pair_pd_en_o = 1'b0;

        db_oe_o          = 1'b0;
        db_ie_o          = 1'b1;  // Input Enabled
        db_pd_en_o       = 1'b0;  // Pull down disabled


        //If the phy has received the last 32bit data chrunk, it will inform the upstream that a valid word can be picked up
        if (cnt_q[2:0] == '0) begin
          data_valid_o = 1;
        end

        //If the phy starts to receive the last WORD of this BURST READ operation, this fsm will inform the upstream that the PHY is receiving the last WORD
        if (cnt_q[8:3] == '0) begin
          data_last_o = 1;
        end

        //If the BURST READ has completed, this fsm will jump to EN_CS_WAIT_NEW_CMD to wait for sometime and then listen to new valid input command
        if (cnt_q == 0) begin
          state_d = EN_CS_WAIT_NEW_CMD;
          cnt_d   = n_rd_besl - 1;
        end else begin
          state_d = RD_DATA;
          cnt_d   = cnt_q - 1;
        end
      end
    endcase
  end

  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (rst_ni == 0) begin
      state_q    <= IDLE;
      cnt_q      <= '0;
      tPPD_cnt_q <= '0;
    end else begin
      state_q    <= state_d;
      cnt_q      <= cnt_d;
      tPPD_cnt_q <= tPPD_cnt_d;
    end
  end

endmodule
