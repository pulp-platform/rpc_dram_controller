// Copyright 2022 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Chen Wang <chewang@student.ethz.ch>
// Jiawei Zhang <jiawzhang@student.ethz.ch>

module config_reg #(
  // REG BUS Paramter
  parameter int unsigned REG_WIDTH = 32,
  parameter int unsigned ADDR_WIDTH = 8,
  // Output Parameter
  parameter int unsigned CMD_FIFO_DEPTH = 4,
  parameter int unsigned CMD_WIDTH = 19,
  parameter int unsigned DELAY_CFG_WIDTH = 5,

  // Derived Paramter
  localparam int unsigned STROBE_WIDTH = REG_WIDTH / 8

) (

  // ----------------------------------------------------------------------------------------------
  // ----------------------------clock and reset input  -------------------------------------------
  // ----------------------------------------------------------------------------------------------

  input logic clk_i,
  input logic rst_ni,

  // ----------------------------------------------------------------------------------------------
  // ----------------------------Reg_Bus -> config_reg interface ----------------------------------
  // ----------------------------------------------------------------------------------------------
  input logic   [ADDR_WIDTH-1:0]                        addr_i,
  // write signal
  input logic                                           write_i,
  input logic   [REG_WIDTH-1:0]                         wdata_i,
  input logic   [STROBE_WIDTH-1:0]                      wstrb_i,  // It is of no use to apply mask to the configuration register, so this one is currently omitted
  // read signal
  output logic                                          error_o,
  output logic  [REG_WIDTH-1:0]                         rdata_o,
  // handshaking
  input  logic                                          valid_i,
  output logic                                          ready_o,



  // ----------------------------------------------------------------------------------------------
  // ----------------------------Config Ref -> Timers----------------------------------------------
  // ----------------------------------------------------------------------------------------------

  // config_ref initlization signal
  output logic                                          launch_dram_init_o,
  output rpc_config_path_pkg::dram_init_cfg_reg_t       dram_init_config_o,

  // direct command output config_reg -> CMD_FSM -> DRAM
  input  logic                                          direct_cmd_ready_i,
  output logic                                          direct_cmd_valid_o,
  output logic [CMD_WIDTH-1:0]                          direct_cmd_o,

  // config_reg -> starter_timer
  output logic                                          launch_timer_starter_config_o,
  output rpc_config_path_pkg::timer_starter_cfg_reg_t   timer_starter_config_o,

  // config_reg -> ref_timer
  output logic                                          launch_ref_config_o,
  output rpc_config_path_pkg::ref_cfg_reg_t             ref_config_o,

  // config_reg -> zqc_timer
  output logic                                          launch_zqc_config_o,
  output rpc_config_path_pkg::zqc_cfg_reg_t             zqc_config_o,

  // config_reg ->  DQS, DQS# delay cell
  output logic [DELAY_CFG_WIDTH-1:0]                    phy_clk_90_delay_cfg_o,
  output logic [DELAY_CFG_WIDTH-1:0]                    phy_dqs_i_delay_cfg_o,
  output logic [DELAY_CFG_WIDTH-1:0]                    phy_dqs_ni_delay_cfg_o,

  // timing fsm configuration
  output rpc_config_path_pkg::timing_cfg_reg_t          phy_timing_cfg_o,

  // ----------------------------------------------------------------------------------------------
  // ----------------------------CMD FSM -> Config Ref-------------------------------------------------
  // ----------------------------------------------------------------------------------------------

  input logic                                           rpc_init_completed_i
);


  /////////////////////////////////////////////////////////////////////////////////////////
  ////////////////////// Register Implementation //////////////////////////////////////////
  /////////////////////////////////////////////////////////////////////////////////////////

  //---------------------------Initlization Configuration Register--------------------------
  logic launch_dram_init_config_d, launch_dram_init_config_q;
  rpc_config_path_pkg::dram_init_cfg_reg_t dram_init_config_reg_d, dram_init_config_reg_q;

  assign launch_dram_init_o = launch_dram_init_config_q;
  assign dram_init_config_o = dram_init_config_reg_q;


  //----------------------------------Direct CMD Register-----------------------------------
  // Store the lastest cmd
  rpc_config_path_pkg::direct_command_reg_t direct_command_reg_d, direct_command_reg_q;

  // Insert FIFO

  // From REG BUS -> Config Reg
  logic cmd_fifo_valid_i, cmd_fifo_ready_o;
  // From Config Reg FIFO -> down stream cmd_fsm
  logic cmd_fifo_valid_o, cmd_fifo_ready_i;

  rpc_config_path_pkg::direct_command_reg_t cmd_fifo_o_data;
  assign direct_cmd_o = {cmd_fifo_o_data.cmd_type, cmd_fifo_o_data.cmd_field};


  stream_fifo #(
    .FALL_THROUGH(1'b0),
    .DATA_WIDTH  (REG_WIDTH),
    .DEPTH       (CMD_FIFO_DEPTH),
    .T           (rpc_config_path_pkg::direct_command_reg_t)
  ) i_cmd_fifo (
    .clk_i     (clk_i),
    .rst_ni    (rst_ni),
    .flush_i   (1'b0),
    .testmode_i(1'b0),

    // Input handshaking
    .data_i (wdata_i),
    .valid_i(cmd_fifo_valid_i),
    .ready_o(cmd_fifo_ready_o),
    // Output handshaking
    .data_o (cmd_fifo_o_data),
    .valid_o(direct_cmd_valid_o),
    .ready_i(direct_cmd_ready_i)
  );




  //---------------------------------DRAM starter Register-------------------------------
  logic launch_timer_starter_config_d, launch_timer_starter_config_q;
  rpc_config_path_pkg::timer_starter_cfg_reg_t timer_starter_reg_d, timer_starter_reg_q;

  assign launch_timer_starter_config_o = launch_timer_starter_config_q;
  assign timer_starter_config_o        = timer_starter_reg_q;

  //--------------------------------Ref Timer Confiugration Register------------------------
  logic launch_ref_config_d, launch_ref_config_q;
  rpc_config_path_pkg::ref_cfg_reg_t ref_config_reg_d, ref_config_reg_q;

  assign launch_ref_config_o = launch_ref_config_q;
  assign ref_config_o        = ref_config_reg_q;

  //--------------------------------ZQC Timer Configuration Register------------------------
  logic launch_zqc_config_d, launch_zqc_config_q;
  rpc_config_path_pkg::zqc_cfg_reg_t zqc_config_reg_d, zqc_config_reg_q;

  assign launch_zqc_config_o = launch_zqc_config_q;
  assign zqc_config_o        = zqc_config_reg_q;


  //--------------------------------DQSi, DQS#i delay configuration register------------------------
  rpc_config_path_pkg::delay_line_cfg_reg_t clk_90_delay_cfg_reg_d, clk_90_delay_cfg_reg_q;
  rpc_config_path_pkg::delay_line_cfg_reg_t dqs_i_delay_cfg_reg_d, dqs_i_delay_cfg_reg_q;
  rpc_config_path_pkg::delay_line_cfg_reg_t dqs_ni_delay_cfg_reg_d, dqs_ni_delay_cfg_reg_q;


  assign phy_clk_90_delay_cfg_o = clk_90_delay_cfg_reg_q[DELAY_CFG_WIDTH-1:0];
  assign phy_dqs_i_delay_cfg_o  = dqs_i_delay_cfg_reg_q[DELAY_CFG_WIDTH-1:0];
  assign phy_dqs_ni_delay_cfg_o = dqs_ni_delay_cfg_reg_q[DELAY_CFG_WIDTH-1:0];


  //--------------------------------Timing FSM Configuration Register -------------------------------
  rpc_config_path_pkg::timing_cfg_reg_t timing_cfg_reg_d, timing_cfg_reg_q;
  logic [31:0] timing_cfg_addr_offset;

  assign phy_timing_cfg_o = timing_cfg_reg_q;


  //--------------------------------Register indicating reset complete -------------------------------
  logic rpc_init_completed_d, rpc_init_completed_q;
  // Edge Detection
  assign rpc_init_completed_d = ((!rpc_init_completed_q) && rpc_init_completed_i)? 1'b1 : rpc_init_completed_q;



  //////////////////////////////////////////////////////////////////////////////////////////
  ////////////////////// Implement FSM  ////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////////////////////




  // Define FSM State
  typedef enum logic [1:0] {
    IDLE,
    BUSY
  } state_t;

  state_t reg_bus_state_d, reg_bus_state_q;



  always_comb begin : next_state_logic
    // --------------------Register Initalization---------------------------------
    reg_bus_state_d               = reg_bus_state_q;
    dram_init_config_reg_d        = dram_init_config_reg_q;
    direct_command_reg_d          = direct_command_reg_q;
    timer_starter_reg_d           = timer_starter_reg_q;
    ref_config_reg_d              = ref_config_reg_q;
    zqc_config_reg_d              = zqc_config_reg_q;
    dqs_i_delay_cfg_reg_d         = dqs_i_delay_cfg_reg_q;
    dqs_ni_delay_cfg_reg_d        = dqs_ni_delay_cfg_reg_q;
    clk_90_delay_cfg_reg_d        = clk_90_delay_cfg_reg_q;
    timing_cfg_reg_d              = timing_cfg_reg_q;

    timing_cfg_addr_offset        = '0;

    //---------------------Reg Bus Hand Shaking Initialization--------------------
    rdata_o                       = '0;
    error_o                       = '0;
    ready_o                       = '0;

    // --------------------Output Configuration Init------------------------------
    cmd_fifo_valid_i              = '0;  //FIFO used to store direct cmd data
    launch_dram_init_config_d     = '0;
    launch_timer_starter_config_d = '0;
    launch_ref_config_d           = '0;
    launch_zqc_config_d           = '0;

    //


    // Define state transistion
    case (reg_bus_state_q)
      // In  the idle state the register wait for new data from regbus, if
      IDLE: begin
        // The ready_o tells that a hand shaking has been completed, this module will only assert ready if a data transaction has been conpleted
        // ready_o can be 1 in the IDEL State for Write Mode Operation, however it will cause problem in Read Mode, so it should be 0 for IDLE moudle to insert 1 CLK delay
        ready_o = 1'b0;
        // If valid data asserted by upstream, goes into the BUSY mode
        if (valid_i) begin
          reg_bus_state_d = BUSY;
        end else begin
          reg_bus_state_d = IDLE;
        end
      end


      BUSY: begin
        // Inidicate the transcation has been completed, the upstream may send a new data access comand in the coming clock cycle
        ready_o         = 1'b1;
        reg_bus_state_d = IDLE;
        // Based on the write data, write to the corresponding location
        if (write_i) begin

          if (addr_i == rpc_config_path_pkg::ADDR_INIT_CFG) begin
            launch_dram_init_config_d = 1'b1;
            dram_init_config_reg_d    = wdata_i;
            reg_bus_state_d           = IDLE;

          end else if (addr_i == rpc_config_path_pkg::ADDR_DIRECT_CMD) begin
            // Send upstream valid signal to push data into the FIFO
            cmd_fifo_valid_i = 1'b1;
            // If the FIFO accpect this data, return to the IDLE state and put the current command into temp register for read back
            if (cmd_fifo_ready_o) begin
              reg_bus_state_d      = IDLE;
              direct_command_reg_d = wdata_i;
              // If the FIFO is full, wait until it has been read out
            end else begin
              reg_bus_state_d = BUSY;
              ready_o         = 1'b0;
            end

          end else if (addr_i == rpc_config_path_pkg::ADDR_TIMER_STARTER) begin
            launch_timer_starter_config_d = 1'b1;
            timer_starter_reg_d           = wdata_i;
            reg_bus_state_d               = IDLE;

          end else if (addr_i == rpc_config_path_pkg::ADDR_REF_TIMER) begin
            launch_ref_config_d = 1'b1;
            ref_config_reg_d    = wdata_i;
            reg_bus_state_d     = IDLE;

          end else if (addr_i == rpc_config_path_pkg::ADDR_ZQC_TIMER) begin
            launch_zqc_config_d = 1'b1;
            zqc_config_reg_d    = wdata_i;
            reg_bus_state_d     = IDLE;

          end else if (addr_i == rpc_config_path_pkg::ADDR_DELAY_CFG_CLK_90) begin
            clk_90_delay_cfg_reg_d = wdata_i;
            reg_bus_state_d        = IDLE;

          end else if (addr_i == rpc_config_path_pkg::ADDR_DELAY_CFG_DQS_I) begin
            dqs_i_delay_cfg_reg_d = wdata_i;
            reg_bus_state_d       = IDLE;

          end else if (addr_i == rpc_config_path_pkg::ADDR_DELAY_CFG_DQS_NI) begin
            dqs_ni_delay_cfg_reg_d = wdata_i;
            reg_bus_state_d        = IDLE;

          end else begin
            // Find which timing configuration is updated, based on the updated value, update the corresponding configuration status
            timing_cfg_addr_offset = (addr_i - rpc_config_path_pkg::ADDR_TIMING_CONFIG_START) >> 2;
            if(timing_cfg_addr_offset >= 0 && timing_cfg_addr_offset <= rpc_config_path_pkg::NUM_TIMING_CONFIG) begin
              timing_cfg_reg_d[timing_cfg_addr_offset] = wdata_i;
            end
          end

          // Handle the READ Mode

        end else begin

          if (addr_i == rpc_config_path_pkg::ADDR_INIT_CFG) begin
            rdata_o = dram_init_config_reg_q;

          end else if (addr_i == rpc_config_path_pkg::ADDR_INIT_COMP) begin
            rdata_o = rpc_init_completed_q;

          end else if (addr_i == rpc_config_path_pkg::ADDR_DIRECT_CMD) begin
            rdata_o = direct_command_reg_q;

          end else if (addr_i == rpc_config_path_pkg::ADDR_TIMER_STARTER) begin
            rdata_o = timer_starter_reg_q;

          end else if (addr_i == rpc_config_path_pkg::ADDR_REF_TIMER) begin
            rdata_o = ref_config_reg_q;

          end else if (addr_i == rpc_config_path_pkg::ADDR_ZQC_TIMER) begin
            rdata_o = zqc_config_reg_q;

          end else if (addr_i == rpc_config_path_pkg::ADDR_DELAY_CFG_CLK_90) begin
            rdata_o = clk_90_delay_cfg_reg_q;

          end else if (addr_i == rpc_config_path_pkg::ADDR_DELAY_CFG_DQS_I) begin
            rdata_o = dqs_i_delay_cfg_reg_q;

          end else if (addr_i == rpc_config_path_pkg::ADDR_DELAY_CFG_DQS_NI) begin
            rdata_o = dqs_ni_delay_cfg_reg_q;

          end else begin
            // Find which timing configuration is updated, based on the updated value, update the corresponding configuration status
            timing_cfg_addr_offset = (addr_i - rpc_config_path_pkg::ADDR_TIMING_CONFIG_START) >> 2;
            if(timing_cfg_addr_offset >= 0 && timing_cfg_addr_offset <= rpc_config_path_pkg::NUM_TIMING_CONFIG) begin
              rdata_o = timing_cfg_reg_q[timing_cfg_addr_offset];
            end else begin
              error_o = 1'b1;
            end
          end

          reg_bus_state_d = IDLE;
        end

      end
    endcase
  end



  // -------------------------Define the sequential logic --------------------------------------------
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin

      // State Reset
      reg_bus_state_q               <= IDLE;

      // Register Reset
      dram_init_config_reg_q        <= '0;
      direct_command_reg_q          <= '0;
      timer_starter_reg_q           <= '0;
      ref_config_reg_q              <= '0;
      zqc_config_reg_q              <= '0;
      dqs_i_delay_cfg_reg_q         <= '0;
      dqs_ni_delay_cfg_reg_q        <= '0;
      clk_90_delay_cfg_reg_q        <= '0;
      timing_cfg_reg_q              <= '0;

      // Launch Signal Reset
      launch_dram_init_config_q     <= '0;
      launch_timer_starter_config_q <= '0;
      launch_ref_config_q           <= '0;
      launch_zqc_config_q           <= '0;

      rpc_init_completed_q          <= '0;

    end else begin
      reg_bus_state_q               <= reg_bus_state_d;
      dram_init_config_reg_q        <= dram_init_config_reg_d;
      direct_command_reg_q          <= direct_command_reg_d;
      timer_starter_reg_q           <= timer_starter_reg_d;
      ref_config_reg_q              <= ref_config_reg_d;
      zqc_config_reg_q              <= zqc_config_reg_d;
      dqs_i_delay_cfg_reg_q         <= dqs_i_delay_cfg_reg_d;
      dqs_ni_delay_cfg_reg_q        <= dqs_ni_delay_cfg_reg_d;
      timing_cfg_reg_q              <= timing_cfg_reg_d;

      launch_dram_init_config_q     <= launch_dram_init_config_d;
      launch_timer_starter_config_q <= launch_timer_starter_config_d;
      launch_ref_config_q           <= launch_ref_config_d;
      launch_zqc_config_q           <= launch_zqc_config_d;
      clk_90_delay_cfg_reg_q        <= clk_90_delay_cfg_reg_d;

      rpc_init_completed_q          <= rpc_init_completed_d;

    end
  end


  // =========================
  //    Assertions
  // =========================


`ifndef SYNTHESIS
  default disable iff (~rst_ni);

  initial
    assert (REG_WIDTH == 32)
    else begin
      $error("The Register Width must be 32!");
    end

  initial
    assert (ADDR_WIDTH == 5)
    else begin
      $error("The ADDR Width must be 5!");
    end

  initial
    assert (DELAY_CFG_WIDTH == 5)
    else begin
      $error("The DQS Delay Config Width must be 5!");
    end

  initial
    assert (CMD_WIDTH == 19)
    else begin
      $error("The CMD Width must be 19!");
    end


  // If Reg Bus Wrie Transaction Received
  display_reg_bus_trans :
  assert property (@(posedge clk_i) (valid_i && ready_o && write_i)) begin
    $display("-------------------------------------");
    $display("Configuration Regiser Module report:");
    $display("[%0tps] : Reg Bus Write Transaction", $time);
    $display("Input Address:  %h", $sampled(addr_i));
    $display("Input Data:     %h", $sampled(wdata_i));
    $display("INput Strobe:   %h", $sampled(wstrb_i));
    $display("-------------------------------------");
  end else begin
  end


  // If Reg Bus Wrie Transaction Received
  display_dram_init :
  assert property (@(posedge clk_i) (launch_dram_init_o)) begin
    $display("-------------------------------------");
    $display("Configuration Regiser Module report:");
    $display("[%0tps] : DRAM Initialization Triggered!", $time);
    $display("Initialization Configuration: %h", dram_init_config_o);
    $display("-------------------------------------");
  end else begin
  end

`endif

endmodule
