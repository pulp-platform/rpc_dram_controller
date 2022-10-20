// Copyright 2022 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Chen Wang <chewang@student.ethz.ch>
// Jiawei Zhang <jiawzhang@student.ethz.ch>

module timer_starter #(
  parameter int unsigned CNT_WIDTH = 32,
  parameter int unsigned CMD_WIDTH = 19
) (

  //Input Interface
  input  logic  clk_i,
  input  logic  rst_ni,

  //Load from conf_reg_management
  input  logic  load_config_i,
  input  rpc_config_path_pkg::timer_starter_cfg_reg_t   config_i,

  //Default init time from cmd_fsm
  input  logic  rpc_init_completed_i,

  //Output Interface
  output logic  init_timer_o
);

  /////////////////////////////////////////////////////////////////////////////////////////////////
  ///////////////////////Implement Configuration Register /////////////////////////////////////////
  /////////////////////////////////////////////////////////////////////////////////////////////////


  rpc_config_path_pkg::timer_starter_cfg_reg_t config_i_buff_d, config_i_buff_q;
  logic config_i_buff_valid_d, config_i_buff_valid_q;
  logic config_i_buff_clear;
  logic rpc_init_status_d, rpc_init_status_q;
  logic rpc_init_status_clear;

  //The following logic load the configuration to the input buffer
  //This part is independent of the major counter logic

  //Generate long pulse of rpc_init_status
  always_comb begin
    rpc_init_status_d = rpc_init_status_q;
    if (rpc_init_completed_i) begin
      rpc_init_status_d = 1'b1;
    end
  end

  //Generate long pulse of config_i_buff_valid
  always_comb begin
    config_i_buff_d       = config_i_buff_q;
    config_i_buff_valid_d = config_i_buff_valid_q;
    //If luanch_config is asserted, load the input configuration into the buffer
    if (load_config_i) begin
      config_i_buff_d       = config_i;
      config_i_buff_valid_d = 1'b1;
      //If the current buffer value is read out, and there is no new data coming in, the valid flag will reset to zero
    end else if (config_i_buff_clear) begin
      config_i_buff_valid_d = 1'b0;
    end
  end


  //This is the register that actually controls the refresh mode
  rpc_config_path_pkg::timer_starter_cfg_reg_t config_reg_d, config_reg_q;



  /////////////////////////////////////////////////////////////////////////////////////////////////
  ///////////////////////Implement Counter ////////////////////////////////////////////////////////
  /////////////////////////////////////////////////////////////////////////////////////////////////
  //--------------------Define Signal for INIT Command Counter--------------------------
  // INIT Counter Enable
  logic cnt_en;
  // INIT Counter Value
  logic [CNT_WIDTH-1:0] cnt_value;

  // Counter Uppper Ceilling
  logic [CNT_WIDTH-1:0] cnt_ceiling;
  assign cnt_ceiling = config_reg_q.interval << 7;



  // INIT Counter Clear
  logic cnt_clear;
  // INIT Overflow Flag
  logic cnt_overflow;



  //--------------------Logic Implementation-----------------------------------------
  counter #(  // Counter to program init time
    .WIDTH          (CNT_WIDTH),
    .STICKY_OVERFLOW(1'b0)
  ) i_counter_starter (
    .clk_i     (clk_i),
    .rst_ni    (rst_ni),
    .clear_i   (cnt_clear),    // synchronous clear
    .en_i      (cnt_en),       // enable the counter
    .load_i    (1'b0),         // load a new value
    .down_i    (1'b0),         // downcount, default is up
    .d_i       ('0),           // Load value
    .q_o       (cnt_value),
    .overflow_o(cnt_overflow)
  );



  /////////////////////////////////////////////////////////////////////////////////////////////////
  ///////////////////////   Implement FSM for init_timer_o   //////////////////////////////////////
  /////////////////////////////////////////////////////////////////////////////////////////////////

  // ---------------------------------Timer FSM-----------------------------------

  typedef enum logic [1:0] {
    POWER_UP,
    IDLE,
    COUNTING,
    INIT
  } state_t;

  state_t state_d, state_q;

  always_comb begin : implement_init_fsm

    //Initialize signals to avoid launch
    state_d               = state_q;
    cnt_en                = 1'b0;
    config_i_buff_clear   = 1'b0;
    rpc_init_status_clear = 1'b0;

    config_reg_d          = config_reg_q;
    //Initialize counter reset
    cnt_clear             = 1'b0;

    //Initialize output
    init_timer_o          = 1'b0;


    case (state_q)
      IDLE: begin
        // if DRAM has completed initialization and the timer starter has been configured
        if (rpc_init_status_q && config_i_buff_valid_q) begin
          // Check the configuration to determine waiting time
          if (config_i_buff_q.mode == 1'b1) begin
            config_reg_d = config_i_buff_q;
          end else begin
            config_reg_d = rpc_config_path_pkg::TIMER_STARTER_DEFAULT_SETTING;
          end
          state_d = COUNTING;
        end
      end

      COUNTING: begin
        //If the counter value reached, go to the CMD_OUT state
        cnt_en = 1'b1;
        if (cnt_value == (cnt_ceiling - 1)) begin
          state_d = INIT;
        end else begin
          state_d = COUNTING;
        end
      end

      INIT: begin
        init_timer_o        = 1'b1;
        state_d             = IDLE;
        // Clear the counter to start a new cycle
        cnt_clear           = 1'b1;
        config_i_buff_clear = 1'b1;
        cnt_en              = 1'b0;
      end
    endcase
  end


  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (rst_ni == 1'b0) begin
      state_q               <= IDLE;
      config_i_buff_q       <= '0;
      config_i_buff_valid_q <= '0;
      config_reg_q          <= '0;
      rpc_init_status_q     <= '0;
    end else begin
      state_q               <= state_d;
      config_i_buff_q       <= config_i_buff_d;
      config_i_buff_valid_q <= config_i_buff_valid_d;
      config_reg_q          <= config_reg_d;
      rpc_init_status_q     <= rpc_init_status_d;
    end
  end

  // =========================
  //    Assertions
  // =========================

`ifndef SYNTHESIS

  default disable iff (~rst_ni);

  // If cmd_fsm has asserted that dram initialization completed!
  display_dram_init_complete :
  assert property (@(posedge clk_i) (rpc_init_completed_i)) begin
    $display("-------------------------------------");
    $display("Timer Starter Module Report");
    $display("[%0tns] : DRAM Initialization Completed!", $time);
    $display("-------------------------------------");
  end else begin
  end

  // If cmd_fsm has asserted that dram initialization completed!
  display_module_init_complete :
  assert property (@(posedge clk_i) $stable(config_reg_q))
  else begin
    $display("-------------------------------------");
    $display("Timer Starter Module Report");
    $display("[%0tns] : Timer Starter Initilized", $time);
    $display("Mode:          %h", config_reg_q.mode);
    $display("dont_care:     %h", config_reg_q.dont_care);
    $display("Time Interval: %d", cnt_ceiling);
    $display("-------------------------------------");
  end

`endif

endmodule  // timer_init_gen
