// Copyright 2022 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Chen Wang <chewang@student.ethz.ch>
// Jiawei Zhang <jiawzhang@student.ethz.ch>

module ref_timer 
#(
  parameter int unsigned CNT_WIDTH  = 32,
  parameter int unsigned CMD_WIDTH  = 19
)
(
  input  logic  clk_i,
  input  logic  rst_ni,

  // Input interface
  input  logic                                  init_timer_i,         // Initialization flag from conf_reg_management
  input  logic                                  load_config_i,        // Launch flag from conf_reg_management
  input  rpc_config_path_pkg::ref_cfg_reg_t     config_i,             // Launch command from conf_reg_management
  // Output interface
  input   logic                  ref_ready_i,          // Handshaking with down_stream arbiter
  output  logic                  ref_valid_o,          // Handshaking with down_stream arbiter
  output  logic [CMD_WIDTH-1:0]  ref_cmd_o             // Handshaking with down_stream arbiter
);

  /////////////////////////////////////////////////////////////////////////////////////////////////
  ///////////////////////Implement Configuration Register /////////////////////////////////////////
  /////////////////////////////////////////////////////////////////////////////////////////////////

  // Configuration Input Buffer
  rpc_config_path_pkg::ref_cfg_reg_t config_i_buff_d, config_i_buff_q;
  // Buffer Full Indicater
  logic config_i_buff_valid_d, config_i_buff_valid_q;
  // Once the command has been used, clear the input configuration buffer
  logic config_i_buff_clear;


  //The following logic load the configuration to the input buffer
  //This part is independent of the major counter logic

  always_comb begin

    //Initialization
    config_i_buff_d = config_i_buff_q;
    config_i_buff_valid_d = config_i_buff_valid_q;

    //If luanch_config is asserted, load the input configuration into the buffer
    //Then tell the timer new configuration has been latched in the input configuration buffer
    if(load_config_i) begin
      config_i_buff_d = config_i;
      config_i_buff_valid_d = 1'b1;
    //If the current buffer value is read out, and there is no new data coming in, the valid flag will reset to zero
    end else if(config_i_buff_clear) begin 
      config_i_buff_valid_d = 1'b0;
    end
  end


  //This is the register that actually controls the refresh mode
  rpc_config_path_pkg::ref_cfg_reg_t config_reg_d, config_reg_q;
  

  /////////////////////////////////////////////////////////////////////////////////////////////////
  ///////////////////////Implement Counter ////////////////////////////////////////////////////////
  /////////////////////////////////////////////////////////////////////////////////////////////////
  //--------------------Define Signal for REHRESH Command Timer--------------------------
  // REF Timer Enable
  logic   cnt_en;

  // REF Counter Value
  logic   [CNT_WIDTH-1:0] cnt_value;

  // REF Counter Upper Ceiling
  logic   [CNT_WIDTH-1:0] cnt_ceiling;
  // Shift the value stored in configuration register so that the 25bit interval can to used to generate larger interval
  assign  cnt_ceiling = config_reg_q.interval << 7;

  // REF Counter Freeze
  // When handshaking, freeze the counter at the current counter value
  logic   cnt_freeze;
  logic   [CNT_WIDTH-1:0] cnt_freeze_value;
  assign  cnt_freeze_value = cnt_ceiling;

  // REF Counter Clear
  logic   cnt_clear;
  // REF Overflow Flag
  logic   cnt_overflow;
  // REF Counter Freeze

  // The counter upper bound



  //--------------------Counter Implementation-----------------------------------------
  counter #(                
      .WIDTH(CNT_WIDTH),
      .STICKY_OVERFLOW (1'b0) 
  ) i_counter_ref(
      .clk_i        (clk_i),
      .rst_ni       (rst_ni),
      .clear_i      (cnt_clear),          // synchronous clear
      .en_i         (cnt_en),           // enable the counter
      .load_i       (cnt_freeze),         // load a new value
      .down_i       (1'b0),               // downcount, default is up
      .d_i          (cnt_freeze_value),   // The counter value to be frozen
      .q_o          (cnt_value),
      .overflow_o   (cnt_overflow)
  );



  /////////////////////////////////////////////////////////////////////////////////////////////////
  ///////////////////////Implement FSM for Timer Hand Shaking//////////////////////////////////////
  /////////////////////////////////////////////////////////////////////////////////////////////////

  // ---------------------------------Timer FSM-----------------------------------
  typedef enum logic [2:0] {
    POWER_UP,
    INIT,
    IDLE,
    COUNTING,
    CONFIG,
    CMD_OUT
  } state_t;

  state_t   state_d, state_q; 


  always_comb begin :implement_timer_fsm

    //Initialize signals to avoid latch
    state_d = state_q;

    // Input Buffer
    config_i_buff_clear = 1'b0;

    // Timer Control Register
    config_reg_d = config_reg_q;

    // Enable Counter
    cnt_en =  1'b0;
    // Reset Counter
    cnt_clear = 1'b0;
    // Freeze Counter during handshaking
    cnt_freeze = 1'b0;

    ref_valid_o = '0;
    ref_cmd_o = '0;



    case(state_q)
      POWER_UP: begin
        // If init cmd given to this module, start power-up initialization
        if(init_timer_i) begin
          state_d = INIT;
        end else begin
          state_d = POWER_UP;
        end
      end 


      //This sate is necessary to allow the input configuration to come together with init_timer_i
      INIT: begin
        //If the configuration input buffer is not empty, use the configuration stored in the output
        //Otherwise Use the Default Setting 
        if(config_i_buff_valid_q) begin
          config_reg_d = config_i_buff_q;
          // Set config_i_buff_clear to clear up the valid flag, indicating the buffer value has been read
          config_i_buff_clear = 1'b1;
        end else begin 
          config_reg_d = rpc_config_path_pkg::REF_TIMER_DEFAULT_SETTING;
        end
        
        //Since new command is given to the configuration register, the counter_value is reset at the same time
        cnt_clear = 1'b1;
        //Go to the IDLE
        state_d = IDLE;
      end

      //In this state, the following logic will be implemented:

      
      IDLE: begin
        // As the counter is in the IDLE mode, it should disable the counter
        cnt_en = 1'b0;
        // Clear the counter stored value
        cnt_clear = 1'b1;

        //When the configuration register config_reg_q enables the timer, enable the timer on next clock cycle to perform normal operation
        if(config_reg_q.enable) begin
          state_d = COUNTING;
        //When the configuration register config_ref_q disables the timer, wait a new command and load it to the configuration register
        end else begin
          // When new configuration coming in, load the new con
          if(config_i_buff_valid_q) begin
            config_reg_d = config_i_buff_q;
            //Set config_i_buff_clear to clear up the valid flag, indicating the input configuration in the buffer has been used
            config_i_buff_clear = 1'b1;
          end
          state_d = IDLE;
        end
      end

      COUNTING: begin
        //In this state, the counter is enabled
        cnt_en = 1'b1;
        //If the counter value reached, go to the CMD_OUT state
        if(cnt_value == (cnt_ceiling-1)) begin
          state_d = CMD_OUT;
        end else begin
          state_d = COUNTING;
        end
      end

      CMD_OUT: begin
        // Indicate REF command generated
        ref_valid_o = 1'b1;
        // Output command based on configuration setting
        ref_cmd_o = {2'b00,config_reg_q.ref_bank_list,13'b0}; 
        // Freeze the counter 
        cnt_freeze = 1'b1;
        cnt_en     = 1'b0;
        // When downstream is able to accpet command, restart counter cycle
        if(ref_ready_i) begin
          // Clear the counter to start a new cycle
          cnt_clear = 1'b1;
          // Judge if new configuration setting arrives
          if(config_i_buff_valid_q) begin
            config_reg_d = config_i_buff_q;
            config_i_buff_clear = 1'b1;
            state_d = IDLE;
          end else begin
            state_d = COUNTING;
          end
        end else begin
          state_d = CMD_OUT;
        end
      end

      default: begin
        state_d = IDLE;
      end
    endcase
  end


  always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        config_i_buff_q       <= '0;
        config_i_buff_valid_q <= '0;
        config_reg_q          <= '0;
        state_q               <= POWER_UP;             
      end else begin
        config_i_buff_q       <= config_i_buff_d;
        config_i_buff_valid_q <= config_i_buff_valid_d;
        config_reg_q          <= config_reg_d;
        state_q               <= state_d;
      end
  end







    // =========================
    //    Assertions
    // =========================

    `ifndef SYNTHESIS


      default disable iff (~rst_ni);

      // If the timer is enabled, then its interval setting cannot be 0;
      non_zero_timer_interval: assert property (@(posedge clk_i) config_reg_q.enable |-> (config_reg_q.interval != 1'b0))
      else begin
          $error("Enabled timer cannot have 0 interval!");
      end


      // If Reg Bus Wrie Transaction Received
      display_ref_update: assert property (@(posedge clk_i) $stable(config_reg_q)) else begin
        $display("-------------------------------------"); 
        $display("Refresh Timer Module:"); 
        $display("[%0tps] : Timer Config Updating",$time);
        $display("Enable:         %h", config_reg_q.enable);
        $display("REFOP:          %h", config_reg_q.ref_refop);
        $display("Bank List:      %h", config_reg_q.ref_bank_list);
        $display("Time Interval:  %h", config_reg_q.interval);
        $display("-------------------------------------"); 
      end

    // If Reg Bus Wrie Transaction Received
    display_ref_out: assert property (@(posedge clk_i) ref_valid_o && ref_ready_i) begin
      $display("-------------------------------------"); 
      $display("REF Timer Module:"); 
      $display("[%0tps] : REF CMD Sent",$time);
      $display("-------------------------------------"); 
    end else begin
    end


  `endif


endmodule

