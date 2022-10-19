// Copyright 2022 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Vaibhav Krishna <vakrishna@student.ethz.ch>
// Rui Zhou <ruzhou@student.ethz.ch>
// Chen Jinfan <jinfchen@student.ethz.ch>
// Chen Wang <chewang@student.ethz.ch>
// Jiawei Zhang <jiawzhang@student.ethz.ch>

module rpc_cmd_fsm 
  #(
  	parameter int DRAM_CMD_WIDTH   = 32,
    parameter int ARB_IN_NUM       = 4,
    parameter int ARB_DATA_WIDTH   = 27,
    parameter type DataType   = logic [ARB_DATA_WIDTH-1:0]
	) (

    // ----------------------------------------------------------------------------------------------
    // ----------------------------clock and reset input  -------------------------------------------
    // ----------------------------------------------------------------------------------------------
      input  logic                                        clk_i,
      input  logic                                        rst_ni,


    // ----------------------------------------------------------------------------------------------
    // ----------------------------Upstream Interface  ----------------------------------------------
    // ----------------------------------------------------------------------------------------------

      // Interface with Data Path for READ/WRTIE CMD Operation
      input  logic                                        data_path_valid_i,
      output logic                                        data_path_ready_o,
      input  logic  [19:0]                                data_path_addr_i,
      input  logic  [5:0]                                 data_path_len_i,
      input  logic                                        data_path_is_write_i, 

      //Signals interface to accept SoC Direct Command
      input  logic                                        direct_cmd_valid_i,
      output logic                                        direct_cmd_ready_o,
      input  logic  [19-1:0]                              direct_cmd_i,

      // Initialization Command Interface
      input  logic                                        launch_init_i,
      input  rpc_config_path_pkg::dram_init_cfg_reg_t     dram_init_config_i,

      //Output Flag, asserted when RPC DRAM initilization complete. Used to trigger timer initialization
      output  logic                                       rpc_init_completed_o,

      // Ref Command Interface
      input  logic                                        ref_valid_i,
      output logic                                        ref_ready_o,
      input  logic  [19-1:0]                              ref_cmd_i,

      // ZQC Command Interface
      input  logic                                        zqc_valid_i,
      output logic                                        zqc_ready_o,
      input  logic  [19-1:0]                              zqc_cmd_i,

    // ----------------------------------------------------------------------------------------------
    // ---------------------------- CMD_FSM -> PHY Interface  ---------------------------------------
    // ----------------------------------------------------------------------------------------------

      //Output to PHY module
      input  logic                                        phy_ready_i,
      output logic                                        phy_valid_o,
      output logic  [DRAM_CMD_WIDTH-1:0]                  phy_cmd_o
);
 


  ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  ///////////////////////////////////////////////////////Begin SoC CMD / DMA CMD Arbiter/////////////////////////////////////////////////////////////////////
  ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  // The round robin arbiter handles the command collsions both DMA and the upstream SoC Core want to control PHY operation
  // The arbiter determines whose command should be given to PHY module at one time


  //------------------Upstream Command -> CMD Arbiter--------------------------------
  // Input CMD Request
  // When a input client has valid command, the corresponding bit will be asserted
  logic [ARB_IN_NUM -1:0] arb_i_req;
  // assign arb_i_req  = {zqc_valid_i, ref_valid_i, direct_cmd_valid_i, data_path_valid_i};
  assign arb_i_req  = {ref_valid_i, zqc_valid_i, direct_cmd_valid_i, data_path_valid_i};
  
  // Input CMD Data
  DataType [ARB_IN_NUM -1:0] arb_i_data;
  assign arb_i_data[0] = {data_path_addr_i, data_path_len_i, data_path_is_write_i};
  assign arb_i_data[1] = {direct_cmd_i, 8'b0};
  // Note: Due to unkown reason, without using the following order will lead to signal disconnection in synthesis
  assign arb_i_data[2] = {zqc_cmd_i,8'b0};
  assign arb_i_data[3] = {ref_cmd_i,8'b0};
  

  // Output grant flag
  // When a certain command is given to the downstream PHY, the one-hot grant flag will tell the upstream
  logic [ARB_IN_NUM -1:0] arb_o_gnt;
  assign data_path_ready_o  = arb_o_gnt[0];
  assign direct_cmd_ready_o = arb_o_gnt[1];
  // Note: Due to unkown reason, without using the following order will lead to signal disconnection in synthesis
  assign zqc_ready_o        = arb_o_gnt[2];
  assign ref_ready_o        = arb_o_gnt[3];


  //------------------CMD Arbiter to CMD_FSM-------------------------
  DataType data_o;
  
  // Indicate arbiter has valid output to pass to the downstream
  logic arb_o_valid;
  logic arb_i_ready;

  // Index of the winner client of command arbitration
  // i.e. if client 1 is granted idx_o = 1
  logic [1:0] arb_o_idx;



  //------------------CMD Arbiter--------------------------------
  rr_arb_tree #(
    .NumIn      (ARB_IN_NUM), 
    .DataWidth  (ARB_DATA_WIDTH),
    .AxiVldRdy  (1'b1),
    .LockIn     (1'b1)
  ) i_rr_arb (

    // system clk and rst
    .clk_i(clk_i),
    .rst_ni (rst_ni),

    // upstream -> arbiter interface
    .req_i  (arb_i_req),
    .data_i (arb_i_data),
    
    .gnt_o  (arb_o_gnt),

    // arbiter -> cmd_fsm

    .req_o  (arb_o_valid),  // tells arbiter have valid cmd to cmd_fsm
    .data_o (data_o),
    .idx_o  (arb_o_idx),

    .gnt_i  (arb_i_ready),

    // Unused functionalities
    .flush_i(1'b0),
    .rr_i   ('0)
  );


  ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  ///////////////////////////////////////////////////////Begin FSM for Command Sequence//////////////////////////////////////////////////////////////////////
  ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


  // define the states for this state machine
  typedef enum logic[7:0] {
    DUMM,
    READY,
    WRITE,
    READ,
    RESET,
    PRECHARGE_ALL,
    PRECHARGE,
    ACTIVATE,
    CAL_INIT,
    MRS_INIT,
    REF,
    MRS,
    ZQ_CAL
  } state;

  state                 state_q, state_d;
  logic [3:0]           bank;


  ///////////
  // Logic //
  ///////////
  logic [5:0]             len_q, len_d;
  logic [19:0]            addr_q, addr_d; 
  logic                   is_write_q, is_write_d;  
  logic [16:0]            cmd_reg_q, cmd_reg_d;
  rpc_config_path_pkg::dram_init_cfg_reg_t  dram_init_config_reg_d, dram_init_config_reg_q;



  //-----------------------------------------------------Begin the FSM state transition logic--------------------------------------------------------------------
  always_comb begin


    arb_i_ready = 0;

    phy_valid_o = 1;
    phy_cmd_o = 32'b1;

    state_d = RESET;
    bank = 4'b0001;
    len_d = len_q;
    addr_d = addr_q;
    is_write_d = is_write_q;
    cmd_reg_d = cmd_reg_q;
    dram_init_config_reg_d = dram_init_config_reg_q;

    rpc_init_completed_o = 1'b0;   //Default, load_init_fsm to timer_init_gen is low


    case (addr_q[19:18]) 
      2'b00 : begin
        bank = 4'b0001;
      end
      2'b01 : begin 
        bank = 4'b0010;
      end
      2'b10 : begin
        bank = 4'b0100;
      end
      2'b11 : begin
        bank = 4'b1000;
      end
    endcase
  
    case (state_q)

      // ------------------------------------------- Begin Ready State Logic--------------------------------------------------------------
      // Ready State indicates that the cmd_fsm is ready to pick up new command from the command arbiter

      READY : begin 
        // If the SoC does not intend to trigger RPC DRAM initlization
        if(launch_init_i == 0)begin
          phy_valid_o = 0;
          arb_i_ready = 1;

          // If the command is valid and it is a data path W/R command, activate the target address
          if (arb_o_valid ==1 && arb_o_idx == '0) begin 
            phy_valid_o = 1;
            state_d = ACTIVATE;
            //                      BA          ACT            ROW ADDR
            phy_cmd_o = {11'b0, addr_q[19:18], 3'b101 ,3'b000, addr_q[17:6], 1'b0};
            len_d = data_o[6:1];
            addr_d = data_o[26:7];
            is_write_d = data_o[0];

           // If the command is a RPC DRAM regular maintenance command
          end else if (arb_o_valid == 1) begin
            phy_valid_o = 1;
            cmd_reg_d = data_o[24:8];
            if (data_o[26:25] == 2'b0) begin 
                // Refresh Command: Based on data_o[24:21] determine which banks are to be refreshed
                // 1000 - BK3, 0100 - BK2, 0010 - BK1, 0001 - BK0
                // 1100 - BK3,BK2 etc.
                phy_cmd_o = {6'b0, data_o[24:21], 3'b0, 3'b110, 15'b0, 1'b0};
                state_d = REF;
            end else if (data_o[26:25] == 2'b01) begin 
                // ZQ Calibration Command: Based on  data_o[24:23] determine which ZQ calibration mode is chosen
                phy_cmd_o = {data_o[24:23], 11'b0, 3'b001, 15'b0, 1'b1};
                state_d = ZQ_CAL;
            end else if (data_o[26:25] == 2'b10) begin 
                // Mode Register Set Command
                //             ODT             Zout          nWR             CL                    TM        ODT PD      CSR FX    STB ODT 
                phy_cmd_o = {data_o[24:22], data_o[21:18], data_o[17:15], data_o[14:12], 3'b010, data_o[11], data_o[10], data_o[9], data_o[8], 11'b0, 1'b0};
                state_d = MRS;
            end else begin
                state_d = READY;
            end
          end else begin
            state_d = READY;
          end


        // If the SoC triggers RPC DRAM initlization
        end else if(launch_init_i == 1) begin
          // Store initlization config
          dram_init_config_reg_d = dram_init_config_i;
          phy_valid_o = 0;
          arb_i_ready = 1;
          state_d = DUMM;
        end
      end



      //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
      //////////////////////Begin Regular DRAM maintenance State////////////////////////////////////////////////////////////
      //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

      // ------------------------------------------- Begin REF State Logic---------
      REF : begin
        phy_valid_o = 1;
        arb_i_ready = 0;
        // phy_cmd_o = {6'b0, data_o[24:21], 3'b0, 3'b110, 15'b0, 1'b0};
        phy_cmd_o = {6'b0, cmd_reg_q[16:13], 3'b0, 3'b110, 15'b0, 1'b0};
        if (phy_ready_i) begin
          phy_valid_o = '0;
          state_d = READY;
        end else begin
          state_d = REF;
        end
      end

      ZQ_CAL : begin 
        phy_valid_o = 1;
        arb_i_ready = 0;
        // phy_cmd_o = {data_o[24:23], 11'b0, 3'b001, 15'b0, 1'b1};
        phy_cmd_o = {cmd_reg_q[16:15], 11'b0, 3'b001, 15'b0, 1'b1};
        if (phy_ready_i) begin
          phy_valid_o = '0;
          state_d = READY;
        end else begin
          state_d = ZQ_CAL;
        end
      end

      MRS : begin
        phy_valid_o = 1;
        arb_i_ready = 0;
        // phy_cmd_o = {data_o[24:22], data_o[21:18], data_o[17:15], data_o[14:12], 3'b010, data_o[11], data_o[10], data_o[9], data_o[8], 11'b0, 1'b0};
        phy_cmd_o = {cmd_reg_q[16:14], cmd_reg_q[13:10], cmd_reg_q[9:7], cmd_reg_q[6:4], 3'b010, cmd_reg_q[3], cmd_reg_q[2], cmd_reg_q[1], cmd_reg_q[0], 11'b0, 1'b0};
        if (phy_ready_i) begin
          phy_valid_o = '0;
          state_d = READY;
        end else begin
          state_d = MRS;
        end
      end



      //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
      //////////////////////Begin Data-Accessinhg Related  State////////////////////////////////////////////////////////////
      //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
      PRECHARGE : begin 
        phy_valid_o = 1;
        arb_i_ready = 0;
        phy_cmd_o = {6'b0, bank, 3'b000, 3'b100, 15'b0, 1'b0};
        // Once complete PRECHARGE, return to the READY state to listen to new insturctions
        if (phy_ready_i) begin
          state_d = READY;
          phy_valid_o = '0;
        end else begin
          state_d = PRECHARGE;
        end
      end


      //--------------------------------------- Begin ACT State Logic-----------------------------------
      //Keep the Activate Command until finishing hand shaking with down stream phy
      //When the DMA Insturction is to write down data into DRAM, cmd_fsm enters WRITE state
      //When the DMA Insturction is to read out data from DRAM, cmd_fsm enters READ state

      ACTIVATE : begin
        phy_valid_o = 1;
        arb_i_ready = 0;
        phy_cmd_o = {11'b0, addr_q[19:18], 3'b101 ,3'b000, addr_q[17:6], 1'b0};

        //If the command is a WRITE command, give WRTIE Command to PHY
        if (phy_ready_i == 1 && is_write_q == 1) begin
          state_d = WRITE;
          //             CA6-4        XX    BC     BA1 BA0       WR CMD  CA9-CA7      XXXX
          phy_cmd_o = {addr_q[2:0] ,2'b0 ,len_q ,addr_q[19:18], 3'b001, addr_q[5:3], 12'b0 ,1'b0};

        //If the command is a READ command, give READ Command to PHY
        end else if (phy_ready_i == 1 && is_write_q == 0) begin
          state_d = READ;
          //            CA6-4        XX    BC     BA1 BA0       RD CMD  CA9-CA7      XXXX
          phy_cmd_o = {addr_q[2:0] ,2'b0 ,len_q ,addr_q[19:18], 3'b000, addr_q[5:3], 12'b0 ,1'b0};
        end else begin
          state_d = ACTIVATE;
        end
      end


      //------------------------------------------- Begin WRITE State Logic-----------------------
      WRITE : begin 
        phy_valid_o = 1;
        arb_i_ready = 0;
        phy_cmd_o = {addr_q[2:0] ,2'b0 ,len_q ,addr_q[19:18], 3'b001, addr_q[5:3], 12'b0 ,1'b0};

        // Once write command completes, output PRECHARE command to close the accessed row
        if (phy_ready_i) begin
          state_d = PRECHARGE;
          //                  BA    XXX       PRE
          phy_cmd_o = {6'b0, bank, 3'b000, 3'b100, 15'b0, 1'b0};
        end else begin
          state_d = WRITE;
        end
      end


      //------------------------------------------- Begin READ State Logic-----------------------
      READ : begin
        phy_valid_o = 1;
        arb_i_ready = 0;
        phy_cmd_o = {addr_q[2:0] ,2'b0 ,len_q ,addr_q[19:18], 3'b000, addr_q[5:3], 12'b0 ,1'b0};

        // Once read command completes, output PRECHARE command to close the accessed row
        if (phy_ready_i) begin
          state_d = PRECHARGE;
          //                  BA    XXX       PRE
          phy_cmd_o = {6'b0, bank, 3'b000, 3'b100, 15'b0, 1'b0};
          //phy_valid_o = '0;
        end else begin
          state_d = READ;
        end
      end


      //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
      //////////////////////Begin RPC DRAM Initialization Related-State/////////////////////////////////////////////////////
      //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

      //-------------- Begin DUMM State Logic----------
      //In DUMM State the RESET instruction is output to the PHY module

      DUMM : begin 
        phy_valid_o = 1;
        arb_i_ready = 0;
        phy_cmd_o = {1'b0, 12'b0, 3'b000, 15'b0, 1'b1};
        state_d = RESET;
      end


      //------------- Begin Reset State Logic-----------
      //If handshaking complete, send precharge command to precharge all the four banks BK3-0
      //If handshaking fails, hold RESET command

      RESET : begin
        phy_valid_o = 1;
        arb_i_ready = 0;
        phy_cmd_o = {1'b0, 12'b0, 3'b000, 15'b0, 1'b1};
        if (phy_ready_i) begin
          state_d = PRECHARGE_ALL;
          //                   BK3-0          PRE
          phy_cmd_o = {6'b0, 4'b1111, 3'b0, 3'b100, 15'b0, 1'b0};
        end else begin
          state_d = RESET;
        end
      end


      //--------------Begin PRECHARGE_ALL State Logic---------------
      PRECHARGE_ALL : begin
        phy_valid_o = 1;
        arb_i_ready = 0;
        phy_cmd_o = {6'b0, 4'b1111, 3'b0, 3'b100, 15'b0, 1'b0};
        //If hand shaking completes, going into the next state
        if (phy_ready_i) begin
          state_d = MRS_INIT;
          //           ODT-60  Zout-120  nWR=8  CL=8     MRS     TM
          phy_cmd_o = {dram_init_config_reg_q.odt,      
                       dram_init_config_reg_q.zout,     
                       dram_init_config_reg_q.nwr,      
                       dram_init_config_reg_q.cl,       
                       3'b010,                          
                       dram_init_config_reg_q.tm,     
                       dram_init_config_reg_q.odt_pd, 
                       dram_init_config_reg_q.csr_fx, 
                       dram_init_config_reg_q.stb_odt, 
                       11'b0, 
                       1'b0};
          //phy_cmd_o = {3'b001, 4'b0010, 3'b011, 3'b000, 3'b010, 1'b1, 3'b0, 11'b0, 1'b0};
        end else begin
          state_d = PRECHARGE_ALL;
        end
      end


      //--------------Begin MRS_INIT State Logic----------------------
      MRS_INIT : begin
        phy_valid_o = 1;
        arb_i_ready = 0;
        phy_cmd_o = {dram_init_config_reg_q.odt,    dram_init_config_reg_q.zout, 
                     dram_init_config_reg_q.nwr,    dram_init_config_reg_q.cl, 
                     3'b010, 
                     dram_init_config_reg_q.tm,     dram_init_config_reg_q.odt_pd, 
                     dram_init_config_reg_q.csr_fx, dram_init_config_reg_q.stb_odt, 
                     11'b0, 1'b0};
        //phy_cmd_o = {3'b001, 4'b0010, 3'b011, 3'b000, 3'b010, 1'b1, 3'b0, 11'b0, 1'b0};
        //If hand shaking completes, going into the next state
        if (phy_ready_i) begin
          state_d = CAL_INIT;
          //       Init Cali,       ZQ Calib
          phy_cmd_o = {2'b00, 11'b0, 3'b001, 15'b0, 1'b1};
        end else begin
          state_d = MRS_INIT;
        end
      end

      //--------------Begin CAL_INIT State Logic----------------------
      CAL_INIT : begin
        phy_valid_o = 1;
        arb_i_ready = 0;
        phy_cmd_o = {2'b00, 11'b0, 3'b001, 15'b0, 1'b1};
        ///If hand shaking completes, then the RPC DRAM finishes initialization
        // the CMD FSM returns to READY state to listen to new instructions
        if (phy_ready_i) begin
          phy_valid_o = '0;
          state_d = READY;
          rpc_init_completed_o = 1'b1;   //Send initialize flag to timer_init_gen
        end else begin
          state_d = CAL_INIT;
        end
      end
    endcase
  end

  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (rst_ni == 0) begin
      state_q     <= READY;
      len_q       <= '0;
      addr_q      <= '0;
      is_write_q  <= '0;
      cmd_reg_q   <= '0;
      dram_init_config_reg_q  <= '0;
    end else begin
      state_q     <= state_d;
      len_q       <= len_d;
      addr_q      <= addr_d;
      is_write_q  <= is_write_d;
      cmd_reg_q   <= cmd_reg_d;
      dram_init_config_reg_q  <= dram_init_config_reg_d;
    end
  end

endmodule