## timing constraints

# 50 MHz differential clock for Genesys 2 FPGA
create_clock -add -name rpc_clk -period 20.00 -waveform {0 2.5} [get_ports clkp_i]
set_property CLOCK_DEDICATED_ROUTE ANY_CMT_COLUMN [get_nets clkp_i]

# rst_n
set_max_delay -from [get_ports rst_ni] [expr 0.7*5]

# Constrain clock domain crossings
# cdc_fifo_gray
set async_pins [get_pins "i_rpc_top/i_rpc_controller/i_rpc_phy_controller/i_rpc_phy/i_cdc_fifo/*/*async*"]
set_false_path -through ${async_pins}

# clock domain crossing
set_false_path -from [get_clocks clkfbout_xilinx_phase_shift_90] -to [get_clocks rpc_clk]
set_false_path -from [get_clocks rpc_clk] -to [get_clocks clkfbout_xilinx_phase_shift_90]

## FMC mapping

### CS_N
# CS_N - FPGA J11 - FMC  K31
set_property -dict {PACKAGE_PIN J11 IOSTANDARD LVCMOS12} [get_ports rpc_cs_no]

### STB
# STB - FPGA H12 - FMC  K35
set_property -dict {PACKAGE_PIN H12 IOSTANDARD LVCMOS12} [get_ports rpc_stb_o]

### CLK
# CLK - FPGA D12 - FMC  K37
set_property -dict {PACKAGE_PIN D12 IOSTANDARD LVCMOS12} [get_ports rpc_clk_o]

### CLK_N
# CLK_N - FPGA D13 - FMC  K38
set_property -dict {PACKAGE_PIN D13 IOSTANDARD LVCMOS12} [get_ports rpc_clk_no]

### DQS
# DQS - FPGA G13 - FMC  K25
set_property -dict {PACKAGE_PIN G13 IOSTANDARD LVCMOS12} [get_ports rpc_dqs]

### DQS_N
# DQS_N - FPGA F13 - FMC  K26
set_property -dict {PACKAGE_PIN F13 IOSTANDARD LVCMOS12} [get_ports rpc_dqsn]

### DB_0
# DB_0 - FPGA B12 - FMC  E31
set_property -dict {PACKAGE_PIN B12 IOSTANDARD LVCMOS12} [get_ports rpc_db0]

### DB_1
# DB_1 - FPGA C15 - FMC  E27
set_property -dict {PACKAGE_PIN C15 IOSTANDARD LVCMOS12} [get_ports rpc_db1]

### DB_2
# DB_2 - FPGA L12 - FMC  J33
set_property -dict {PACKAGE_PIN L12 IOSTANDARD LVCMOS12} [get_ports rpc_db2]

### DB_3
# DB_3 - FPGA C12 - FMC  E30
set_property -dict {PACKAGE_PIN C12 IOSTANDARD LVCMOS12} [get_ports rpc_db3]

### DB_4
# DB_4 - FPGA C11 - FMC  J31
set_property -dict {PACKAGE_PIN C11 IOSTANDARD LVCMOS12} [get_ports rpc_db4]

### DB_5
# DB_5 - FPGA D11 - FMC  J30
set_property -dict {PACKAGE_PIN D11 IOSTANDARD LVCMOS12} [get_ports rpc_db5]

### DB_6
# DB_6 - FPGA A13 - FMC  J28
set_property -dict {PACKAGE_PIN A13 IOSTANDARD LVCMOS12} [get_ports rpc_db6]

### DB_7
# DB_7 - FPGA J12 - FMC  K32
set_property -dict {PACKAGE_PIN J12 IOSTANDARD LVCMOS12} [get_ports rpc_db7]

### DB_8
# DB_8 - FPGA E11 - FMC  E34
set_property -dict {PACKAGE_PIN E11 IOSTANDARD LVCMOS12} [get_ports rpc_db8]

### DB_9
# DB_9 - FPGA H11 - FMC  K34
set_property -dict {PACKAGE_PIN H11 IOSTANDARD LVCMOS12} [get_ports rpc_db9]

### DB_10
# DB_10 - FPGA L13 - FMC  J34
set_property -dict {PACKAGE_PIN L13 IOSTANDARD LVCMOS12} [get_ports rpc_dba]

### DB_11
# DB_11 - FPGA F11 - FMC  E33
set_property -dict {PACKAGE_PIN F11 IOSTANDARD LVCMOS12} [get_ports rpc_dbb]

### DB_12
# DB_12 - FPGA C14 - FMC  E37
set_property -dict {PACKAGE_PIN C14 IOSTANDARD LVCMOS12} [get_ports rpc_dbc]

### DB_13
# DB_13 - FPGA D14 - FMC  E36
set_property -dict {PACKAGE_PIN D14 IOSTANDARD LVCMOS12} [get_ports rpc_dbd]

### DB_14
# DB_14 - FPGA E15 - FMC  J37
set_property -dict {PACKAGE_PIN E15 IOSTANDARD LVCMOS12} [get_ports rpc_dbe]

### DB_15
# DB_15 - FPGA E14 - FMC  J36
set_property -dict {PACKAGE_PIN E14 IOSTANDARD LVCMOS12} [get_ports rpc_dbf]

# TODO @ale: fix this hack for clock cells placement on dqs/dqsn
set_property CLOCK_DEDICATED_ROUTE FALSE [get_nets i_rpc_fpga_top/i_iobuf_rpc/i_dqs_iobuf/O]
set_property CLOCK_DEDICATED_ROUTE FALSE [get_nets i_rpc_fpga_top/i_iobuf_rpc/i_dqsn_iobuf/O]
