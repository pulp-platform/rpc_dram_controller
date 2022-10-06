## timing constraints

# 50 MHz differential clock for Genesys 2 FPGA
create_clock -add -name rpc_clk -period 20.00 -waveform {0 2.5} [get_ports clkp_i]
set_property CLOCK_DEDICATED_ROUTE ANY_CMT_COLUMN [get_nets clkp_i]

# rst_n
set_max_delay -from [get_ports rst_ni] [expr 0.7*5]

## in/out constraints

### CS_N
# CS_N - FPGA B23 - FMC  H19
set_property -dict {PACKAGE_PIN B23 IOSTANDARD LVCMOS12} [get_ports rpc_csn]

### STB
# STB - FPGA A23 - FMC  H20
set_property -dict {PACKAGE_PIN A23 IOSTANDARD LVCMOS12} [get_ports rpc_stb]

### CLK
# CLK - FPGA E23 - FMC  G18
set_property -dict {PACKAGE_PIN E23 IOSTANDARD LVCMOS12} [get_ports rpc_clk]

### CLK_N
# CLK_N - FPGA D23 - FMC  G19
set_property -dict {PACKAGE_PIN D23 IOSTANDARD LVCMOS12} [get_ports rpc_clkn]

### DQS
# DQS - FPGA F25 - FMC  H13
set_property -dict {PACKAGE_PIN F25 IOSTANDARD LVCMOS12} [get_ports rpc_dqs]

### DQS_N
# DQS_N - FPGA E25 - FMC  H14
set_property -dict {PACKAGE_PIN E25 IOSTANDARD LVCMOS12} [get_ports rpc_dqsn]

### DB_0
# DB_0 - FPGA E24 - FMC  D17
set_property -dict {PACKAGE_PIN E24 IOSTANDARD LVCMOS12} [get_ports rpc_db0]

### DB_1
# DB_1 - FPGA D24 - FMC  D18
set_property -dict {PACKAGE_PIN D24 IOSTANDARD LVCMOS12} [get_ports rpc_db1]

### DB_2
# DB_2 - FPGA F26 - FMC  G15
set_property -dict {PACKAGE_PIN F26 IOSTANDARD LVCMOS12} [get_ports rpc_db2]

### DB_3
# DB_3 - FPGA E26 - FMC  G16
set_property -dict {PACKAGE_PIN E26 IOSTANDARD LVCMOS12} [get_ports rpc_db3]

### DB_4
# DB_4 - FPGA B27 - FMC  C14
set_property -dict {PACKAGE_PIN B27 IOSTANDARD LVCMOS12} [get_ports rpc_db4]

### DB_5
# DB_5 - FPGA A27 - FMC  C15
set_property -dict {PACKAGE_PIN A27 IOSTANDARD LVCMOS12} [get_ports rpc_db5]

### DB_6
# DB_6 - FPGA H21 - FMC  H22
set_property -dict {PACKAGE_PIN H21 IOSTANDARD LVCMOS12} [get_ports rpc_db6]

### DB_7
# DB_7 - FPGA H22 - FMC  H23
set_property -dict {PACKAGE_PIN H22 IOSTANDARD LVCMOS12} [get_ports rpc_db7]

### DB_8
# DB_8 - FPGA G22 - FMC  G21
set_property -dict {PACKAGE_PIN G22 IOSTANDARD LVCMOS12} [get_ports rpc_db8]

### DB_9
# DB_9 - FPGA F22 - FMC  G22
set_property -dict {PACKAGE_PIN F22 IOSTANDARD LVCMOS12} [get_ports rpc_db9]

### DB_10
# DB_10 - FPGA D22 - FMC  G27
set_property -dict {PACKAGE_PIN D22 IOSTANDARD LVCMOS12} [get_ports rpc_dba]

### DB_11
# DB_11 - FPGA C22 - FMC  G28
set_property -dict {PACKAGE_PIN C22 IOSTANDARD LVCMOS12} [get_ports rpc_dbb]

### DB_12
# DB_12 - FPGA F21 - FMC  D20
set_property -dict {PACKAGE_PIN F21 IOSTANDARD LVCMOS12} [get_ports rpc_dbc]

### DB_13
# DB_13 - FPGA E21 - FMC  D21
set_property -dict {PACKAGE_PIN E21 IOSTANDARD LVCMOS12} [get_ports rpc_dbd]

### DB_14
# DB_14 - FPGA D17 - FMC  C22
set_property -dict {PACKAGE_PIN D17 IOSTANDARD LVCMOS12} [get_ports rpc_dbe]

### DB_15
# DB_15 - FPGA D18 - FMC  C23
set_property -dict {PACKAGE_PIN D18 IOSTANDARD LVCMOS12} [get_ports rpc_dbf]

# TODO @ale: fix this hack for clock cells placement on dqs/dqsn
set_property CLOCK_DEDICATED_ROUTE FALSE [get_nets i_rpc_wrap/i_iobuf_rpc/i_dqs_iobuf/O]
set_property CLOCK_DEDICATED_ROUTE FALSE [get_nets i_rpc_wrap/i_iobuf_rpc/i_dqsn_iobuf/O]
