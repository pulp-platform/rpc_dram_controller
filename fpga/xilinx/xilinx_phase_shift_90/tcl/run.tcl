set partNumber $::env(XILINX_PART)
set boardName  $::env(XILINX_BOARD)

set ipName xilinx_phase_shift_90

create_project $ipName . -force -part $partNumber
set_property board_part $boardName [current_project]

create_ip -name clk_wiz -vendor xilinx.com -library ip -module_name $ipName

set_property -dict [list CONFIG.USE_PHASE_ALIGNMENT {false} \
                    CONFIG.USE_INCLK_SWITCHOVER {false} \
                    CONFIG.PRIM_IN_FREQ {50.000} \
                    CONFIG.NUM_OUT_CLKS {1} \
                    CONFIG.CLKOUT2_USED {false} \
                    CONFIG.CLKOUT3_USED {false} \
                    CONFIG.CLKOUT4_USED {false} \
                    CONFIG.CLKOUT1_REQUESTED_OUT_FREQ {50.000} \
                    CONFIG.CLKOUT1_REQUESTED_PHASE {90.000} \
                    CONFIG.CLKIN1_JITTER_PS {50.0}
                   ] [get_ips $ipName]


generate_target {instantiation_template} [get_files ./$ipName.srcs/sources_1/ip/$ipName/$ipName.xci]
generate_target all [get_files  ./$ipName.srcs/sources_1/ip/$ipName/$ipName.xci]
create_ip_run [get_files -of_objects [get_fileset sources_1] ./$ipName.srcs/sources_1/ip/$ipName/$ipName.xci]
launch_run -jobs 8 ${ipName}_synth_1
wait_on_run ${ipName}_synth_1
