vsim rpc_controller_tb -t 1ps -voptargs=+acc -classdebug

set StdArithNoWarnings 1
set NumericStdNoWarnings 1
log -r /*

delete wave *
