PROJECT ?= rpc
BOARD ?= genesys2
XILINX_PART ?= xc7k325tffg900-2
XILINX_BOARD ?= digilentinc.com:genesys2:part0:1.1

out := out
bit := $(out)/rpc_controller_top_xilinx.bit
mcs := $(out)/neo_top_xilinx.mcs


VIVADOENV ?=	PROJECT=$(PROJECT)				\
				BOARD=$(BOARD)					\
				XILINX_PART=$(XILINX_PART)		\
				XILINX_BOARD=$(XILINX_BOARD)	\
				BIT=$(bit)

VIVADO ?= vitis-2020.2
VIVADOFLAGS ?= -nojournal -mode gui -source scripts/prologue.tcl

ip-dir := xilinx
ips := xilinx_phase_shift_90.xci

all: $(mcs)

# Generate mcs from bitstream
$(mcs) : $(bit)
	$(VIVADOENV) $(VIVADO) vivado $(VIVADOFLAGS) -source scripts/write_cfgmem.tcl -tclargs $@ $^

$(bit) : $(ips)
	@mkdir -p $(out)
	$(VIVADOENV) $(VIVADO) vivado $(VIVADOFLAGS) -source scripts/run.tcl
	cp $(PROJECT).runs/impl_1/$(PROJECT)* ./$(out)

$(ips):
	@echo "Generating IP $(basename $@)"
	cd $(ip-dir)/$(basename $@) && $(MAKE) clean && $(VIVADOENV) VIVADO=$(VIVADO) $(MAKE)
	cp $(ip-dir)/$(basename $@)/$(basename $@).srcs/sources_1/ip/$(basename $@)/$@ $@

gui:
	@mkdir -p $(out)
	@echo "Starting $(vivado) GUI"
	@$(VIVADOENV) $(VIVADO) vivado -nojournal -mode gui $(PROJECT).xpr &

program: $(bit)
	@echo "Programming board $(BOARD) ($(XILINX_PART))"
	$(VIVADOENV) $(VIVADO) vivado $(VIVADOFLAGS) -source scripts/program.tcl

clean:
	rm -rf *.sim *.log *.jou *.str *.mif *.xci *.xpr $(out) $(PROJECT).cache $(PROJECT).hw $(PROJECT).ip_user_files

.PHONY:
	clean
