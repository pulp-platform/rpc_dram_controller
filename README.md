# Reduced Pin Count (RPC) DRAM Controller

This repository contains a free and open-source fully synthesizable controller for Etron's
Reduced Pin Count (RPC) DRAM chips. It is part of the PULP ecosystem.

## TODOs (there are many more)
* [ ] Flatten sources; why are there so many files and three levels of directories?
* [ ] Move timers to common cells
* [ ] Use generated register files [https://github.com/pulp-platform/register_interface](https://github.com/pulp-platform/register_interface)
* [ ] Clean sources: harmonize comment style, indentation, etc.
* [ ] Make it more technology independent; remove delay lines e.g.
* [ ] Rework AXI part of the design; use a more dataflow oriented scheme
* [ ] Overall code cleanup and improvements
* [ ] Device a FOSS verification strategy
* [ ] Make it work on Xilinx FPGAs
* [ ] Merge packages into one `rpc_dram_controller` package
* [ ] Properly prefix all files, modules, types
* [ ] Clearly divide controller and AXI interface. Harden interface between the two parts.
* [ ] Adapt `Bender.yml` to use Levels to read the sources
