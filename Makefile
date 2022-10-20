# Copyright 2022 ETH Zurich and University of Bologna
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

TARGET =? .
TARGET_ABS    = $(abspath $(lastword $(TARGET)))
REPORT        ?= 0
LINT_LOGS_DIR = $(ROOT_DIR)/util/verible/rpt

# Verible
# Formatter

# module_net_variable_alignment flush-left is not optimal but better than the
# ugly bracket expansion
.PHONY: verible-format
## Call verible-verilog-format tool
verible-format:
	find $(TARGET_ABS) -name '*.sv' -exec sh -c \
	'$(ROOT_DIR)/util/verible/bin/verible-verilog-format \
	--wrap_spaces 2 \
	--assignment_statement_alignment align \
	--module_net_variable_alignment flush-left \
	--named_parameter_alignment align \
	--named_port_alignment align \
	--port_declarations_alignment preserve \
	--inplace $$1' -- {} \;

# Syntax checker
.PHONY: verible-syntax
## Call verible-verilog-syntax tool
verible-syntax:
	find $(TARGET_ABS) -name '*.sv' -exec sh -c \
	'$(ROOT_DIR)/util/verible/bin/verible-verilog-syntax $$1' -- {} \;

# Linter
.PHONY: verible-lint
## Call verible-verilog-lint tool
verible-lint:
ifeq ($(REPORT), 1)
	find $(TARGET_ABS) -name '*.sv' -exec sh -c \
	'$(ROOT_DIR)/util/verible/bin/verible-verilog-lint \
		--rules_config $(ROOT_DIR)/util/verible/rules.vbl $$1 > \
		$(LINT_LOGS_DIR)/$$(basename $${1%.sv}-lint.log)' \
		-- {} \;
	$(ROOT_DIR)/util/verible/parse-lint-report.py --repdir $(LINT_LOGS_DIR)
	$(RM) $(LINT_LOGS_DIR)/*.log
else
	find $(TARGET_ABS) -name '*.sv' -exec sh -c \
	'$(ROOT_DIR)/util/verible/bin/verible-verilog-lint \
		--rules_config $(ROOT_DIR)/util/verible/rules.vbl $$1' \
		-- {} \;
endif

.PHONY: verible-all
## Call all supported verible tools on target
verible-all: verible-syntax verible-lint verible-format

.PHONY: verible-update
## Format unstaged/uncommitted modifications
verible-update:
	$(ROOT_DIR)/util/verible/bin/git-verible-verilog-format.sh && git add -u

.PHONY: verible-update-interactive
## Format unstaged/uncommitted modifications interactively
verible-update-interactive:
	$(ROOT_DIR)/util/verible/bin/git-verible-verilog-format.sh

.PHONY: verible-clean
verible-clean:
	$(RM) -r $(ROOT_DIR)/util/verible/rpt

