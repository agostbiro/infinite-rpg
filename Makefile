.PHONY: install run build check check-pictures cheats

# The port of the game server: make run PORT=9000
PORT ?= 8080
# The IPv4 address the game server listens on. The default lets only this machine connect.
# To play from the host of a VM (virtual machine), use the VM's address: make run HOST=10.211.55.6
HOST ?= 127.0.0.1

# Install the Lean toolchain named in lean-toolchain, then build the game and check every proof.
install:
	@command -v elan >/dev/null || (curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none)
	elan toolchain install $$(cat lean-toolchain)
	$(MAKE) check

# Build, start the game server on $(HOST), and open the page in the browser. Ctrl-C stops it.
# Pass a seed to replay the first game with the same dice: make run SEED=7
run: build
	@URL=http://$(HOST):$(PORT)/; \
	echo "Open $$URL in your browser."; \
	( sleep 1; (command -v xdg-open >/dev/null && xdg-open $$URL) || (command -v open >/dev/null && open $$URL) || true ) >/dev/null 2>&1 & \
	exec .lake/build/bin/rpg --host $(HOST) --port $(PORT) $(if $(SEED),--seed $(SEED),)

build:
	lake build

# Words that can make compiled code differ from what the proofs are about.
# The DM may not use them in Adventure or Character files.
# `@[` and `attribute [` catch every attribute, such as `@[implemented_by]`.
FORBIDDEN = \b(implemented_by|extern|unsafe|initialize|builtin_initialize|macro|macro_rules|syntax|elab|set_option)\b|@\[|attribute *\[

# The folder of Pictures. The DM writes these SVG files.
PICTURES ?= web/pictures

# Build, then replay every proof through the Lean kernel. This fails on `sorry` and on new axioms.
# It also fails if a DM file uses a forbidden word, or a Picture uses a forbidden SVG feature.
check: build
	lake check
	@if grep -rnE '$(FORBIDDEN)' Rpg/Adventures Rpg/Characters.lean; then \
	  echo "error: a forbidden word is used above"; exit 1; fi
	@$(MAKE) --no-print-directory check-pictures

# Pictures may not run code or load things from elsewhere. scripts/check_pictures.py parses each
# SVG file and rejects scripts, event handlers, outside links, and more (see its docstring).
# The page shows Pictures only through <img> tags, which run no scripts; this is a second guard.
check-pictures:
	python3 scripts/check_pictures.py $(PICTURES)

# Show the checker rejecting the cheating Adventures.
cheats:
	lake exe cheats
