.PHONY: install run build check cheats

# Install the Lean toolchain named in lean-toolchain, then build the game and check every proof.
install:
	@command -v elan >/dev/null || (curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none)
	elan toolchain install $$(cat lean-toolchain)
	$(MAKE) check

# Play the game. Pass a seed to replay a game: make run SEED=7
run:
	lake exe rpg $(if $(SEED),--seed $(SEED),)

build:
	lake build

# Words that can make compiled code differ from what the proofs are about.
# The DM may not use them in Adventure or Character files.
# `@[` and `attribute [` catch every attribute, such as `@[implemented_by]`.
FORBIDDEN = \b(implemented_by|extern|unsafe|initialize|builtin_initialize|macro|macro_rules|syntax|elab|set_option)\b|@\[|attribute *\[

# Build, then replay every proof through the Lean kernel. This fails on `sorry` and on new axioms.
# It also fails if a DM file uses a forbidden word.
check: build
	lake check
	@if grep -rnE '$(FORBIDDEN)' Rpg/Adventures Rpg/Characters.lean; then \
	  echo "error: a forbidden word is used above"; exit 1; fi

# Show the checker rejecting the cheating Adventures.
cheats:
	echo 2 | lake exe rpg
