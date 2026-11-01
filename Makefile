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

# Build, then replay every proof through the Lean kernel. This fails on `sorry` and on new axioms.
check: build
	lake check

# Show the checker rejecting the cheating Adventures.
cheats:
	lake exe rpg --cheats

# Fixed game batch with exact binomial intervals and Lean-proved coverage.
.PHONY: validate
validate:
	lake exe validate
