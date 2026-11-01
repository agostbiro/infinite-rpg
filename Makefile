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

# Fast diagnostics only; this command never creates a fairness proof.
.PHONY: audit
audit:
	lake exe audit $(if $(SAMPLES),--samples $(SAMPLES),) $(if $(SEED),--seed $(SEED),)

# Frozen validation protocol backed by the Lean statistical risk theorem.
.PHONY: validate
validate:
	lake exe validate
