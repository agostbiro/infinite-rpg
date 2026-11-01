.PHONY: install run run-fake build check check-rules cheats validate comparator agree test-spatial test-browser

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
# Set ANTHROPIC_API_KEY to let the Player ask the DM for an Adventure with a Wish, or for a rule
# change during play.
# Pass a seed to replay the first game with the same dice: make run SEED=7
run: build
	@URL=http://$(HOST):$(PORT)/; \
	echo "Open $$URL in your browser."; \
	( sleep 1; (command -v xdg-open >/dev/null && xdg-open $$URL) || (command -v open >/dev/null && open $$URL) || true ) >/dev/null 2>&1 & \
	exec .lake/build/bin/rpg --host $(HOST) --port $(PORT) $(if $(SEED),--seed $(SEED),)

# Test hook: run the game with recorded API replies from tests/fake-api instead of the Claude API.
# No API key is needed. There is no recorded Wish now, so a Wish fails with "no recorded reply"
# (docs/follow-ups.md). The saved Adventures can be played.
run-fake: build
	@echo "TEST MODE: Wishes use recorded replies from tests/fake-api."
	RPG_FAKE_API=tests/fake-api .lake/build/bin/rpg --host $(HOST) --port $(PORT) $(if $(SEED),--seed $(SEED),)

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
	@if grep -rnE '$(FORBIDDEN)' Rpg/Adventures; then \
	  echo "error: a forbidden word is used above"; exit 1; fi
	@$(MAKE) --no-print-directory check-rules

# People own the rules files of each Adventure. A DM may not change them.
# During play, the DM can propose a live change: equipment, combat effects, and new or replaced
# Scenes that are not visited yet. The core rules stay the same. The server installs a change only
# after the checker and the balance check pass (docs/adr/0005-live-rule-changes.md).
# Each Rules.lean under Rpg/Adventures may only say `def rules : RuleSet := {}` (the default rules),
# unless a person puts its path on RULES_ALLOW. No other Adventure file may name `RuleSet` or
# change a rules value with `{ ... with ... }`.
RULES_ALLOW ?=
RULES_LINE = ^(import Rpg\.RuleSet|namespace Rpg\.[A-Za-z]+|end Rpg\.[A-Za-z]+|def rules : RuleSet := \{\}|/--.*-/)?$$
check-rules:
	@bad=0; for f in $$(find Rpg/Adventures -name Rules.lean); do \
	  case " $(RULES_ALLOW) " in *" $$f "*) continue;; esac; \
	  if grep -nvE '$(RULES_LINE)' $$f; then echo "error: $$f changes the rules (see check-rules in the Makefile)"; bad=1; fi; \
	done; \
	if grep -rnE 'RuleSet|rules with' Rpg/Adventures --include=*.lean | grep -v '/Rules.lean:'; then \
	  echo "error: an Adventure file names RuleSet or changes a rules value"; bad=1; fi; \
	exit $$bad

# Test the parts of the 3D page that have no browser in them: the objects for the inputs, the walk,
# and the playback of Reports. This needs only Node.js.
test-spatial:
	node --test tests/spatial.test.js tests/playback.test.js tests/environment.test.js tests/travel.test.js

# The port of the test server for the browser test. It is not PORT, so the test never talks to a
# game that a Player has open.
TEST_PORT ?= 8093

# Play a Wish in a real browser (Playwright), with the recorded replies in tests/fake-api.
# Run `npm ci` first. Playwright uses its own browser files; it does not download anything else.
test-browser: build
	TEST_PORT=$(TEST_PORT) npx playwright test

# Show the checker rejecting the cheating Adventures.
cheats:
	lake exe cheats

# Run the balance check on the built-in Adventure (Lafayette at Barren Hill), and print each row
# with its interval and range. It uses the fixed validation seed. To try another seed:
# make validate SEED=7
validate:
	lake exe validate $(if $(SEED),--seed $(SEED),)

# Check that the main theorems in Comparator/Proofs.lean prove the statements in
# Comparator/Statements.lean, pass the kernel, and use only the standard axioms (see comparator.json).
comparator:
	lake comparator

# Compare the exact Fight model with the simulator on the Fights of the test Adventure. This takes
# minutes.
agree:
	lake exe agree
