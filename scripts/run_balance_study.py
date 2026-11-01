#!/usr/bin/env python3
"""Build and run the precommitted compiled study, retaining raw data and source hashes."""
import hashlib
import json
from pathlib import Path
import subprocess
import time
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parents[1]
RESULTS = ROOT / "experiments/results"


def hashes():
    paths = sorted((ROOT / "Rpg").rglob("*.lean"))
    paths += [ROOT / p for p in ("BalanceStudy.lean", "experiments/plan.json", "lean-toolchain", "lake-manifest.json", "lakefile.toml")]
    paths += sorted((ROOT / "experiments/adventures").glob("*.json"))
    return {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}


def main():
    subprocess.run(["lake", "build", "balance-study"], cwd=ROOT, check=True)
    frozen = hashes()
    plan = json.loads((ROOT / "experiments/plan.json").read_text())
    RESULTS.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    started_utc = datetime.now(timezone.utc).isoformat()
    temporary = RESULTS / "observations.jsonl.tmp"
    with temporary.open("w") as out:
        subprocess.run([str(ROOT / ".lake/build/bin/balance-study")], cwd=ROOT,
                       stdout=out, check=True, timeout=900)
    elapsed = time.monotonic() - started
    if hashes() != frozen:
        raise RuntimeError("Study inputs changed during measurement; results are incomplete")
    records = [json.loads(line) for line in temporary.read_text().splitlines()]
    assert [r["variant"] for r in records] == plan["variants"]
    for row in records:
        life = row["lifetime"]
        assert life["games"] == plan["lifetime_games_per_variant"]
        assert sum(life["deaths"]) + sum(life["endings"]) + sum(life["censored"]) + life["invalid"] == life["games"]
        assert life["invalid"] == 0, f"Invalid trajectories in {row['variant']}"
        assert [b["seed"] for b in row["batches"]] == plan["admission_seeds"]
        assert all(b["games"] == plan["admission_games_per_batch"] for b in row["batches"])
    temporary.replace(RESULTS / "observations.jsonl")
    metadata = {"started_utc": started_utc, "elapsed_seconds": elapsed,
                "git_parent": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
                "command": "python3 scripts/run_balance_study.py", "source_sha256": frozen,
                "plan_sha256": frozen["experiments/plan.json"],
                "note": "Exploratory comparisons, not a source-bound admission certificate or simultaneous confidence claim."}
    (RESULTS / "metadata.json").write_text(json.dumps(metadata, indent=2) + "\n")
    print(f"Study complete: {len(records)} variants in {elapsed:.2f}s; raw observations and source hashes saved.")


if __name__ == "__main__":
    main()
