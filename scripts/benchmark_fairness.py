#!/usr/bin/env python3
"""Replay the recorded 5,000-game batches; verify counts and exact intervals."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import time


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    recorded_path = root / "docs/reports/fairness-5000-ten.json"
    recorded = json.loads(recorded_path.read_text())
    output = args.output.resolve()
    if output == recorded_path:
        parser.error("Preserve the original measurements; choose a new output file.")
    binary = root / ".lake/build/bin/benchmark-fairness"
    if not binary.is_file():
        parser.error("First run: lake build benchmark-fairness")

    reports = []
    for run, expected in zip(recorded["plan"]["runs"], recorded["reports"]):
        source = root / run["archivedInput"]
        if hashlib.sha256(source.read_bytes()).hexdigest() != run["sha256"]:
            raise RuntimeError(f"Input changed: {source}")
        start = time.perf_counter()
        result = subprocess.run(
            [str(binary), str(source), str(run["seed"]), "5000"],
            cwd=root, text=True, capture_output=True, check=True,
        )
        wall_seconds = time.perf_counter() - start
        actual = json.loads(result.stdout)
        for key in ("games", "horizon", "trials", "deaths", "rows", "meetsAllBands"):
            if actual[key] != expected[key]:
                raise RuntimeError(f"{run['difficulty']}: recorded {key} changed")
        coverage = [(x["scene"], x["games"]) for x in actual["coverage"]]
        reference = [(x["scene"], x["games"]) for x in expected["coverage"]]
        if coverage != reference:
            raise RuntimeError(f"{run['difficulty']}: coverage changed")
        actual["processWallSeconds"] = wall_seconds
        reports.append(actual)
        print(json.dumps({
            "difficulty": run["difficulty"], "games": actual["games"],
            "choices": actual["choicesCovered"], "replayMatches": True,
            "processWallSeconds": wall_seconds,
            "meetsAllBands": actual["meetsAllBands"],
        }), flush=True)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps({
        "note": "Replay timings, not new independent statistical evidence.",
        "reports": reports,
    }, indent=2) + "\n")


if __name__ == "__main__":
    main()
