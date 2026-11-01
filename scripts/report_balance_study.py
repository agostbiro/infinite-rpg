#!/usr/bin/env python3
"""Make reproducible CSV tables, standard plots, and a self-contained HTML study report."""
import csv
from fractions import Fraction
import html
import json
import math
import os
from pathlib import Path

os.environ.setdefault("MPLCONFIGDIR", "/private/tmp/rpg-study-matplotlib")
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from matplotlib.ticker import PercentFormatter

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "experiments/results"
COLORS = ["#64748b", "#2563eb", "#7c3aed", "#16a34a", "#dc2626", "#0d9488", "#d97706"]
SHORT = ["Original Lighthouse", "Original + meta rules", "Expanded Lighthouse", "Unchecked superweapon", "Harsh opposition", "No combat", "Silver Acorn"]


def quantile(histogram, p):
    total = sum(histogram)
    if not total:
        return None
    threshold = math.ceil(p * total)
    seen = 0
    for turn, count in enumerate(histogram):
        seen += count
        if seen >= threshold:
            return turn


def average(histogram):
    count = sum(histogram)
    return sum(t * n for t, n in enumerate(histogram)) / count if count else None


def csv_file(name, rows):
    with (OUT / name).open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0]), lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)


def save(fig, name):
    fig.savefig(OUT / f"{name}.svg", bbox_inches="tight")
    fig.savefig(OUT / f"{name}.png", dpi=180, bbox_inches="tight")
    plt.close(fig)
    svg_path = OUT / f"{name}.svg"
    svg = "\n".join(line.rstrip() for line in svg_path.read_text().splitlines()) + "\n"
    svg_path.write_text(svg)
    return svg[svg.index("<svg"):]


def table(headers, rows):
    def escape(value):
        return html.escape(str(value))
    return "<table><thead><tr>" + "".join(f"<th>{escape(x)}</th>" for x in headers) + "</tr></thead><tbody>" + "".join("<tr>" + "".join(f"<td>{escape(x)}</td>" for x in row) + "</tr>" for row in rows) + "</tbody></table>"


def main():
    plan = json.loads((ROOT / "experiments/plan.json").read_text())
    meta = json.loads((OUT / "metadata.json").read_text())
    records = [json.loads(line) for line in (OUT / "observations.jsonl").read_text().splitlines()]
    assert [r["variant"] for r in records] == plan["variants"]
    stats, admissions, trajectories, profiles = [], [], [], []
    for r in records:
        life = r["lifetime"]
        deaths, ends, censored = map(sum, (life["deaths"], life["endings"], life["censored"]))
        terminal = [a+b for a, b in zip(life["deaths"], life["endings"])]
        stats.append({"variant": r["variant"], "label": r["label"], "games": life["games"],
                      "deaths": deaths, "death_rate": deaths/life["games"], "successful_endings": ends,
                      "mean_turns_given_death": average(life["deaths"]), "median_turns_given_death": quantile(life["deaths"], .5),
                      "death_turn_p10": quantile(life["deaths"], .1), "death_turn_p90": quantile(life["deaths"], .9),
                      "mean_turns_given_termination": average(terminal), "censored": censored, "invalid": life["invalid"]})
        for turn, (dead, ended, unknown) in enumerate(zip(life["deaths"], life["endings"], life["censored"])):
            trajectories.append({"variant": r["variant"], "turn": turn, "deaths": dead, "endings": ended, "censored": unknown})
        for b in r["batches"]:
            for p in b["policies"]:
                admissions.append({"variant": r["variant"], "seed": b["seed"], "games": b["games"],
                                   "aborted": b["aborted"], "policy": p["name"], "retention": p["retention"],
                                   "shape": p["shape"], "tolerance": p["tolerance"], "delta": p["delta"], "passed": p["passed"]})
        for row in range(plan["balance_horizon"] + 1):
            trials = sum(b["trials"][row] for b in r["batches"])
            dead = sum(b["deaths"][row] for b in r["batches"])
            profiles.append({"variant": r["variant"], "row": row, "death_turn": row+1,
                             "conditioning_turn": max(0, row-1), "trials": trials, "deaths": dead,
                             "observed_probability": dead/trials if trials else None})
    csv_file("lifetime-statistics.csv", stats)
    csv_file("policy-admissions.csv", admissions)
    csv_file("turn-counts.csv", trajectories)
    csv_file("conditional-frequencies.csv", profiles)
    plt.rcParams.update({"font.size": 10, "axes.spines.top": False, "axes.spines.right": False,
                         "axes.titleweight": "bold", "figure.facecolor": "white"})
    max_turn = max(t for r in records for t, n in enumerate(r["lifetime"]["deaths"]) if n)
    max_turn = max(max_turn, max(t for r in records for t, n in enumerate(r["lifetime"]["endings"]) if n))
    fig, ax = plt.subplots(figsize=(10, 5.2))
    for r, color, label in zip(records, COLORS, SHORT):
        values = np.cumsum(r["lifetime"]["deaths"]) / r["lifetime"]["games"]
        ax.step(range(max_turn+1), values[:max_turn+1], where="post", color=color, label=label,
                linewidth=2.7 if r["variant"] == "expanded_lighthouse" else 1.8)
    ax.set(title="Observed deaths over the game", xlabel="Scene-choice turn (including its entire fight)", ylabel="Fraction of all games ending in death")
    ax.set_ylim(-.015, 1.015)
    ax.yaxis.set_major_formatter(PercentFormatter(1))
    ax.set_xticks(range(max_turn+1))
    ax.grid(alpha=.15)
    ax.legend(loc="upper left", fontsize=9)
    deaths_svg = save(fig, "death-curves")

    matrix = np.array([[sum(b["policies"][i]["passed"] for b in r["batches"]) for i in range(len(plan["policies"]))] for r in records])
    policy_labels = ["Default\nq=.95, k=2", "Earlier\nq=.90", "Later\nq=.98", "Geometric\nk=1", "Steeper\nk=3", "Tighter\n±.10", "Wider\n±.30", "90%\nconfidence", "99%\nconfidence"]
    fig, ax = plt.subplots(figsize=(12, 5.2))
    image = ax.imshow(matrix, cmap="Blues", vmin=0, vmax=len(plan["admission_seeds"]), aspect="auto")
    ax.set_xticks(range(len(policy_labels)), policy_labels, fontsize=9)
    ax.set_yticks(range(len(SHORT)), SHORT)
    ax.set_title("Admission changes when the balance parameters change", pad=18)
    for y in range(len(records)):
        for x in range(len(policy_labels)):
            ax.text(x, y, f"{matrix[y,x]}/5", ha="center", va="center", color="white" if matrix[y,x] >= 3 else "#111827", fontweight="bold")
    fig.colorbar(image, ax=ax, label="Passing batches out of five (1,000 games per batch)", ticks=range(6), shrink=.8)
    admission_svg = save(fig, "policy-admissions")

    fig, ax = plt.subplots(figsize=(10, 5))
    means = [s["mean_turns_given_death"] or 0 for s in stats]
    ax.barh(SHORT, means, color=COLORS)
    for i, s in enumerate(stats):
        mean = s["mean_turns_given_death"]
        label = "No observed deaths" if mean is None else f"{mean:.2f} turns; {s['death_rate']:.1%} die"
        ax.text((mean or 0)+.07, i, label, va="center", fontsize=9)
    ax.invert_yaxis()
    ax.set_xlim(0, max(means)+3)
    ax.set(title="Turns before death, among characters who died", xlabel="Mean scene-choice turns; successful endings are excluded")
    ax.grid(axis="x", alpha=.15)
    time_svg = save(fig, "turns-before-death")

    target_rows = []
    for p in plan["policies"]:
        q, shape, tolerance = Fraction(p["retention"]), p["shape"], Fraction(p["tolerance"])
        targets = [1-q] + [(q**((t+1)**shape)-q**((t+2)**shape))/(q**(t**shape)) for t in range(plan["balance_horizon"])]
        target_rows.extend({"policy":p["name"], "row":i, "target":str(v), "lower_band":str(max(0,v-tolerance)), "upper_band":str(min(1,v+tolerance))} for i,v in enumerate(targets))
    csv_file("policy-targets.csv", target_rows)
    default_targets = [r for r in target_rows if r["policy"] == "default"]
    fig, ax = plt.subplots(figsize=(10, 5.2))
    x = np.arange(1, plan["balance_horizon"]+2)
    target = [float(Fraction(r["target"])) for r in default_targets]
    lo = [float(Fraction(r["lower_band"])) for r in default_targets]
    hi = [float(Fraction(r["upper_band"])) for r in default_targets]
    ax.fill_between(x, lo, hi, color="#e2e8f0", label="Default allowed band (±20 percentage points)")
    ax.plot(x, target, "k--", label="Discrete Weibull target")
    for r, color, label in zip(records, COLORS, SHORT):
        if r["variant"] not in ("original_lighthouse", "expanded_lighthouse", "unchecked_power", "harsh_opposition"):
            continue
        values = [p["observed_probability"] for p in profiles if p["variant"] == r["variant"]]
        ax.plot(x, values, marker="o", color=color, label=label)
    ax.set(title="Why the default balance check accepts or rejects different games", xlabel="Death turn (first turn, then t+2 conditional on active at t)", ylabel="Observed conditional death frequency")
    ax.yaxis.set_major_formatter(PercentFormatter(1))
    ax.legend(fontsize=8)
    ax.grid(alpha=.15)
    frequency_svg = save(fig, "conditional-frequencies")

    def fmt(value):
        return "—" if value is None else f"{value:.2f}"
    stat_rows = [[label, s["games"], f"{s['death_rate']:.2%}", fmt(s["mean_turns_given_death"]),
                  s["median_turns_given_death"] or "—", fmt(s["mean_turns_given_termination"]), s["censored"]]
                 for label, s in zip(SHORT, stats)]
    stat_table = table(["Game variant", "Games", "Death rate", "Mean turns given death", "Median death turn", "Mean completion turn", "Unresolved"], stat_rows)
    policies_table = table(["Policy", "q", "Shape", "Tolerance", "Interval confidence"], [[p["name"], p["retention"], p["shape"], p["tolerance"], f"{1-float(Fraction(p['delta'])):.0%}"] for p in plan["policies"]])
    accepted = [SHORT[i] for i in range(len(records)) if matrix[i,0] > 0]
    rejected = [SHORT[i] for i in range(len(records)) if matrix[i,0] == 0]
    total_games = sum(s["games"] for s in stats) + len(records)*len(plan["admission_seeds"])*plan["admission_games_per_batch"]
    report = f'''<!doctype html><html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>RPG balance and lifetime study</title>
<style>body{{max-width:1150px;margin:40px auto;padding:0 24px;font:16px/1.6 system-ui;color:#172033;background:#fafbfe}}h1,h2{{line-height:1.2}}h1{{font-size:36px}}h2{{margin-top:40px}}.lead{{font-size:20px}}.card{{padding:20px;background:white;border:1px solid #dce3ef;border-radius:12px;margin:24px 0}}svg{{width:100%;height:auto}}table{{border-collapse:collapse;width:100%;font-size:13px}}th,td{{text-align:left;padding:9px;border-bottom:1px solid #e2e8f0}}th{{background:#edf2fa}}.table{{overflow:auto}}code{{font-size:13px}}small{{color:#596579}}a{{color:#4f46e5}}</style>
<h1>Does the balance check change which games we allow?</h1>
<p class="lead">Yes: the same simulated outcomes produce different admission decisions when the Weibull curve, tolerance, or confidence changes. The parameters filter games; they do not change the dice or the lifetime of an unchanged game.</p>
<p>{total_games:,} trajectories across seven variants of two adventures. Each variant has 20,000 lifetime runs and five independent-seed batches of 1,000 games. The nine policies reuse those five batches. Study runtime: {meta['elapsed_seconds']:.1f} seconds.</p>
<div class="card"><strong>Default policy:</strong> q=0.95, shape=2, tolerance=±0.20, 95% exact binomial confidence, six checked death rows.<br>At least one batch passed for: {html.escape(', '.join(accepted))}.<br>No batches passed for: {html.escape(', '.join(rejected))}.</div>
<h2>Death rates and time before death</h2><div class="table">{stat_table}</div>
<p><strong>Mean turns given death</strong> averages only characters who died within the observation window. A successful ending is never counted as a death. A game with no observed deaths has no such average. Mean completion turn includes both death and successful endings. One turn is one scene choice, including its entire fight; it is not one combat round.</p>
<div class="card">{deaths_svg}</div><div class="card">{time_svg}</div>
<h2>How much the balance parameters matter</h2><div class="card">{admission_svg}</div>
<p>Each cell counts passing batches out of five. A darker cell does not mean a game is more fun or mathematically more balanced. It means this particular test admitted it more often under that policy. Five batches are a sensitivity check, not a precise estimate of long-run acceptance probability.</p>
<div class="table">{policies_table}</div>
<p>Changing confidence from 95% to 99% makes intervals wider and can reduce acceptance. Changing the target or tolerance changes which risk patterns are permitted. The shipped game keeps the default policy; these alternatives are experimental only.</p>
<p><strong>What the sweep exposes:</strong> q=0.90, shape=3, and the ±0.10 tolerance each require some deaths on turn 2; every studied story has two safe opening turns, so even the harsh variant fails. With q=0.98, shape=1, or ±0.30 tolerance, all six bands include zero, so the no-combat variant can pass. The ±0.30 setting also admits the harsh variant. At 99% confidence, Silver Acorn passed four batches instead of five.</p>
<h2>What the test compares</h2><div class="card">{frequency_svg}</div>
<p>The first row is first-turn death. Later rows measure death at exactly t+2 given the game is active at t. These are not the probability of dying anywhere within two turns and not the one-turn hazard. The plotted observations pool five batches for display; admission uses each separate batch's complete exact-binomial intervals, not these point estimates.</p>
<h2>What changed in the game</h2><p>The new meta rules are Committed Strike (+1 hero damage during All-Out Attack), Guard Feint (−1 enemy hit level against All-Out Defense), Cornered Fury (+2 enemy hit level at half HP), and Punish the Opening (+1 enemy damage against All-Out Attack). They are shared defaults for built-in and generated adventures. Lighthouse also adds a relief-watch bluff, a cargo-net route that splits the wreckers, a keeper rescue, a disarmed duel, a flare bluff, and a new ending.</p>
<p>The original baseline uses its original graph and no new meta rules. The meta-rules-only variant isolates the combat change on that original graph. The expanded version adds the new choices. The unchecked superweapon has attack level 18 and 6d+6 flame damage; the harsh variant adds unconditional +4 enemy hit level and +6 damage. The peaceful variant replaces fights with their win destination. The Silver Acorn is a separate authored fixture with its own character and encounters.</p>
<h2>Method, proof, and limits</h2><ul><li>All trajectories run the compiled Lean simulator and the same shared combat engine as play, with uniform scene choices and the fixed uniform maneuver/target policy.</li><li>The lifetime cap is {plan['lifetime_turn_limit']} scene turns; the combat cap is {plan['combat_round_limit']} rounds per fight. Timeouts and invalid trajectories are retained. None are silently dropped.</li><li><code>StatisticalCandidate.balancedAt</code> now accepts an explicit policy. The study calls the same <code>ValidationAccepted</code> predicate with that policy. Production admission still uses <code>defaultPolicy</code>.</li><li>The theorem gives per-row coverage and bounds false acceptance of one whole test, under the accepted conditional-binomial sampling assumptions. It does not certify fun, every player strategy, PRNG independence, or simultaneous confidence across all cells in this exploratory study.</li><li>The default check admitted Silver Acorn despite an 83.4% random-play death rate: the finite timing bands do not set an overall win-rate target. Higher conditional mean time to death alone does not prove a game is safer: compare death rates too. Winning games never later die in this model, so an unconditional mean time to death can be infinite.</li><li>Policies and seeds were recorded before study results. No study result was used to tune the shipped rules. The same seeds across variants aid reproducibility but do not make every consumed roll a matched observation.</li><li>The Weibull values are game-design choices, not empirical RPG standards. Linux-only kernel replay and Comparator remain pending on this Mac.</li></ul>
<h2>Reproduce and inspect</h2><p>Run <code>python3 scripts/run_balance_study.py</code>, then the report script with Matplotlib installed. The plan is <code>experiments/plan.json</code>. This report is self-contained; the CSVs, SVGs, PNGs, raw JSONL observations, and source SHA-256 hashes are alongside it.</p><p><small>Recorded parent commit: {html.escape(meta['git_parent'])}. Plan SHA-256: {html.escape(meta['plan_sha256'])}. Measurement started: {html.escape(meta['started_utc'])}.</small></p></html>'''
    (OUT / "report.html").write_text(report)
    print(json.dumps({"games": total_games, "lifetime": stats, "default_acceptance": {r['variant']: int(matrix[i,0]) for i,r in enumerate(records)}, "report": str(OUT/'report.html')}, indent=2))


if __name__ == "__main__":
    main()
