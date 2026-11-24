"""Lean integration checks for sparse support, including corrupted certificates.

Run explicitly after building MarkovRPGLiveRules and MarkovRPGScenes. These
checks do not start a server or modify saved games.
"""
import argparse
from fractions import Fraction as Q
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import time

import certificate
import engine
import rules


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    root = Path(__file__).resolve().parent.parent

    # An explicit zero-weight entry must never become an edge.
    rows = [{1: Q(1), 2: Q(0)}, {2: Q(1)}, {2: Q(1)}]
    toy = dict(nodes=[dict(id=i) for i in range(3)], rows=rows,
               choices=[{'Continue': row} for row in rows],
               terminal=[False, False, True], lose=[False, False, True],
               rank=[2, 1, 0], next=[1, 2, 2])
    source = '''import MarkovRPGLiveRules
set_option maxRecDepth 100000
open scoped BigOperators NNReal
open MarkovRPG MarkovRPG.Workshop
namespace WorkshopCertificate
'''
    source += certificate.graph('world', toy)
    source += certificate.actions_certificate(toy, dict(deterministic_max=1)).split(
        '\ndef cycleNeighbors', 1)[0]
    source += '\n#print axioms edge_support_exact\nend WorkshopCertificate\n'
    source = source.replace('by decide', 'by decide +kernel')
    needle = '([[1], [2], [2]] : List (List Nat))'
    assert source.count(needle) == 1

    cases = [('zero_weight_valid', source, False)]
    for name, targets in [('missing_edge', '[[], [2], [2]]'),
                          ('spurious_zero_weight_edge', '[[1, 2], [2], [2]]')]:
        cases.append((name, source.replace(needle, f'({targets} : List (List Nat))'), True))

    # Exercise the same support in a complete live-change certificate at t > 0.
    d, w, r, c = engine.generate(max_nodes=30)
    snapshot = dict(document=d, world=w, ref=r, duel=c, current=1,
                    timestamp=1, fight=None, revision=1)
    action = next(iter(w['choices'][1]))
    destination = next(iter(w['choices'][1][action]))
    candidate = rules.propose(snapshot, dict(kind='insert', action=action,
                                            destination=destination, scene='new'))
    assert candidate[0]['timestamp'] == 1
    assert len(candidate[0]['scenes']) == len(d['scenes']) + 1
    cases.append(('live_new_scene_at_t1', certificate.export(*candidate, previous=snapshot), False))

    results = []
    for name, code, should_reject in cases:
        path = args.output / (name + '.lean')
        log_path = args.output / (name + '.log')
        path.write_text(code)
        started = time.perf_counter()
        timed_out = False
        with log_path.open('w') as log_file:
            process = subprocess.Popen(['lake', 'env', 'lean', str(path.resolve())],
                                       cwd=root, stdout=log_file, stderr=subprocess.STDOUT,
                                       start_new_session=True)
            try:
                process.wait(timeout=120)
            except subprocess.TimeoutExpired:
                timed_out = True
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
        log = log_path.read_text()
        forbidden = [s for s in ('sorryAx', 'Lean.ofReduceBool', 'uses `sorry`') if s in log]
        missing = [n for n in re.findall(r'^#print axioms (\w+)', code, re.MULTILINE)
                   if 'WorkshopCertificate.' + n not in log]
        if should_reject:
            line = next(i for i, text in enumerate(code.splitlines(), 1)
                        if text.startswith('theorem edge_targets_match'))
            # Reject for the intended assertion, not a syntax or unrelated failure.
            expected_error = re.search(rf':{line}:\d+: error:.*decide', log)
            passed = process.returncode != 0 and expected_error is not None
        else:
            passed = process.returncode == 0 and not forbidden and not missing
        result = dict(case=name, seconds=time.perf_counter() - started,
                      expected_rejection=should_reject, returncode=process.returncode,
                      timed_out=timed_out, passed=passed and not timed_out)
        results.append(result)
        (args.output / 'result.json').write_text(json.dumps(results, indent=2) + '\n')
        print(json.dumps(result), flush=True)
    if not all(x['passed'] for x in results):
        raise SystemExit('A support integration check failed; see the saved Lean logs.')


if __name__ == '__main__':
    main()
