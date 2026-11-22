"""Measure the unmodified generator and complete Lean certificate separately.

Run after `lake build MarkovRPGLiveRules MarkovRPGScenes`. No server or game
session is changed. The diagnostic timeout may exceed the site's 240s limit;
the report records both actual completion and compatibility with that limit.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import resource
import signal
import subprocess
import time

import certificate
import engine


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--nodes', type=int, default=60)
    parser.add_argument('--characters', type=int, default=12)
    parser.add_argument('--branches', type=int, default=4)
    parser.add_argument('--difficulty', choices=('easy', 'medium', 'hard'), default='hard')
    parser.add_argument('--timeout', type=float, default=600)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    root = Path(__file__).resolve().parent.parent
    report = dict(configuration=dict(nodes=args.nodes, characters=args.characters,
                  branches=args.branches, difficulty=args.difficulty),
                  python=platform.python_version(), machine=platform.machine(),
                  site_timeout_seconds=240, diagnostic_timeout_seconds=args.timeout,
                  dependencies_prebuilt=True, repetitions=1,
                  source_hashes={p: hashlib.sha256((root / p).read_bytes()).hexdigest()
                     for p in ('workshop/engine.py', 'workshop/certificate.py',
                               'workshop/scenes.py', 'MarkovRPGScenes.lean',
                               'MarkovRPGAdventureProperties.lean', 'MarkovRPGLiveRules.lean')})
    report_path = args.output / 'result.json'
    def save():
        report_path.write_text(json.dumps(report, indent=2) + '\n')

    start = time.perf_counter()
    data = engine.generate(args.difficulty, args.branches, args.nodes, args.characters)
    report['generation_seconds'] = time.perf_counter() - start
    document, world, _, _ = data
    report.update(actual_nodes=len(world['nodes']), scenes=len(document['scenes']),
                  actions=len(certificate.flat_actions(world)), horizon=document['horizon'])
    start = time.perf_counter()
    source = certificate.export(*data)
    report['certificate_export_seconds'] = time.perf_counter() - start
    report['certificate_sha256'] = hashlib.sha256(source.encode()).hexdigest()
    source_path = args.output / 'certificate.lean'
    source_path.write_text(source)
    (args.output / 'graph.json').write_text(json.dumps(document, indent=2))
    expected = re.findall(r'^#print axioms (\w+)', source, re.MULTILINE)
    assert {'scene_graph_exact', 'additional_properties', 'actions_match_graph',
            'timestamp_fair', 'phase_type_fair', 'loss_exact'} <= set(expected)
    report['status'] = 'verifying'
    save()
    print(json.dumps({k: report[k] for k in ('generation_seconds', 'certificate_export_seconds',
                     'actual_nodes', 'scenes', 'actions', 'horizon')}), flush=True)
    cpu_before = resource.getrusage(resource.RUSAGE_CHILDREN)
    start = time.perf_counter()
    with (args.output / 'lean.log').open('w') as log_file:
        process = subprocess.Popen(['lake', 'env', 'lean', str(source_path.resolve())],
                                   cwd=root, stdout=log_file, stderr=subprocess.STDOUT,
                                   start_new_session=True)
        try:
            process.wait(timeout=args.timeout)
        except subprocess.TimeoutExpired:
            # Stop the launcher and its Lean child, not only `lake`.
            os.killpg(process.pid, signal.SIGKILL)
            process.wait()
            report['status'] = 'timeout'
    report['lean_seconds'] = time.perf_counter() - start
    cpu_after = resource.getrusage(resource.RUSAGE_CHILDREN)
    # On timeout this counter may exclude descendants not reaped by the launcher.
    report['direct_child_cpu_seconds'] = (cpu_after.ru_utime + cpu_after.ru_stime -
                                  cpu_before.ru_utime - cpu_before.ru_stime)
    report['lean_returncode'] = process.returncode
    log = (args.output / 'lean.log').read_text()
    report['missing_theorems'] = [n for n in expected if 'WorkshopCertificate.' + n not in log]
    report['forbidden_axioms'] = [s for s in ('sorryAx', 'Lean.ofReduceBool', 'uses `sorry`') if s in log]
    report['accepted'] = (process.returncode == 0 and not report['missing_theorems']
                          and not report['forbidden_axioms'])
    if report['status'] != 'timeout':
        report['status'] = 'verified' if report['accepted'] else 'rejected'
    report['within_site_timeout'] = report['accepted'] and report['lean_seconds'] <= 240
    report['total_seconds'] = (report['generation_seconds'] + report['certificate_export_seconds']
                               + report['lean_seconds'])
    save()
    print(json.dumps(report, indent=2), flush=True)


if __name__ == '__main__':
    main()
