#!/usr/bin/env python3
"""Build and check a finished mechanic candidate within one shared deadline."""
import argparse
import hashlib
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time

CHECK_SECONDS = 60.0


class CheckFailure(Exception):
    def __init__(self, message, code=1):
        super().__init__(message)
        self.code = code


def stop_group(process):
    """Stop the command and its compiler or simulator children."""
    try:
        os.killpg(process.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    process.wait()


def run_step(label, command, root, deadline):
    """A failed command or exhausted shared budget can never become a pass."""
    remaining = deadline - time.monotonic()
    if remaining <= 0:
        raise CheckFailure(f"INCOMPLETE: deadline reached before {label}", 124)
    print(f"\n{label} ({remaining:.1f}s remaining)", flush=True)
    process = subprocess.Popen(command, cwd=root, stdin=subprocess.DEVNULL,
                               stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                               text=True, start_new_session=True)
    try:
        output, _ = process.communicate(timeout=max(0, deadline - time.monotonic()))
    except subprocess.TimeoutExpired:
        stop_group(process)
        output, _ = process.communicate()
        print(output, end="", flush=True)
        raise CheckFailure(f"INCOMPLETE: {label} exceeded the shared deadline", 124)
    except BaseException:
        stop_group(process)
        raise
    print(output, end="", flush=True)
    if process.returncode != 0:
        raise CheckFailure(f"FAILED: {label} (exit {process.returncode})")
    if time.monotonic() > deadline:
        raise CheckFailure(f"INCOMPLETE: deadline reached during {label}", 124)


def source_digest(root):
    """Reject a result if the checked inputs changed while the command ran."""
    paths = list((root / 'Rpg').rglob('*.lean'))
    paths += list((root / '.agents/skills/add-mechanic').rglob('*.lean'))
    paths += [root / name for name in
              ('Main.lean', 'Validate.lean', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain')]
    digest = hashlib.sha256()
    for path in sorted(paths):
        digest.update(str(path.relative_to(root)).encode())
        digest.update(path.read_bytes())
    return digest.hexdigest()


def audit_source(root):
    """Inspect every project theorem, including private regression examples."""
    modules = sorted('.'.join(p.relative_to(root).with_suffix('').parts)
                     for p in (root / 'Rpg').rglob('*.lean'))
    imports = '\n'.join('import ' + name for name in modules)
    return 'import Lean\n' + imports + '''
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  for (name, info) in env.constants.toList do
    let text := name.toString
    if text.startsWith "Rpg." || text.startsWith "_private.Rpg." then
      match info with
      | .axiomInfo _ => throwError "Project axiom is not allowed: {name}"
      | .thmInfo _ =>
        let axioms ← liftCoreM <| collectAxioms name
        for axiomName in axioms do
          unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
            throwError "{name} uses an unapproved axiom: {axiomName}"
        checked := checked + 1
      | _ => pure ()
  if checked = 0 then throwError "No project theorems were audited"
  logInfo m!"Axiom audit passed for {checked} project theorems."
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--final', action='store_true',
                        help='After freezing the mechanic, run held-out admission and Linux replay.')
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[4]
    start = time.monotonic()
    deadline = start + CHECK_SECONDS
    try:
        before = source_digest(root)
        run_step('Build all proofs, regression tests, and compiled helpers',
                 ['lake', 'build', 'Rpg', 'rpg', 'agree', 'screen', 'validate'], root, deadline)
        with tempfile.TemporaryDirectory(prefix='rpg-proof-audit-') as directory:
            audit = Path(directory) / 'Audit.lean'
            audit.write_text(audit_source(root))
            run_step('Audit proof axioms', ['lake', 'env', 'lean', str(audit)], root, deadline)
        run_step('Compiled exploratory screen', ['.lake/build/bin/screen'], root, deadline)
        if args.final:
            run_step('Compiled held-out admission',
                     ['.lake/build/bin/screen', '--validation'], root, deadline)
            if sys.platform.startswith('linux'):
                run_step('Isolated kernel replay', ['lake', 'check'], root, deadline)
            else:
                print('PENDING: isolated kernel replay requires Linux; it was not run.', flush=True)
        if source_digest(root) != before:
            raise CheckFailure('INCOMPLETE: source inputs changed during validation')
        elapsed = time.monotonic() - start
        if elapsed > CHECK_SECONDS:
            raise CheckFailure('INCOMPLETE: shared deadline exceeded', 124)
        print(f'\nLOCAL CHECKS PASSED in {elapsed:.2f}s; exact combat enumeration was not run.')
        return 0
    except CheckFailure as error:
        print(f'\n{error}; elapsed={time.monotonic() - start:.2f}s', file=sys.stderr)
        return error.code
    except OSError as error:
        print(f'\nFAILED: {error}', file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.exit(main())
