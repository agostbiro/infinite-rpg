"""Exercise failure propagation and timeout cleanup without running the game."""
import importlib.util
from pathlib import Path
import sys
import tempfile
import time
import unittest

spec = importlib.util.spec_from_file_location('mechanic_check', Path(__file__).with_name('check.py'))
check = importlib.util.module_from_spec(spec)
spec.loader.exec_module(check)


class DeadlineTests(unittest.TestCase):
    def test_nonzero_is_failure(self):
        with self.assertRaises(check.CheckFailure) as failure:
            check.run_step('deliberate rejection', [sys.executable, '-c', 'raise SystemExit(7)'],
                           Path.cwd(), time.monotonic() + 5)
        self.assertEqual(failure.exception.code, 1)

    def test_expired_budget_never_starts_command(self):
        with tempfile.TemporaryDirectory() as directory:
            marker = Path(directory) / 'started'
            command = [sys.executable, '-c', f'open({str(marker)!r}, "w").close()']
            with self.assertRaises(check.CheckFailure) as failure:
                check.run_step('expired', command, Path.cwd(), time.monotonic() - 1)
            self.assertEqual(failure.exception.code, 124)
            self.assertFalse(marker.exists())

    def test_timeout_stops_child_processes(self):
        with tempfile.TemporaryDirectory() as directory:
            marker = Path(directory) / 'survived'
            child = f'import time; time.sleep(0.8); open({str(marker)!r}, "w").close()'
            parent = f'import subprocess,sys,time; subprocess.Popen([sys.executable,"-c",{child!r}]); time.sleep(10)'
            start = time.monotonic()
            with self.assertRaises(check.CheckFailure) as failure:
                check.run_step('timeout', [sys.executable, '-c', parent],
                               Path.cwd(), start + 0.25)
            self.assertEqual(failure.exception.code, 124)
            self.assertLess(time.monotonic() - start, 2)
            time.sleep(1)
            self.assertFalse(marker.exists())


if __name__ == '__main__':
    unittest.main()
