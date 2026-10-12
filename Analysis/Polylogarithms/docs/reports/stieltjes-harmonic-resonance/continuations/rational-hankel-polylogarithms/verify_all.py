"""Run every certificate with assertions enabled; fail on any nonzero exit."""
from pathlib import Path
import subprocess
import sys
import time
import json

if not __debug__:
    raise RuntimeError('Run this script without -O.')
root = Path(__file__).resolve().parent
scripts = ['check_compiler.py', 'check_structure.py',
           'check_spectral_exact.py', 'check_numeric.py']
runs = []
for name in scripts:
    start = time.perf_counter()
    proc = subprocess.run([sys.executable, str(root / 'verification' / name)],
                          cwd=root, text=True, capture_output=True, check=False)
    (root / 'data' / f'{Path(name).stem}_replay.txt').write_text(
        proc.stdout + proc.stderr, encoding='utf-8')
    print(proc.stdout, end='')
    if proc.returncode:
        print(proc.stderr, file=sys.stderr)
        raise SystemExit(proc.returncode)
    runs.append({'script': name, 'exit_code': proc.returncode,
                 'seconds': round(time.perf_counter() - start, 3)})
(root / 'data' / 'replay_summary.json').write_text(json.dumps(runs, indent=2))
print('All exact checks and separate numerical diagnostics passed.')
