#!/usr/bin/env python3
"""Capture a repeatable post-restoration audit without overwriting evidence."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

here = Path(__file__).resolve().parent
audit = here / 'audit.py'
output = here / 'audit-observations-attempt05'
terminal = here / 'observations/audit-attempt05'
if output.exists() or terminal.exists():
    raise RuntimeError('refusing to overwrite a previous audit')
before = audit.read_bytes()
pin = 'a78fb817cdb0f70870c60176f8f9197c6599a72d24452430be69f58288b5bd33'
h = lambda b: hashlib.sha256(b).hexdigest()
if h(before) != pin:
    raise RuntimeError('audit source pin drift')
terminal.mkdir(parents=True)
command = [sys.executable, '-I', '-B', str(audit), str(output)]
run = subprocess.run(command, capture_output=True, text=True, timeout=180)
(terminal / 'stdout').write_text(run.stdout)
(terminal / 'stderr').write_text(run.stderr)
result = output / 'audit.json'
receipt = {'command': command, 'exit_code': run.returncode,
           'audit_sha256': h(before), 'audit_unchanged': audit.read_bytes() == before,
           'stdout_sha256': h(run.stdout.encode()), 'stderr_sha256': h(run.stderr.encode()),
           'result_sha256': h(result.read_bytes()) if result.is_file() else None}
(terminal / 'terminal.json').write_text(json.dumps(receipt, indent=2, sort_keys=True) + '\n')
print(json.dumps(receipt, sort_keys=True))
if run.returncode != 0 or run.stderr or not receipt['audit_unchanged'] or not result.is_file():
    raise SystemExit(1)
