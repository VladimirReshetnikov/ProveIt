#!/usr/bin/env python3
from pathlib import Path
from hashlib import sha256
import json
import subprocess
import sys
import time

p = Path(__file__).resolve().parent
o = p / 'observations/attempt03'
o.mkdir(parents=True, exist_ok=False)
cmd = [sys.executable, '-I', '-S', '-B', str(p / 'check.py')]
r = subprocess.run(cmd, capture_output=True)
(o / 'stdout').write_bytes(r.stdout)
(o / 'stderr').write_bytes(r.stderr)
h = lambda b: sha256(b).hexdigest()
terminal = {'exit': r.returncode, 'command': cmd, 'check_sha256': h((p / 'check.py').read_bytes()),
            'stdout_sha256': h(r.stdout), 'stderr_sha256': h(r.stderr), 'time_ns': time.time_ns(),
            'scope': 'external graph, degree, payload and isolated rebuild audit; no Lean replay or file binding'}
(o / 'terminal.json').write_text(json.dumps(terminal, indent=2, sort_keys=True) + '\n')
print(json.dumps(terminal, indent=2))
sys.exit(r.returncode)
