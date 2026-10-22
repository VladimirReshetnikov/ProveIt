#!/usr/bin/env python3
"""Check the constructive collection core and recursively recheck its object."""
import hashlib
import json
import os
from pathlib import Path
import subprocess

here = Path(__file__).resolve().parent
coqc = os.environ.get('COQC', 'coqc')
coqchk = os.environ.get('COQCHK', 'coqchk')
commands = [[coqc, '--version'], [coqc, 'CollectionFirst.v'],
            [coqchk, '-silent', 'CollectionFirst']]
receipt = {'scope': 'Constructive semantic core only; not a syntactic Rocq ZFC endpoint',
           'sha256': hashlib.sha256((here/'CollectionFirst.v').read_bytes()).hexdigest(),
           'records': []}
for command in commands:
    result = subprocess.run(command, cwd=here, capture_output=True, text=True)
    receipt['records'].append({'command': command, 'exit_code': result.returncode,
                              'stdout': result.stdout, 'stderr': result.stderr})
    (here/'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(result.stdout + result.stderr, end='')
    if result.returncode:
        raise SystemExit(result.returncode)
receipt['passed'] = True
(here/'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
print('PASS: compilation, two closed assumption reports, recursive coqchk.')
