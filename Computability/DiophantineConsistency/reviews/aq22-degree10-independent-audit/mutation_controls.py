#!/usr/bin/env python3
"""Exercise the independent checker against altered child graphs in temp copies."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile

if not __debug__:
    raise RuntimeError('optimized Python is not supported')

here = Path(__file__).resolve().parent
root = here.parents[1]
old = root / 'research/adaptive-square-sums26-degree8/candidate.json'
new = root / 'research/adaptive-square-sums22-degree10/candidate.json'
audit = here / 'audit.py'
original = hashlib.sha256(new.read_bytes()).hexdigest()

for label, rowname, operator, expected in (
    ('reverse g72', 'g72', '+', 'g72'),
    ('change retained Fa', 'Fa', '+', 'auxResidual'),
):
    with tempfile.TemporaryDirectory() as tmp:
        sandbox = Path(tmp) / 'Computability/DiophantineConsistency'
        target_old = sandbox / 'research/adaptive-square-sums26-degree8/candidate.json'
        target_new = sandbox / 'research/adaptive-square-sums22-degree10/candidate.json'
        target_audit = sandbox / 'reviews/aq22-degree10-independent-audit/audit.py'
        for p in (target_old, target_new, target_audit):
            p.parent.mkdir(parents=True, exist_ok=True)
        target_old.write_bytes(old.read_bytes())
        graph = json.loads(new.read_text())
        row = next(row for row in graph['source'] if row[0] == rowname)
        row[1] = operator
        target_new.write_text(json.dumps(graph, indent=2) + '\n')
        changed_hash = hashlib.sha256(target_new.read_bytes()).hexdigest()
        # Update only the child hash pin, so rejection must occur beyond hashing.
        source = audit.read_text()
        assert source.count(original) == 1
        target_audit.write_text(source.replace(original, changed_hash))
        proc = subprocess.run([sys.executable, str(target_audit)], capture_output=True, text=True)
        assert proc.returncode != 0 and expected in proc.stderr, (label, proc.stderr)
        assert not (target_audit.parent / 'receipt.json').exists()
        print(label + ': rejected after updating hash pin')

for flag in ('-O', '-OO'):
    proc = subprocess.run([sys.executable, flag, str(audit)], capture_output=True, text=True)
    assert proc.returncode != 0 and 'optimized Python is not supported' in proc.stderr
    print(flag + ': rejected')
