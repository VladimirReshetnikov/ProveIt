#!/usr/bin/env python3
"""Rebuild every finite fixture and rerun the portable checks. No giant scalar expansion."""
import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--symbolic', action='store_true', help='also run SymPy degree and canonical-overlay checks')
args = parser.parse_args()
steps = ['tree_kernel.py', 'eager_compiler.py', 'counter_source.py',
         'shared_compression.py', 'export_shared_macro.py', 'verify_shared_macro.py',
         'canonical.py', 'canonical_projected.py',
         'independent_audit.py', 'independent_compiler_audit.py',
         'independent_shared_audit.py', 'constant_bit_bound.py',
         'verify_packet_assumptions.py', 'analyze_growth.py', 'audit_exact_count.py',
         'independent_growth_audit.py']
if args.symbolic:
    import sympy
    steps += ['symbolic_audit.py', 'canonical_overlay_audit.py', 'canonical_projected_audit.py']
logs = ROOT / 'replay-output'
logs.mkdir(exist_ok=True)
summary = []
for step in steps:
    print('Checking ' + step, flush=True)
    result = subprocess.run([sys.executable, str(ROOT / 'code' / step)], cwd=ROOT / 'code', text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (logs / (step + '.log')).write_text(result.stdout)
    summary.append({'script': step, 'returncode': result.returncode})
    if result.returncode:
        print(result.stdout)
        raise SystemExit(result.returncode)
(logs / 'replay-summary.json').write_text(json.dumps(summary, indent=2) + '\n')
print('All requested checks passed. Logs: replay-output/')
