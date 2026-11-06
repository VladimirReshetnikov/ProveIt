#!/usr/bin/env python3
"""Recheck both audited providers and a pinned overlay comparison; no Lean."""
import hashlib
import json
import subprocess
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
P = Path(__file__).resolve().parent
D = P.parents[1]
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
audits = (
    ('nine-sharing-norm38-seed-static-iff-terminal-independent',
     '1328edd7b35885ad91e7ed0e2acd644fe094da66ca14996a61b25cf041faee74',
     'e659cb0324676bdf6c836eb302a9304e45a1f41cc687e89f3701c2e81713a714'),
    ('nine-sharing-norm38-static-source-terminal-independent',
     '8ff82219499c91131ae0a9dd831f509c6629df559d266557f4bdb9cf0a78f33d',
     '90cf29bcd9a6397a261fb4a86c46bdf03a5888026490116d02cb85d80f99d048'),
)
for name, script_pin, result_pin in audits:
    q = D / 'reviews' / name
    if sha(q / 'check.py') != script_pin or sha(q / 'result.json') != result_pin:
        raise RuntimeError(('audit pin mismatch', name))
    r = subprocess.run([sys.executable, '-I', '-S', '-B', str(q / 'check.py')],
                       capture_output=True, timeout=300)
    if r.returncode or r.stderr or r.stdout != (q / 'result.json').read_bytes():
        raise RuntimeError(('audit failed', name, r.returncode, r.stderr.decode(errors='replace')))
if sha(P / 'survey.py') != '5270a33b0bbe85f458bdcad7a5cf56576da5999fd65b3793cf3e372b2edbb087':
    raise RuntimeError('survey source mismatch')
if sha(P / 'survey-result.json') != '44a620d71b18f10c9d6ad925d6c8feb183b2293c72271b8882b4784d126cb15a':
    raise RuntimeError('survey result mismatch')
r = subprocess.run([sys.executable, '-I', '-S', '-B', str(P / 'survey.py')],
                   capture_output=True, timeout=300)
if r.returncode or r.stderr or r.stdout != (P / 'survey-result.json').read_bytes():
    raise RuntimeError(('overlay comparison failed', r.returncode, r.stderr.decode(errors='replace')))
print(json.dumps({'status': 'PASS_POINT_IN_TIME_PROVIDER_SURVEY',
                  'scope': 'Two retained provider audits and overlay comparison only; no Lean replay or complete dynamic ancestry.'}, sort_keys=True, indent=2))
