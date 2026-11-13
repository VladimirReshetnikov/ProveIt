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
    ('nine-sharing-norm38-current-nine-source-terminal-independent',
     '306b382dc3284b7ebf8416843dba8be1666bb9e551d26ed14bbd8179ceb11082',
     'a51f89e0640a94e24ce1707344d256c045c76925a7d4998f2e55a05f879951ae'),
    ('nine-sharing-norm38-current-source-to-seed-terminal-independent',
     'fd7181a17929d7bee9ac79f0b34f2ee3f912724fc7071a0b86f8942fac870dc6',
     '39fe98ccb95f88a258cf5df740d95aa7ede59fe8f75ca068b25fff3c2b4292c8'),
)
for name, script_pin, result_pin in audits:
    q = D / 'reviews' / name
    if sha(q / 'check.py') != script_pin or sha(q / 'result.json') != result_pin:
        raise RuntimeError(('audit pin mismatch', name))
    r = subprocess.run([sys.executable, '-I', '-S', '-B', str(q / 'check.py')],
                       capture_output=True, timeout=300)
    if r.returncode or r.stderr or r.stdout != (q / 'result.json').read_bytes():
        raise RuntimeError(('audit failed', name, r.returncode, r.stderr.decode(errors='replace')))
if sha(P / 'survey.py') != 'fb7ae0b171a1f39a2e3bcdfddb3e310803d2fe0ef812e7078a5f2e86b15e2b3c':
    raise RuntimeError('survey source mismatch')
if sha(P / 'survey-result.json') != '71deaee09f8e4ac86f9afb82b46ed982e82897d3fa2fd9802a587bd2c864b750':
    raise RuntimeError('survey result mismatch')
r = subprocess.run([sys.executable, '-I', '-S', '-B', str(P / 'survey.py')],
                   capture_output=True, timeout=300)
if r.returncode or r.stderr or r.stdout != (P / 'survey-result.json').read_bytes():
    raise RuntimeError(('overlay comparison failed', r.returncode, r.stderr.decode(errors='replace')))
print(json.dumps({'status': 'PASS_POINT_IN_TIME_PROVIDER_SURVEY',
                  'scope': 'Two retained provider audits and overlay comparison only; no Lean replay or complete dynamic ancestry.'}, sort_keys=True, indent=2))
