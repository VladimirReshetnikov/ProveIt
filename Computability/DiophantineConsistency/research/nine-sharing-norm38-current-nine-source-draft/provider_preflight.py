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
    ('nine-sharing-norm38-current-seed-source-terminal-independent',
     '81b874897e34f1fd72b945984362898377fa3729ebdf58ecf242e3ece075518f',
     '7ee92495532437db853b310f5458cd9e2059507fe4e0ebd05b63d2b73a19a26c'),
    ('nine-sharing-seed38-current-jones-terminal-independent',
     '504a229301d984eb0aefb57bd16c31d7cc14c48776942822a675482195a51f19',
     '08bb9057563af616e0f2705ccf2fe65e6534e20f2ac3b2c20d53789dd74f3468'),
)
for name, script_pin, result_pin in audits:
    q = D / 'reviews' / name
    if sha(q / 'check.py') != script_pin or sha(q / 'result.json') != result_pin:
        raise RuntimeError(('audit pin mismatch', name))
    r = subprocess.run([sys.executable, '-I', '-S', '-B', str(q / 'check.py')],
                       capture_output=True, timeout=300)
    if r.returncode or r.stderr or r.stdout != (q / 'result.json').read_bytes():
        raise RuntimeError(('audit failed', name, r.returncode, r.stderr.decode(errors='replace')))
if sha(P / 'survey.py') != '71db530c429040d0dd55a68ab2a168610730599a54eabdf7ff55fca4359f74b0':
    raise RuntimeError('survey source mismatch')
if sha(P / 'survey-result.json') != '4b8494b1a9dbe3d4ceca77eed5155cde4994cb0af8de8fa289797aa65cc43138':
    raise RuntimeError('survey result mismatch')
r = subprocess.run([sys.executable, '-I', '-S', '-B', str(P / 'survey.py')],
                   capture_output=True, timeout=300)
if r.returncode or r.stderr or r.stdout != (P / 'survey-result.json').read_bytes():
    raise RuntimeError(('overlay comparison failed', r.returncode, r.stderr.decode(errors='replace')))
print(json.dumps({'status': 'PASS_POINT_IN_TIME_PROVIDER_SURVEY',
                  'scope': 'Two retained provider audits and overlay comparison only; no Lean replay or complete dynamic ancestry.'}, sort_keys=True, indent=2))
