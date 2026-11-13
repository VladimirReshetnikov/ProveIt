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
    ('nine-sharing-norm38-seed-source-composition-terminal-independent',
     'd1e800b3f078680b0e42697d0f437366786c09140eedb6e6cd770afcc1a65ad0',
     '6520c4666c3716838f59129f8ffcbe9d83e1ddc99b2de2dc1d108dfb92f32c1d'),
    ('nine-sharing-norm38-current-four-cast-terminal-independent',
     '9aacdb00a0e79285a7d0027d8d1ab3decc7b1d2c1afcf987649f18c40c8da2f0',
     'd5890e8a192b3551490c8da97b6434c967d8f35ad5ac626c62c2ee5f005e3499'),
)
for name, script_pin, result_pin in audits:
    q = D / 'reviews' / name
    if sha(q / 'check.py') != script_pin or sha(q / 'result.json') != result_pin:
        raise RuntimeError(('audit pin mismatch', name))
    r = subprocess.run([sys.executable, '-I', '-S', '-B', str(q / 'check.py')],
                       capture_output=True, timeout=300)
    if r.returncode or r.stderr or r.stdout != (q / 'result.json').read_bytes():
        raise RuntimeError(('audit failed', name, r.returncode, r.stderr.decode(errors='replace')))
if sha(P / 'survey.py') != 'aa089f85862e0feba2d51173ec5d8dabfa2aed296f2432364966c84b8d59a42a':
    raise RuntimeError('survey source mismatch')
if sha(P / 'survey-result.json') != '4a8fc9a1e2a4b4269e31152ba71b26e4b7647ecc64ee2d1b4ff8b53a60830b7e':
    raise RuntimeError('survey result mismatch')
r = subprocess.run([sys.executable, '-I', '-S', '-B', str(P / 'survey.py')],
                   capture_output=True, timeout=300)
if r.returncode or r.stderr or r.stdout != (P / 'survey-result.json').read_bytes():
    raise RuntimeError(('overlay comparison failed', r.returncode, r.stderr.decode(errors='replace')))
print(json.dumps({'status': 'PASS_POINT_IN_TIME_PROVIDER_SURVEY',
                  'scope': 'Two retained provider audits and overlay comparison only; no Lean replay or complete dynamic ancestry.'}, sort_keys=True, indent=2))
