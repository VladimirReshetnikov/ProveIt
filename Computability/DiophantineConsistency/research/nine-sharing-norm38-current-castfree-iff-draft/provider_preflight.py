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
    ('nine-sharing-norm38-current-existential-iff-terminal-independent',
     '84e1130702cd44a25de5116fd1de58c46ab1cf64213f8a7a8d61d4ca10897a65',
     '7b1cd70e7becc995640cfc631d886d16111771f0bd041519a76aa0a14db07c72'),
    ('nine-sharing-norm38-current-source-cast-instantiation-terminal-independent',
     '996c5605c8ff6dc27261133650be0d9ab9128a78733d585b456ede70c0e2c84a',
     '226fe1ec13607b7f14b59cd223a95334b69936864d6914795c6bd14e28394490'),
)
for name, script_pin, result_pin in audits:
    q = D / 'reviews' / name
    if sha(q / 'check.py') != script_pin or sha(q / 'result.json') != result_pin:
        raise RuntimeError(('audit pin mismatch', name))
    r = subprocess.run([sys.executable, '-I', '-S', '-B', str(q / 'check.py')],
                       capture_output=True, timeout=300)
    if r.returncode or r.stderr or r.stdout != (q / 'result.json').read_bytes():
        raise RuntimeError(('audit failed', name, r.returncode, r.stderr.decode(errors='replace')))
if sha(P / 'survey.py') != '1b78af04f6031bd8100a9475eca7c483218e792e29ed7dd88065225e6ddd9ec2':
    raise RuntimeError('survey source mismatch')
if sha(P / 'survey-result.json') != '2466858ff749f926f45a6a29604ab798e9c26e34ab0ca10fd04f408dd0fbea08':
    raise RuntimeError('survey result mismatch')
r = subprocess.run([sys.executable, '-I', '-S', '-B', str(P / 'survey.py')],
                   capture_output=True, timeout=300)
if r.returncode or r.stderr or r.stdout != (P / 'survey-result.json').read_bytes():
    raise RuntimeError(('overlay comparison failed', r.returncode, r.stderr.decode(errors='replace')))
print(json.dumps({'status': 'PASS_POINT_IN_TIME_PROVIDER_SURVEY',
                  'scope': 'Two retained provider audits and overlay comparison only; no Lean replay or complete dynamic ancestry.'}, sort_keys=True, indent=2))
