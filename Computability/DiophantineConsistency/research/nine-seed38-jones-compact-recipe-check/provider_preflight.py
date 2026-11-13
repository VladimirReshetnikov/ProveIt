#!/usr/bin/env python3
"""Recheck language provider and JSON-to-source quote; no Lean."""
import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
P = Path(__file__).resolve().parent
D = P.parents[1]
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
audits = (
    ('nine-seed38-jones-compact-language-retry01-terminal-frontier-independent', 'f088fde3236c613d6504c48361037639724a9058a682c78abf8946032c167fe0', 'a5985b35a04b6c7101f8ea542f9ef3a84648b254cb08c67cadd45fe2e6062a8b'),
    ('nine-seed38-jones-compact-macro-frontier-independent', 'a98aae5bde70e9946beba8a761e61e3348494abc3bb9d4ab619636bf5da9d022', '68f23e449388f3ec78e1e3f42ed4e1633338d71355fc2741f487c71ecd25488e'),
)
for name, script_pin, result_pin in audits:
    q = D / 'reviews' / name
    if sha(q / 'check.py') != script_pin or sha(q / 'result.json') != result_pin:
        raise RuntimeError(('audit pin mismatch', name))
    r = subprocess.run([sys.executable, '-I', '-S', '-B', str(q / 'check.py')], capture_output=True, timeout=300)
    if r.returncode or r.stderr or r.stdout != (q / 'result.json').read_bytes():
        raise RuntimeError(('audit failed', name, r.returncode, r.stderr.decode(errors='replace')))
draft = D / 'research/nine-seed38-jones-compact-lean-draft'
if sha(draft / 'quote.py') != '21e781a1f13a315bcb065650fc19ea0143ea36408826b3ee086f885be5d13c2b' or sha(draft / 'Norm38MacroRecipe.lean') != '3756c5e056e9bfedd28aa1fca5d5aa01c6bbde8163332c70abced196cf6d3979':
    raise RuntimeError('generated source pin')
r = subprocess.run([sys.executable, '-I', '-S', '-B', str(draft / 'quote.py'), '--check'], capture_output=True, timeout=30)
if r.returncode or r.stderr or json.loads(r.stdout)['status'] != 'PASS_QUOTE_REGENERATION_ONLY':
    raise RuntimeError(('source quote check', r.returncode, r.stderr.decode(errors='replace')))
base = Path('/tmp/nine-seed38-jones-compact-language-retry01-20261106/lib/DiophantineConsistency')
obj = base / 'Norm38MacroLanguage.olean'
expected = '7031d85f55adb8f82f96686c300443da2adf4eeb30ae743fb6f42a08509e8d65'
if not obj.is_file() or sha(obj) != expected:
    raise RuntimeError('macro language provider')
if os.path.lexists(base / 'Norm38MacroRecipe.olean'):
    raise RuntimeError('output shadows provider')
print(json.dumps({'status': 'PASS_POINT_IN_TIME_PROVIDER_SURVEY',
                  'selected': {'DiophantineConsistency.Norm38MacroLanguage': {'realpath': str(obj.resolve()), 'sha256': expected}},
                  'scope': 'Audited language producer and reproducible unverified quote only; no Lean, scopedness/semantics proof, verified parser or complete dynamic ancestry.'}, indent=2, sort_keys=True))
