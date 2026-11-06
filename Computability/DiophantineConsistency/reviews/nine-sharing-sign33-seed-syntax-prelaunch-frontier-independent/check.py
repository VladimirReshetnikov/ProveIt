#!/usr/bin/env python3
import hashlib, json, re, subprocess, sys
from pathlib import Path

d = Path(__file__).resolve().parents[2]
p = d / 'research/nine-sharing-sign33-seed-syntax-check'
def h(path): return hashlib.sha256(path.read_bytes()).hexdigest()
pins = {'run.py': '0df4ada22abaa515b618393b58e01bdc68a5171c2a2d8f5f04982d2c5b230b23',
        'source-manifest.json': '58c8a2ee13210a88e9416a5d3746d9c99e9896010c85c031af1abe9a9402088e',
        'src/DiophantineConsistency/SharingSeed33Syntax.lean': '80218a4396d553da7c49a2d314a0263643b477db7b14d325874cb3dab595f2dd'}
for name, digest in pins.items(): assert h(p / name) == digest, name
source = (p / 'src/DiophantineConsistency/SharingSeed33Syntax.lean').read_text()
assert re.findall(r'^import ([\w.]+)$', source, re.M) == ['DiophantineConsistency.NineFreshJones']
assert not re.search(r'^\s*(theorem|lemma)\s', source, re.M)
assert h(d / 'research/nine-sharing-sign33-seed-syntax-draft/SharingSeed33Syntax.lean') == pins['src/DiophantineConsistency/SharingSeed33Syntax.lean']
audit = d / 'reviews/nine-sharing-sign33-seed-syntax-frontier-independent'
assert h(audit / 'check.py') == '934ac9b2b352d19a8b0cef7d04f40270a44fd4a9e428dc50df7bc05123a3a245'
assert h(audit / 'result.json') == '878aefbc80f4785e006d6ae4240421c4cb86c071cd8ea327b3f3f193d096e49f'
subprocess.run([sys.executable, '-I', '-S', '-B', str(audit / 'check.py')], check=True, stdout=subprocess.DEVNULL)
r = subprocess.run([sys.executable, '-I', '-S', '-B', str(p / 'run.py'), '--preflight'], check=True, capture_output=True, text=True)
o = json.loads(r.stdout)
assert o['status'] == 'PASS_NO_LEAN_PREFLIGHT' and o['stage_count'] == 1
print(json.dumps({'status': 'PASS', 'preflight': o, 'scope': 'source and direct provider prelaunch only; no Lean run'}, sort_keys=True, indent=2))
