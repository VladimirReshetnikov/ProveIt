#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign14-positive74-circuit-output-draft/Sign14Positive74CircuitOutput.lean';s=p.read_text();sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();assert re.findall(r'^import (\S+)$',s,re.M)==['DiophantineConsistency.Sign14Positive74CircuitTransitions08'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for z in ('(symState p 74).getD 73 (.constant 0)','(numState p v 74).getD 73 0','circuitExpr p = Sign14Positive74.expression p','circuitEval p v = (Sign14Positive74.expression p).evalRing v','rw [symState74]','rw [numState74]'):assert z in s
assert s.count('  rfl')==2
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign14-positive74-circuit-transitions-source-independent/check.py')],capture_output=True,check=True,timeout=180)
print(json.dumps({'status':'PASS_SOURCE_AUDIT','source_sha256':sha(p),'scope':'proposed state-74 register-73 symbolic/ring expression equality; no Lean run, file binding or separate foldl equivalence'},indent=2))
