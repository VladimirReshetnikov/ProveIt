#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re,subprocess,sys
D=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
s=(P/'CompactEquivalence.lean').read_text();ports=(D/'Lean/DiophantineConsistency/Compact44/CompactSymbolicPorts.lean').read_text()
for t in ('ports CompactFixedBeta.betaNat K lowNat highNat','C44Short15Facts.port_bounds','CompactFixedBeta.beta_identity','P72Root.cast_port p 0','P72Root.cast_port p 3','ModelEquivalence8485Draft.positive_zero_iff'):assert t in s
assert '![β,K,L,β+H]' in ports and 67*8807==590069
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
p=D/'research/ordinary14-84-85-model-equivalence-draft';r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90)
assert not r.stderr and r.stdout==(p/'observation.json').read_bytes()
paths=[P/'CompactEquivalence.lean',p/'ModelEquivalence.lean',D/'Lean/DiophantineConsistency/Compact44/CompactSymbolicPorts.lean',D/'Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean',D/'Lean/DiophantineConsistency/Compact44/C44Short15Facts.lean',D/'Lean/DiophantineConsistency/Compact44/P72Root.lean']
print(json.dumps({'scope':'source/interface and symbolic port layout inventory, draft receipt replay; no Lean invocation','beta_exponent':590069,'sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
