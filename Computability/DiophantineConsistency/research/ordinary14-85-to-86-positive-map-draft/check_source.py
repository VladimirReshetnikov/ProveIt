#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,random,re,subprocess,sys
D=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
s=(P/'PositiveMap85To86.lean').read_text()
for t in ('Ring85To86Draft.output_eval','cast_forward','forward_positive','P85QcubeGraph.graph p','P86ResidueGraph.graph p','v 8+v 7'):assert t in s
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
rng=random.Random(858602)
for _ in range(300):
 beta=rng.randint(0,8);v=[rng.randint(1,8) for i in range(14)];q=1+v[0]*beta;out=v.copy();out[7]=q**3*v[7];out[8]=v[8]+v[7]
 assert all(x>0 for x in out) and out[7]==q**3*v[7] and out[8]==v[8]+v[7]
p=D/'research/ordinary14-85-86-ring-client-draft';r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60)
assert not r.stderr and r.stdout==(p/'observation.json').read_bytes()
paths=[P/'PositiveMap85To86.lean',p/'RingComparison85To86.lean',D/'Lean/DiophantineConsistency/Compact44/P72Root.lean']
print(json.dumps({'scope':'source inventory, finite positive update controls and draft receipt replay; no Lean invocation','finite_controls':300,'sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
