#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re,subprocess,sys
D=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
s=(P/'Compact78To85.lean').read_text()
for t in ('P78AuxRoot.graph','P85QcubeGraph.graph','positive_zero_iff_natural_ports p hb.1','CompactEquivalence8485Draft.positive_zero_iff K','.symm.trans','ports CompactFixedBeta.betaNat K lowNat highNat'):assert t in s
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
for name in ('ordinary14-84-85-compact-model-equivalence-draft','ordinary14-84-to-78-model-composition-draft'):
 p=D/'research'/name;r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=120)
 assert not r.stderr and r.stdout==(p/'observation.json').read_bytes(),name
paths=[P/'Compact78To85.lean',D/'research/ordinary14-84-85-compact-model-equivalence-draft/CompactEquivalence.lean',D/'research/ordinary14-84-to-78-model-composition-draft/ModelComposition.lean']
print(json.dumps({'scope':'source/interface inventory and draft receipt replays only; no Lean invocation','sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
