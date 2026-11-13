#!/usr/bin/env python3
"""No-Lean field extraction source and finite integer controls."""
from pathlib import Path
import hashlib,itertools,json,re,subprocess,sys
D=Path(__file__).resolve().parents[2]; H=Path(__file__).resolve().parent
src=H/'ZeroFields.lean'; s=src.read_text()
for n in ('fields84','fields85'): assert re.search(r'\btheorem\s+'+n+r'\b',s)
for g in ('P84QcubeGraph','P85QcubeGraph'):
 for field in ('A0','A1','aux','gap','guardResidual'):
  assert f'eval ({g}.graph p).{field} v' in s
 assert f'{g}.output_shape' in s
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
for a,b,c,d,e in itertools.product(range(-2,3), repeat=5):
 assert ((a*a+b*b+c*c+d*d+e*e)==0)==(a==b==c==d==e==0)
for name,script in [('ordinary14-qcube84-lean-draft','make_graph.py'),('ordinary14-qcube85-lean-draft','make_graph.py'),('ordinary14-direct-first-root-model-draft','check_source.py')]:
 p=D/'research'/name
 args=[sys.executable,'-I','-S','-B',str(p/script)]
 if script=='make_graph.py': args+=['--check']
 r=subprocess.run(args,cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60)
 assert not r.stderr and r.stdout==(p/'observation.json').read_bytes(),name
paths=[src,D/'research/ordinary14-qcube84-lean-draft/P84QcubeGraph.lean',D/'research/ordinary14-qcube85-lean-draft/P85QcubeGraph.lean',D/'research/ordinary14-direct-first-root-model-draft/FirstRootBridge.lean']
print(json.dumps({'scope':'source inventory, draft receipt replay, and finite integer controls; no Lean invocation','finite_tuples':3125,'sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
