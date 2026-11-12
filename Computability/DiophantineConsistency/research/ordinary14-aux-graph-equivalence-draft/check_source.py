#!/usr/bin/env python3
"""Source inventory and signed graph-update controls; never invokes Lean."""
from pathlib import Path
import hashlib,json,random,re,subprocess,sys
D=Path(__file__).resolve().parents[2];H=Path(__file__).resolve().parent
p79=D/'research/ordinary14-direct-pell79/candidate.json';p78=D/'research/ordinary14-aux-root78/candidate.json'
def load(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h;return json.loads(b)
a=load(p79,'5c5e2c089d0f10450374219e9d74883235fd0ef3b10d31d6df09a7dc498e2507');b=load(p78,'d579ba32a40eed91a336b0015086104e1d1a7c6569092f757328769a3128ab43')
def expression(g):
 d={n:('slot',i) for i,n in enumerate(g['witnesses'])};d.update({n:('port',i) for i,n in enumerate(g['fixed_numerals'])})
 for n,op,x,y in g['source']:d[n]=(op,d[x] if isinstance(x,str) else ('lit',x),d[y] if isinstance(y,str) else ('lit',y))
 return d
x,y=expression(a),expression(b)
for field in ('A0','A1','g72','guard'):assert x[field]==y[field]
def depends(t,index):
 return (t==('slot',index)) if t[0] in ('slot','port','lit') else depends(t[1],index) or depends(t[2],index)
assert all(not depends(x[n],11) for n in ('A0','A1','g72','guard'))
def calc(g,v):
 w=v.copy()
 for n,op,x,y in g['source']:
  x=w[x] if isinstance(x,str) else x;y=w[y] if isinstance(y,str) else y
  w[n]=x+y if op=='+' else x-y if op=='-' else x*y
 return w
rng=random.Random(781179)
for _ in range(200):
 slots=[rng.randrange(1,5) for _ in range(14)];ports=[rng.randrange(1,5),rng.randrange(-4,5),rng.randrange(-4,5),rng.randrange(-4,5)]
 va={name:slots[i] for i,name in enumerate(a['witnesses'])};va.update({name:ports[i] for i,name in enumerate(a['fixed_numerals'])});old=calc(a,va)
 vb={name:slots[i] for i,name in enumerate(b['witnesses'])};vb.update({name:ports[i] for i,name in enumerate(b['fixed_numerals'])});vb['y']=old['V']+va['u'];new=calc(b,vb)
 assert all(old[n]==new[n] for n in ('A0','A1','Fa','g72','guard','guarded_out'))
 direct_y=rng.randrange(-8,9);vb['y']=direct_y;new=calc(b,vb);va['u']=direct_y-new['V'];old=calc(a,va)
 assert all(old[n]==new[n] for n in ('A0','A1','Fa','g72','guard','guarded_out'))
source=H/'AuxGraphEquivalence.lean';s=source.read_text()
for n in ('putAux_self','putAux_positive','common_fields','other_fields_ignore_aux','old_aux_eval','new_aux_eval','old_output_eval','new_output_eval','positive_zero_iff','positive_zero_iff_natural_ports'):
 assert re.search(r'\btheorem\s+'+n+r'\b',s)
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
for name in ('ordinary14-aux-graph-norm-client-draft','ordinary14-aux-root-model-draft'):
 p=D/'research'/name;r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60)
 assert not r.stderr and r.stdout==(p/'observation.json').read_bytes()
paths=[source,D/'research/ordinary14-aux-graph-norm-client-draft/GraphNormClient.lean',D/'research/ordinary14-aux-root-model-draft/AuxRootBridge.lean',D/'research/ordinary14-aux-root78-lean-draft/P78AuxRoot.lean',D/'research/ordinary14-direct-pell79-lean-draft/P79DirectPell.lean']
print(json.dumps({'scope':'source inventory, graph dependencies and finite signed controls only; no Lean invocation','signed_controls':200,'sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
