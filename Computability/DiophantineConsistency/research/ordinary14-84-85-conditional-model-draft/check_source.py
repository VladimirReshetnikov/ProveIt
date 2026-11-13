#!/usr/bin/env python3
"""Finite positive-map controls and source inventory, not a Lean check."""
from pathlib import Path
import hashlib, json, random, re, subprocess, sys
D=Path(__file__).resolve().parents[2]; H=Path(__file__).resolve().parent
old=json.loads((D/'research/ordinary14-qcube85-tradeoff/candidate.json').read_bytes())
new=json.loads((D/'research/ordinary14-qcube84-probe/candidate.json').read_bytes())
def calc(g, vals):
 z=vals.copy()
 for name,op,x,y in g['source']:
  x=z[x] if isinstance(x,str) else x; y=z[y] if isinstance(y,str) else y
  z[name]=x+y if op=='+' else x-y if op=='-' else x*y
 return z
rng=random.Random(848501)
for _ in range(200):
 v={x:rng.randint(1,8) for x in new['witnesses']}; v['gamma']=v['w']+rng.randint(1,8)
 p={x:rng.randint(1,8) for x in new['fixed_numerals']}; q=1+v['J']*p['beta']
 a=calc(new,v|p); b={k:v[k] for k in old['witnesses'] if k!='X'}|p; b['X']=q*v['w']; b['gamma']=v['gamma']-v['w']
 assert all(b[x]>0 for x in old['witnesses'])
 c=calc(old,b); assert all(a[x]==c[x] for x in ('A0','A1','Fa','g72','guard','guarded_out'))
 # Reverse map uses the same positive b, and its gamma shift reconstructs v.
 w=b['X']//q; assert b['X']==q*w and w>0
 z={x:b[x] for x in new['witnesses'] if x!='w'}|p; z['w']=w; z['gamma']=b['gamma']+w
 assert all(z[x]>0 for x in new['witnesses'])
 x=calc(new,z); assert all(x[t]==c[t] for t in ('A0','A1','Fa','g72','guard','guarded_out'))
assert 2-2==0  # Without strict gamma>w, the forward new gamma need not be positive.
assert 6%(1+2*2)!=0  # A positive X need not be divisible by q.
s=(H/'ConditionalComparison.lean').read_text()
for n in ('to85_positive','to84_positive','cast_to85','cast_to84','map_84_to_85','map_85_to_84'):
 assert re.search(r'\btheorem\s+'+n+r'\b',s)
assert '(hgamma : v 6<v 12)' in s and '(hdiv : q beta v∣v 6)' in s
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b', re.sub(r'#print axioms.*','',s))
p=D/'research/ordinary14-84-85-ring-client-draft'; r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60)
assert not r.stderr and r.stdout==(p/'observation.json').read_bytes()
paths=[H/'ConditionalComparison.lean',p/'RingComparison.lean',D/'Lean/DiophantineConsistency/Compact44/P72Root.lean']
print(json.dumps({'scope':'finite positive controls and source inventory only; no Lean invocation','positive_map_controls_each_direction':200,'sha256':{str(x.relative_to(D)):hashlib.sha256(x.read_bytes()).hexdigest() for x in paths}},sort_keys=True,indent=2))
