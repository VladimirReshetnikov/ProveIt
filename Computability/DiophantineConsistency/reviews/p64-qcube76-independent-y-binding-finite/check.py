#!/usr/bin/env python3
"""Exact-integer sanity check of the unchecked independent-y ring interfaces."""
import hashlib,json,random,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
here=Path(__file__).resolve().parent; root=here.parents[1]/'research'
files={'old':('p64-qcube77-candidate/graph.json','8cda8e5729f7af6b725631a0a9a5b5d8886c24a4e62d94d889ada47ce54e7315'),
       'new':('p64-qcube76-independent-y-candidate/graph.json','196ef3bdf6805c7ed7d44c278359e32c0f658634db357cc19f0e87464ed6b11c'),
       'binding':('fourteen-p64-qcube76-independent-y-binding-draft/P64QCube76YBinding.lean','917aece0aa983dcd5947baed77eb80725d3f99e2b4fd5ca4cac0901c1adadfc6')}
raw={}
for name,(rel,h) in files.items():
    b=(root/rel).read_bytes()
    if hashlib.sha256(b).hexdigest()!=h: raise RuntimeError('input hash drift: '+name)
    raw[name]=b
old,new=json.loads(raw['old']),json.loads(raw['new'])
if old['witnesses'][12]!='e' or new['witnesses'][12]!='y' or new['source']!=[r for r in old['source'] if r[0]!='y']:
    raise RuntimeError('graph layout mismatch')
def evaluate(rows,init):
    env=dict(init)
    def val(x): return x if isinstance(x,int) else env[x]
    for name,op,a,b in rows:
        x,y=val(a),val(b)
        env[name]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()
    return env
rng=random.Random(0x76B1); negative=positive=zeros=0
for _ in range(600):
    v={n:rng.randint(1,8) for n in old['witnesses']}
    p={n:rng.randint(0,8) for n in old['fixed_numerals']}
    state=evaluate(old['source'],v|p)
    qm=p['beta']*v['J']; q=qm+1; Y=q*q*q*v['s']; c=(v['eta']+v['zeta'])*Y+v['eta']
    rank=(qm*(q-v['F'])+v['alpha'])*(q*q-1)+(p['MC']+q*p['MF'])*v['J']
    signedV=v['f']*v['f']*(c*v['T']-rank)-c
    if signedV!=state['V']: raise RuntimeError('explicit oldV mismatch')
    rootval=signedV+v['e']
    negative+=rootval<0; positive+=rootval>0; zeros+=rootval==0
    for root in (rootval,-rootval):
        vv={n:v[n] for n in new['witnesses'] if n!='y'}; vv['y']=root
        changed=evaluate(new['source'],vv|p)
        if any(changed[n]!=state[n] for n in ('A0','M','W','Na','Lt','polynomial')):
            raise RuntimeError('binding or sign-invariance mismatch')
example={name:1 for name in old['witnesses']}
example_ports={'beta':2,'K0':2,'MC':1,'MF':1}
example_state=evaluate(old['source'],example|example_ports)
if example_state['Lt']!=0 or example_state['V']!=-44 or example_state['y']!=-43 or example_state['W']==0:
    raise RuntimeError('transport-only negative-root example mismatch')
result={'status':'PASS_FINITE_INTEGER_ONLY','script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'input_hashes':{name:h for name,(_,h) in files.items()},'samples':600,
        'negative_old_roots':negative,'positive_old_roots':positive,'zero_old_roots':zeros,
        'transport_zero_negative_root_example':{'all_witnesses':1,'beta':2,'K0':2,'MC':1,'MF':1,'old_V':-44,'old_y':-43,'strong_residual_nonzero':True},
        'scope':'Integer graph samples including signed values; no Lean elaboration, zero-specific positivity or equivalence.'}
out=here/'result.json'; text=json.dumps(result,indent=2,sort_keys=True)+'\n'
if sys.argv[1:]==['--write']:
    with out.open('x') as f:f.write(text)
elif sys.argv[1:]: raise SystemExit('usage: python3 -I -S -B check.py [--write]')
elif out.read_text()!=text: raise SystemExit('result differs')
print(json.dumps(result,sort_keys=True))
