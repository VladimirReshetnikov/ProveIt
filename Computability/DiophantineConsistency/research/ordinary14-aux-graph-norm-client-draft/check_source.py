#!/usr/bin/env python3
"""Source and exact bounded graph controls; never invokes Lean."""
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
for field in ('A0','A1','g72'):assert expression(a)[field]==expression(b)[field]
def calc(g,v):
 w=v.copy()
 for n,op,x,y in g['source']:
  x=w[x] if isinstance(x,str) else x;y=w[y] if isinstance(y,str) else y
  w[n]=x+y if op=='+' else x-y if op=='-' else x*y
 return w
rng=random.Random(787900)
for _ in range(100):
 slots=[rng.randrange(1,5) for _ in range(14)];ports=[rng.randrange(1,5),rng.randrange(-4,5),rng.randrange(-4,5),rng.randrange(-4,5)]
 env={name:slots[i] for i,name in enumerate(a['witnesses'])};env.update({name:ports[i] for i,name in enumerate(a['fixed_numerals'])});u=calc(a,env)
 env2={name:slots[i] for i,name in enumerate(b['witnesses'])};env2.update({name:ports[i] for i,name in enumerate(b['fixed_numerals'])});v=calc(b,env2)
 assert all(u[n]==v[n] for n in ('A0','A1','g72'))
 J,F,alpha,f,i,T,w,s,tau,eta,zeta,_,gamma,h=slots;beta,K0,MC,MF=ports
 q=1+J*beta;X=q*w;Y=q**3*s;U=Y*q*q;k=eta+zeta;ar=X*Y+Y;c=eta+Y*k;delta=3+4*ar+ar*ar;ell=X*Y*Y*k
 R=(alpha+(q-F)*J*beta)*(q*q-1)+J*(MC+MF*q);Z=U*(X+ar*c)+(3+4*ar)*(U*gamma-(k-R-1));Q=delta*(f*f-1);z=f*f*(T*c-R)-c
 assert q>0 and X>0 and Y>0 and U>0
 assert u['A0']==tau*tau-(1+ell*(ell+k)) and u['A1']==Z*Z-U*U*(1+delta*c*c)
 assert u['g72']==(i*c*c)**2-Q and u['V']==z and u['Q']==Q
 for g in (u,v):assert g['guarded_out']==g['A0']**2+g['A1']**2+(g['Fa']-1)**2+g['g72']**2+g['guard']**2
source=H/'GraphNormClient.lean';s=source.read_text()
for n in ('first_eval','main_eval','strong_eval','fields_of_zero','common_norm_fields','fields_of_78_zero','bounds_of_fields','bounds_of_79_positive_zero','bounds_of_78_positive_zero'):
 assert re.search(r'\btheorem\s+'+n+r'\b',s)
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
paths=[source,D/'research/ordinary14-direct-pell79-lean-draft/P79DirectPell.lean',D/'research/ordinary14-aux-root78-lean-draft/P78AuxRoot.lean',D/'research/ordinary14-aux-ring-norm-extraction-draft/RingNormExtraction.lean',D/'research/ordinary14-direct-first-root-model-draft/FirstRootBridge.lean']
print(json.dumps({'scope':'source inventory, graph structure and finite controls only; no Lean invocation','graph_controls':100,'sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
