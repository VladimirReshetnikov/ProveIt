"""Root independent inputless circuit audit. No upstream code execution."""
import json,random,runpy
from pathlib import Path
from collections import Counter
root=Path(__file__).resolve().parents[1]
p=json.loads((root/'diophantine_zfc_review/start_only_polynomial67.json').read_text())
s=json.loads((root/'diophantine_zfc_review/start_only_system61.json').read_text())
def req(c,m):
 if not c:raise ValueError(m)
def ev(rows,values):
 v=dict(values)
 for n,o,a,b in rows:
  a=v[a] if isinstance(a,str) else a;b=v[b] if isinstance(b,str) else b
  v[n]=a+b if o=='+' else a-b if o=='-' else a*b
 return v
rng=random.Random(670061)
req(len(p['witnesses'])==15 and len(p['source'])==67,'polynomial ledger')
req(len(s['source'])==61 and len(s['comparisons'])==6,'system ledger')
for j in range(128):
 v={n:rng.randrange(1,9) for n in p['witnesses']};v.update(Bm1=15,Kconstant=137,MC=2,MF=19)
 a=ev(p['source'],v);b=ev(s['source'],v)
 req(all(a[k]==x for k,x in b.items()),'shared subcircuits')
 q=a['q'];C=q-v['F']-v['alpha'];R=(q*q-C-q*v['F'])*(q*q-1)+(v['MC']+q*v['MF'])*v['Jrep']
 req(a['marked_rhs']==C if 'marked_rhs' in a else a['C_after_alpha']==C,'source word')
 req(a['r_lhs']==R,'packing identity')
 unscaled=a['L16']-a['A']*v['i']**2*a['R10a']**4
 product=1
 for n in p['factor_names']:
  if n!='norm_strong':product*=a[n]
 req(a['polynomial']==a['A']*(product*unscaled-1),'scaling identity')
def plus(a,b,sign,m):
 c=[0]*max(len(a),len(b))
 for i,x in enumerate(a):c[i]+=x
 for i,x in enumerate(b):c[i]+=sign*x
 c=[x%m for x in c]
 while len(c)>1 and c[-1]==0:c.pop()
 return c
def times(a,b,m):
 c=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]=(c[i+j]+x*y)%m
 while len(c)>1 and c[-1]==0:c.pop()
 return c
diag=[]
for prime in (1000000007,1000000009):
 v={n:[rng.randrange(1,10),rng.randrange(1,10)] for n in p['witnesses']};v.update({n:[x] for n,x in dict(Bm1=15,Kconstant=137,MC=2,MF=19).items()})
 leading={n:x[-1] for n,x in v.items()}
 for n,o,a,b in p['source']:
  a=v[a] if isinstance(a,str) else [a];b=v[b] if isinstance(b,str) else [b]
  v[n]=times(a,b,prime) if o=='*' else plus(a,b,1 if o=='+' else -1,prime)
 ds=[len(v[n])-1 for n in p['factor_names']]
 req(ds==[22,18,60,7,2,46] and len(v['polynomial'])-1==155,'degree diagnostic')
 z=leading;Q=15*z['Jrep'];k=z['eta']+z['zeta'];C=Q-z['F']-z['alpha'];Nt=z['w']*C-z['transport_quotient']*Q
 lead=-8*pow(Q,91,prime)*z['h']*z['gamma']*z['i']**4*pow(k,13,prime)*pow(z['w'],13,prime)*pow(z['s'],26,prime)*Nt*z['auxiliary_quotient']**2*z['f']**2
 req(v['polynomial'][-1]==lead%prime,'uniform leading-form diagnostic')
 diag.append({'prime':prime,'degree':155,'factor_degrees':ds,'leading_form_agrees':True})
receipt={'signed_arithmetic_fixtures':128,'univariate_diagnostics':diag,'polynomial':{'operations':67,'M':39,'A':28,'positive_witnesses':15},'system':{'operations':61,'M':34,'A':27,'equations':6},'scope':'Independent finite arithmetic checks, not full compiler execution or formal proof. Numeric fixture constants are not the actual compiler instance.'}
(root/'diophantine_zfc_root/ROOT_INPUTLESS_AUDIT.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
