#!/usr/bin/env python3
"""Independent exact graph, sparse identities, degree and coefficient checks."""
from collections import Counter
from hashlib import sha256
import gzip,json,random
from pathlib import Path
D=Path(__file__).resolve().parents[2]
OLD=D/'research/ordinary12-qcube92-candidate/candidate.json'
NEW=D/'research/ordinary12-xq91-candidate/candidate.json'
COEFF=D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients';BIND=COEFF/'BINDING.json'
PINS={OLD:'3a21d323adb96788a4b46c0b33800e07f2d1cb708b5c3c53ab709f6e186acee3',
 NEW:'fde7510bbc984b7160e92ed5caff260fc90a25c9c24437efbf5c2f40c3f92513',
 BIND:'dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01'}
def need(x,m):
 if not x:raise SystemExit(m)
def sha(p):return sha256(p.read_bytes()).hexdigest()
for p,h in PINS.items():need(sha(p)==h,'input hash mismatch '+str(p))
a=json.loads(OLD.read_text());b=json.loads(NEW.read_text());
need(b['witnesses']==['J','F','alpha','t','T','w','s','r','eta','zeta','n','gamma'],'witness order')
need(a['fixed_numerals']==b['fixed_numerals']==['beta','K0','MC','MF'] and b['domain']==a['domain'] and b['output']==a['output'],'ports/domain/output')
old={r[0]:r[1:] for r in a['source']};new={r[0]:r[1:] for r in b['source']}
need(len(old)==len(a['source'])==92 and len(new)==len(b['source'])==91,'redefined nodes')
need(set(new)==(set(old)-{'g25','g26','g55'})|{'X','kw'},'wrong node-set rewrite')
changes={'X':['*','q','w'],'kw':['+','K0','w'],'g27':['*','C','kw'],'g28':['-','g27','F'],
         'Bt':['*','q','g28'],'g54':['+','gamma','w'],'g56':['*','U','g54']}
for n,row in new.items():
 need(row==(changes[n] if n in changes else old[n]),'node rewrite mismatch '+n)
known=set(b['witnesses']+b['fixed_numerals']);parents={}
for n,op,x,y in b['source']:
 need(n not in known and op in ('+','-','*'),'bad DAG node')
 for z in (x,y):need(type(z) is int or (isinstance(z,str) and z in known),'forward/unknown input')
 known.add(n);parents[n]=(x,y)
live=set();todo=[b['output']]
while todo:
 n=todo.pop()
 if n in parents and n not in live:
  live.add(n);todo.extend(x for x in parents[n] if isinstance(x,str))
counts=dict(Counter(row[1] for row in b['source']))
need(len(live)==91 and live==set(parents) and b['operations']==91 and counts==b['operation_breakdown']=={'*':50,'+':24,'-':17},'count/liveness')
# Polynomials in independent variables (q,w,c,K,F,Y,gamma) over Z.
N=7;zero=(0,)*N
def const(n):return {} if not n else {zero:n}
def var(i):
 x=list(zero);x[i]=1;return {tuple(x):1}
def add(a,b):
 z=dict(a)
 for k,v in b.items():
  z[k]=z.get(k,0)+v
  if not z[k]:del z[k]
 return z
def neg(a):return {k:-v for k,v in a.items()}
def sub(a,b):return add(a,neg(b))
def mul(a,b):
 z={}
 for ka,va in a.items():
  for kb,vb in b.items():
   k=tuple(x+y for x,y in zip(ka,kb));z[k]=z.get(k,0)+va*vb
 return {k:v for k,v in z.items() if v}
q,w,c,K,F,Y,gamma=(var(i) for i in range(N));X=mul(q,w);U=mul(Y,mul(q,q));E=mul(X,Y)
need(sub(mul(c,add(X,mul(K,q))),mul(F,q))==mul(q,sub(mul(c,add(w,K)),F)),'Bt polynomial identity')
need(add(mul(U,gamma),mul(E,q))==mul(U,add(gamma,w)),'g56 polynomial identity')
# Tighten h via its exact cancellation in independent Q,V,n variables.
Q,V,n=(var(i) for i in range(3));one=const(1);vp=add(V,n)
need(add(mul(sub(one,Q),mul(vp,vp)),sub(mul(Q,mul(V,V)),one))==sub(sub(mul(vp,vp),one),mul(mul(Q,n),add(add(V,V),n))),'h polynomial identity')
shape={'vn':['+','V','n'],'vn2':['*','vn','vn'],'polarV2':['*','V','V'],'polarQV2':['*','Q','polarV2'],
       'polarCy':['-','polarQV2',1],'oneQ':['-',1,'Q'],'polarHpart':['*','oneQ','vn2'],'h':['+','polarHpart','polarCy']}
need(all(new[k]==v for k,v in shape.items()),'h source shape')
deg={n:1 for n in b['witnesses']};deg.update({n:0 for n in b['fixed_numerals']})
for n,op,x,y in b['source']:
 dx=deg[x] if isinstance(x,str) else 0;dy=deg[y] if isinstance(y,str) else 0;deg[n]=dx+dy if op=='*' else max(dx,dy)
 if n=='h':
  need((deg['Q'],deg['V'],deg['n'])==(14,8,1),'h degree premises')
  deg[n]=max(2*max(deg['V'],deg['n']),deg['Q']+deg['n']+max(deg['V'],deg['n']))
keys=['Q','V','h','den','polarT','polarA','polarCorrection','N','A0','A1','P12'];upper={n:deg[n] for n in keys}
need(upper=={'Q':14,'V':8,'h':23,'den':20,'polarT':28,'polarA':43,'polarCorrection':78,'N':86,'A0':24,'A1':34,'P12':172},'degree upper mismatch')
# Compute a nonzero leading coefficient after fixed ports and linear witnesses.
p=1000000007;vals={name:[0,i+2] for i,name in enumerate(b['witnesses'])};bind=json.loads(BIND.read_text());payloads={}
for name in b['fixed_numerals']:
 meta=bind['ports'][name];f=COEFF/meta['file'];z=f.read_bytes();raw=gzip.decompress(z)
 need(sha256(z).hexdigest()==meta['sha256_gzip'] and sha256(raw).hexdigest()==meta['sha256_raw'] and len(raw)==meta['raw_bytes'],'payload mismatch '+name)
 vals[name]=[int.from_bytes(raw,'little')%p];payloads[f]=meta['sha256_gzip']
def poly(op,a,b):
 if op=='*':
  z=[0]*(len(a)+len(b)-1)
  for i,x in enumerate(a):
   for j,y in enumerate(b):z[i+j]=(z[i+j]+x*y)%p
 else:z=[((a[i] if i<len(a) else 0)+(1 if op=='+' else -1)*(b[i] if i<len(b) else 0))%p for i in range(max(len(a),len(b)))]
 while len(z)>1 and not z[-1]:z.pop()
 return z
for n,op,x,y in b['source']:vals[n]=poly(op,vals[x] if isinstance(x,str) else [x],vals[y] if isinstance(y,str) else [y])
need(len(vals['P12'])-1==172 and vals['P12'][-1]==960910299,'degree lower mismatch')
def evaluate(g,inputs):
 v=inputs.copy()
 for n,op,x,y in g['source']:
  x=v[x] if isinstance(x,str) else x;y=v[y] if isinstance(y,str) else y
  v[n]={'*':lambda:x*y,'+':lambda:x+y,'-':lambda:x-y}[op]()
 return v
rng=random.Random(91029)
for _ in range(400):
 inputs={k:rng.randrange(1,9) for k in b['witnesses']+b['fixed_numerals']};newv=evaluate(b,inputs)
 oldinputs={k:inputs[k] for k in a['witnesses']+a['fixed_numerals'] if k!='X'};oldinputs['X']=newv['X'];oldv=evaluate(a,oldinputs)
 need(all(oldv[n]==newv[n] for n in ('X','Y','U','E','Bt','g56','A0','A1','N','P12')),'full DAG exact example failed')
for f,h in {**PINS,**payloads}.items():need(sha(f)==h,'input changed '+str(f))
print(json.dumps({'old_live_operations':92,'new_live_operations':91,'breakdown':counts,
 'exact_sparse_polynomial_identities':3,'upper_bounds':upper,'prime':p,
 'degree_lower_witness':{'degree':len(vals['P12'])-1,'leading_coefficient':vals['P12'][-1]},
 'positive_full_graph_examples':400},indent=2))
