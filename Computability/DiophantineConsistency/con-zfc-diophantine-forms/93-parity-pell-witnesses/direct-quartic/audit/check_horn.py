#!/usr/bin/env python3
"""Independent exact binding of all twelve Horn branches to printed C222 rules."""
import json,pathlib,collections
D=pathlib.Path(__file__).resolve().parent;H=json.loads((D.parent/'horn_shared_source.json').read_text())
def req(x,s):
 if not x:raise ValueError(s)
class P:
 def __init__(self,d):self.d=d if isinstance(d,dict) else ({():d} if d else {})
 def __add__(a,b):
  if not isinstance(b,P):b=P(b)
  d=a.d.copy()
  for k,v in b.d.items():d[k]=d.get(k,0)+v
  return P({k:v for k,v in d.items() if v})
 __radd__=__add__
 def __neg__(a):return P({k:-v for k,v in a.d.items()})
 def __sub__(a,b):return a+-b if isinstance(b,P) else a+-P(b)
 def __mul__(a,b):
  if not isinstance(b,P):b=P(b)
  d=collections.defaultdict(int)
  for k,v in a.d.items():
   for q,w in b.d.items():d[tuple(sorted(k+q))]+=v*w
  return P({k:v for k,v in d.items() if v})
 __rmul__=__mul__
 def __eq__(a,b):return a.d==b.d
 def key(a):return tuple(sorted(a.d.items()))
def var(s):return P({(s,):1})
def parse(ts):return P({tuple(t['monomial']):t['coefficient'] for t in ts if t['coefficient']})
counts=[]
for B in H['branches']:
 name=B['name'];wires=B['wires'];defs={parse(w['value']).key():w['name'] for w in wires};matched=set()
 def I(a,b):
  s=a+b;p=2*s*(s+1)+4*b;k=p.key()
  if k in defs:matched.add(defs[k]);return var(defs[k])
  return p
 def R(a,b):return I(a,b)+1
 def A(a,b):return I(a,b)+2
 def Eq(a,b):return I(a,b)+3
 def Neg(a):return I(a,P(1))
 def Ex(a,b):return Neg(A(a,Neg(b)))
 def Req(b,k,m):return A(b,I(m,Neg(A(b,I(m,Neg(R(b,k)))))))
 def Clos(a,b,k,m):return A(b,I(R(b,k),Neg(A(a,I(m,Neg(A(a,I(A(k,I(R(k,a),R(k,b))),Req(b,k,m)))))))))
 a,b,c,d,p,q,v=map(var,['a','b','c','d','p','q','v'])
 if name=='truth':h=P(0)
 elif name=='rho1':h=Ex(a,Eq(a,b))
 elif name=='rho2':h=I(A(a,I(b,c)),I(A(a,b),A(a,c)))
 elif name=='rho3':h=I(Eq(a,b),I(R(c,a),R(c,b)))
 elif name=='rho4':h=I(A(a,A(b,c)),A(b,A(a,c)))
 elif name=='rho5':h=I(Eq(c,a),I(R(c,b),R(a,b)))
 elif name=='rho6':h=I(Ex(a,A(a,b)),b)
 elif name=='growG':h=I(Eq(c,a),I(Eq(c,b),A(R(a,b),Eq(a,b))))
 elif name=='rho8':h=I(I(I(c,d),a),I(I(a,c),I(b,c)))
 elif name=='bundle':h=Neg(I(I(R(a,b),A(c,R(a,b))),A(c,I(Clos(a,b,c,c),Neg(Req(b,c,c))))))
 elif name=='mp':h=I(p,v)
 elif name=='gen':h=A(a,p)
 else:raise ValueError(name)
 rows=[var(w['name'])-parse(w['value']) for w in wires]
 if name=='bundle':rows.append((c-a)*(c-b)*(c-a)*(c-b)-(d+1)*(d+1))
 if name=='mp':rows.append(q-h)
 elif name=='gen':rows.extend([q,v-h])
 else:rows.extend([p,q,v-h])
 actual=[parse(r) for r in B['quadratic_residuals']]
 req(len(rows)==len(actual),name+'rowcount');req(all(x==y for x,y in zip(rows,actual)),name+'literalrule');req(matched=={w['name'] for w in wires},name+'orphanwire')
 known={'a','b','c','d','p','q','v'}
 for w in wires:
  ts=parse(w['value']).d;req(all(co>0 for co in ts.values()),'negative constructor');req(all(set(m)<=known for m in ts),'nontopologicalwire');known.add(w['name'])
 counts.append({'branch':name,'constructor_wires':len(wires),'exact_rows':len(rows)})
out={'status':'PASS','branches':counts,'scope':'Exact polynomial binding to independently transcribed Code254/KCode222 rules; all constructor wires nonnegative and topological; bundle guard exactly ((c-a)(c-b))^2=(d+1)^2. This supplies two-way existential Horn equivalence, not merely sampled agreement.'}
(D/'HORN_CHECK.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
