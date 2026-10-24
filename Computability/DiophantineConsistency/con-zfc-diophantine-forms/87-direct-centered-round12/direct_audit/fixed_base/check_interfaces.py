#!/usr/bin/env python3
"""Independent exact ring checks of all emitted Pell/power/division call instances."""
import json,pathlib,collections,functools
D=pathlib.Path(__file__).resolve().parent;J=json.loads((D.parent.parent/'direct/fixed_base/circuit.json').read_text());N=J['nodes'];V=J['variable_names'];L=J['call_ledger'];E=J['equalities']
class P:
 def __init__(self,x):self.d=x if isinstance(x,dict) else ({():x} if x else {})
 def __add__(a,b):
  if not isinstance(b,P):b=P(b)
  d=a.d.copy()
  for k,v in b.d.items():d[k]=d.get(k,0)+v
  return P({k:v for k,v in d.items() if v})
 __radd__=__add__
 def __neg__(a):return P({k:-v for k,v in a.d.items()})
 def __sub__(a,b):return a+(-b if isinstance(b,P) else -P(b))
 def __rsub__(a,b):return P(b)-a
 def __mul__(a,b):
  if not isinstance(b,P):b=P(b)
  d=collections.defaultdict(int)
  for k,v in a.d.items():
   for q,w in b.d.items():d[tuple(sorted(k+q))]+=v*w
  return P({k:v for k,v in d.items() if v})
 __rmul__=__mul__
 def __pow__(a,k):
  b=P(1)
  for _ in range(k):b=b*a
  return b
 def __eq__(a,b):return a.d==(b.d if isinstance(b,P) else P(b).d)
def sym(n):return P({(str(n),):1})
def req(x,s):
 if not x:raise ValueError(s)
def norm(a,x,y):return x*x+y*y-a*a*y*y-1
def sos(xs):return sum((p*p for p in xs),P(0))
counts=collections.Counter()
for ci,c in enumerate(L):
 if c['kind'] not in ['pell','pow','divmod']:continue
 cuts={i:sym('arg'+str(i)) for i in c['arguments'] if N[i][0]!='c'}
 nested=[]
 if c['kind']=='pow':
  nested=[p for p in L if p['kind']=='pell' and c['before'][0]<=p['before'][0] and p['after'][0]<=c['after'][0]];req(len(nested)==1,'Pell nesting')
  for i in nested[0]['result']:cuts[i]=sym('Pellpart'+str(i))
 @functools.lru_cache(None)
 def ev(i):
  if i in cuts:return cuts[i]
  n=N[i]
  if n[0]=='c':return P(n[1])
  if n[0]=='v':return sym('v'+str(n[1]))
  return ev(n[1])+ev(n[2]) if n[0]=='a' else ev(n[1])*ev(n[2])
 vv={V[i].rsplit('.',1)[0]:sym('v'+str(i)) for i in range(c['before'][0],c['after'][0])}
 def v(s):return vv[s]
 def mod(a,b,m,name):return a+m*v(name+'.q0')-b-m*v(name+'.q1')
 def lt(a,b,name):return b-a-1-v(name+'.slack')
 def le(a,b,name):return b-a-v(name+'.slack')
 if c['kind']=='pell':
  a,n,x,y=map(ev,c['arguments']);u,w,s,t,b=[v('pell.'+s) for s in ['u','w','s','t','b']]
  finite=sos([norm(a,x,y),norm(a,u,w),norm(b,s,t),lt(1,b,'pell.b'),mod(b,1,4*y,'pell.by'),mod(b,a,u,'pell.ba'),lt(0,w,'pell.w'),w-y*y*v('pell.dvd'),mod(s,x,u,'pell.sx'),mod(t,n,4*y,'pell.tn')])
  want=sos([lt(1,a,'pell.a'),le(n,y,'pell.n')])+sos([x-1,y])*finite
  actual=ev(c['result'][0])-ev(c['result'][1])
 elif c['kind']=='pow':
  n,k=map(ev,c['arguments']);m=ev(c['result']);w,a,t,z,x,y,d=[v('power.'+s) for s in ['w','a','t','z','x','y','truncated_difference']]
  sub=(a-d-n)**2*sos([le(a,n,'power.sub'),d])
  pell=ev(nested[0]['result'][0])-ev(nested[0]['result'][1])
  finite=pell+sub+sos([mod(x,y*d+m,t,'power.mod'),2*a*n-t-n*n-1,lt(m,t,'power.mt'),le(n,w,'power.nw'),le(k,w,'power.kw'),norm(w+1,a,w*z)])
  want=sos([k,m-1])*(lt(0,k,'power.k')**2+sos([n,m])*(lt(0,n,'power.n')**2+finite))
  eq=E[c['after'][1]-1];req(eq[2]=='natural power','powerlabel');actual=ev(eq[0])-ev(eq[1])
 else:
  n,d=map(ev,c['arguments']);q,r=map(ev,c['result']);s=v('division.slack');eqs=E[c['before'][1]:c['after'][1]];req(len(eqs)==2,'divisionrowcount')
  req(ev(eqs[0][0])-ev(eqs[0][1])==n-q*d-r,'divisioneq');want=d-r-s-1;actual=ev(eqs[1][0])-ev(eqs[1][1])
 req(want==actual,c['kind']+' '+str(ci));counts[c['kind']]+=1
out={'status':'PASS','exact_interface_instances':dict(counts),'scope':'Exact emitted polynomial identity against independent finite Pell criterion, all-natural power criterion including zero branches, and positive-divisor Euclidean division. Correctness of Pell criterion imports pinned theorem; this script does not prove it anew.'}
(D/'INTERFACE_CHECK.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
