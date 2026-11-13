#!/usr/bin/env python3
"""Independent graph and sparse-polynomial degree audit."""
import hashlib,itertools,json
from pathlib import Path
root=Path(__file__).resolve().parents[2];here=Path(__file__).resolve().parent
for name,digest in json.loads((here/'pins.json').read_text()).items():assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest,name
nine=json.loads((root/'research/ordinary9-shifted-free-aux-two-norm64/candidate.json').read_text())
free=json.loads((root/'research/ordinary13-shifted85-free-aux-square-criterion/candidate.json').read_text())
assert len(nine['witnesses'])==9 and len(nine['source'])==64 and nine['domain']=='nonnegative integers'
assert nine['fixed_numerals']==free['fixed_numerals']==['beta','K0','MC','MF']
# Construct exact expression trees by input names, independent of row labels.
def expression(g):
 names=g['witnesses']+g['fixed_numerals'];assert len(names)==len(set(names))
 env={x:('input',x) for x in names};rowmap={}
 for name,op,x,y in g['source']:
  assert name not in env and op in ('+','-','*')
  xx=env[x] if isinstance(x,str) else ('constant',x)
  yy=env[y] if isinstance(y,str) else ('constant',y)
  env[name]=(op,xx,yy);rowmap[name]=(x,y)
 return env,rowmap
n,rows=expression(nine);f,_=expression(free)
for name in ('A0','A1'):assert n[name]==f[name]
assert nine['source'][-3:]==[['A0sq','*','A0','A0'],['A1sq','*','A1','A1'],['out','+','A0sq','A1sq']]
stack=['out'];live=set();used=set()
while stack:
 item=stack.pop()
 if not isinstance(item,str):continue
 if item in nine['witnesses']:used.add(item)
 if item in rows and item not in live:live.add(item);stack.extend(rows[item])
assert len(live)==64 and used==set(nine['witnesses'])
# Generic ordinary integer unit exclusions, including beta=0 and negative rank.
for b,z,x,s,k in itertools.product(range(4),repeat=5):
 Y=(1+b)**3*s;ell=x*Y*Y*k
 assert (1+z*z-b*b*(1+ell*(ell+k)))%4!=3
for U,a,c,d in itertools.product(range(4),repeat=4):
 assert (1+d*d-U*U*(1+(a*a+4*a+3)*c*c))%4!=3
# A generic sparse-polynomial ring; its exponents may index any chosen variables.
def add(x,y,sgn=1):
 out=x.copy()
 for k,v in y.items():out[k]=out.get(k,0)+sgn*v
 return {k:v for k,v in out.items() if v}
def mul(x,y):
 out={}
 for ex,v in x.items():
  for ey,w in y.items():
   k=tuple(a+b for a,b in zip(ex,ey));out[k]=out.get(k,0)+v*w
 return {k:v for k,v in out.items() if v}
def unit(i,n):return {tuple(int(k==i) for k in range(n)):1}
def scalar(v,n):return {(0,)*n:v} if v else {}
U,X,a,c,H,S=[unit(i,6) for i in range(6)];one=scalar(1,6);two=scalar(2,6)
B=add(X,mul(a,c));D=add(mul(U,B),mul(H,S));Delta=add(mul(a,a),H)
left=add(mul(D,D),mul(mul(U,U),add(one,mul(Delta,mul(c,c)))),-1)
inner=add(add(add(mul(X,X),mul(two,mul(mul(X,a),c))),one,-1),mul(H,mul(c,c)),-1)
right=add(add(mul(mul(U,U),inner),mul(two,mul(mul(mul(U,B),H),S))),mul(mul(H,H),mul(S,S)))
assert left==right
# Direct graph degree bound on A0 and cancellation-dependent A1 upper bound.
deg={x:1 for x in nine['witnesses']};deg.update({x:0 for x in nine['fixed_numerals']})
for name,op,x,y in nine['source']:
 dx=deg[x] if isinstance(x,str) else 0;dy=deg[y] if isinstance(y,str) else 0
 deg[name]=dx+dy if op=='*' else max(dx,dy)
assert [deg[x] for x in ('U','X','a','c','H','shift','A0')]==[6,2,6,5,6,7,24]
U0,X0,a0,c0,H0,S0=[deg[x] for x in ('U','X','a','c','H','shift')]
assert (2*U0+max(2*X0,X0+a0+c0,H0+2*c0),U0+max(X0,a0+c0)+H0+S0,2*H0+2*S0)==(28,30,26)
# A fresh two-variable (t,beta) exact expansion on the specified ray.
P={k:{} for k in nine['witnesses']+nine['fixed_numerals']};P['beta']=unit(1,2)
for name in ('n_J','n_w','n_s','n_eta','n_gamma'):P[name]=unit(0,2)
for name,op,x,y in nine['source']:
 x=P[x] if isinstance(x,str) else scalar(x,2);y=P[y] if isinstance(y,str) else scalar(y,2)
 P[name]=mul(x,y) if op=='*' else add(x,y,1 if op=='+' else -1)
assert max(i for i,j in P['A1'])==30 and {e:v for e,v in P['A1'].items() if e[0]==30}=={(30,21):8}
assert max(i for i,j in P['out'])==60 and {e:v for e,v in P['out'].items() if e[0]==60}=={(60,42):64}
print(json.dumps({'live_witnesses':len(used),'live_operations':len(live),
 'exact_ordered_norm_trees_equal':True,'first_main_unit_cases':1280,
 'generic_A1_cancellation_identity':True,'A0_degree_bound':24,
 'A1_degree_bound_from_identity':30,'leading_ray_coefficient':'64*beta^42',
 'degree_exact_for_fixed_nonzero_beta':60,
 'zero_equivalence_scope':'standard integer shifted free-y² child only',
 'original_parent_reverse_proved':False,'Lean_executed':False},indent=2,sort_keys=True))
