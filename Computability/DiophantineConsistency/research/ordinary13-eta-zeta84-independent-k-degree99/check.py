from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-eta-zeta84-independent-k-degree99')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
raw=Path('research/ordinary13-eta-zeta84-independent-k-candidate/candidate.json').read_bytes();g=json.loads(raw);assert len(g['source'])==84
rows={r[0]:r for r in g['source']}
for row in [['qm','*','n_J','beta'],['ell','*','E','kY'],['g30','+','ell','n_k'],['g31','+','g30','n_r'],['folded_kBt','*','n_k','Bt'],['folded_g31','-','g31','folded_kBt'],['g32','*','qm','folded_g31'],['Z','-','g32','Bt'],['g38','*','Z','Z'],['g39','*','qm','qm'],['g40','*','ell','g30'],['g41','+',1,'g40'],['g42','*','g39','g41'],['A0','-','g38','g42'],['g19','*','a','c'],['b0','+','X','g19'],['g58','*','U','b0'],['g59','*','H','shift'],['Dstar','+','g58','g59'],['g17','*','a','a'],['Delta','+','H','g17'],['c2','*','c','c'],['g61','*','Dstar','Dstar'],['g62','*','U','U'],['g63','*','Delta','c2'],['g64','+',1,'g63'],['g65','*','g62','g64'],['A1','-','g61','g65'],['F0','+',1,'A0'],['F1','+',1,'A1'],['Fs','+',1,'g72'],['P01','*','F0','F1'],['P012','*','P01','Fa'],['P0123','*','P012','Fs'],['out','-','P0123',1]]:assert rows[row[0]]==row,row
# Structural total-degree upper bounds, with coefficients/ports degree zero.
deg={n:1 for n in g['witnesses']};deg.update({n:0 for n in g['fixed_numerals']})
for n,op,l,r in g['source']:
 a=deg[l] if isinstance(l,str) else 0;b=deg[r] if isinstance(r,str) else 0
 deg[n]=a+b if op=='*' else max(a,b)
assert {n:deg[n] for n in ('qm','X','Y','U','n_k','c','a','H','Delta','ell','Bt','shift','Fa','Fs','out')}=={'qm':1,'X':2,'Y':4,'U':6,'n_k':1,'c':5,'a':6,'H':6,'Delta':12,'ell':11,'Bt':3,'shift':7,'Fa':30,'Fs':22,'out':110}
# Exact polynomial identities over the free ring for cancellation. Generic
# polynomials are dict monomial exponent tuples -> integer coefficients.
def plus(x,y,sgn=1):
 a=x.copy()
 for k,v in y.items():a[k]=a.get(k,0)+sgn*v
 return {k:v for k,v in a.items() if v}
def times(x,y):
 a={}
 for p,v in x.items():
  for q,w in y.items():
   k=tuple(i+j for i,j in zip(p,q));a[k]=a.get(k,0)+v*w
 return {k:v for k,v in a.items() if v}
def variable(n,i):
 e=[0]*n;e[i]=1;return {tuple(e):1}
def constant(n,k):return {(0,)*n:k} if k else {}
one=constant(5,1);b,e,k,D0,u=[variable(5,i) for i in range(5)]
z=plus(times(b,e),D0)
lhs=plus(times(z,z),times(times(b,b),plus(one,times(e,plus(e,k)))), -1)
rhs=plus(plus(times(times(constant(5,2),times(b,e)),D0),times(D0,D0)),times(times(b,b),plus(one,times(e,k))),-1)
assert lhs==rhs
# Generic main cancellation: U,a,c,H,E are independent ring variables.
U,a,c,H,E=[variable(5,i) for i in range(5)];A=times(times(U,a),c);z=plus(A,E);delta=plus(times(a,a),H)
lhs=plus(times(z,z),times(times(U,U),plus(one,times(delta,times(c,c)))),-1)
rhs=plus(plus(times(times(constant(5,2),A),E),times(E,E)),times(times(U,U),plus(one,times(H,times(c,c)))),-1)
assert lhs==rhs
# The exact structural identities give these global total-degree bounds:
# D=b*(k+r-k*Bt)-Bt ≤5; E=U*X+H*shift ≤13.
Dbound=max(deg['qm']+max(deg['n_k'],deg['n_r'],deg['n_k']+deg['Bt']),deg['Bt'])
Ebound=max(deg['U']+deg['X'],deg['H']+deg['shift'])
first_bound=max(deg['qm']+deg['ell']+Dbound,2*Dbound,2*deg['qm']+max(0,deg['ell']+deg['n_k']))
main_A=deg['U']+deg['a']+deg['c']
main_bound=max(main_A+Ebound,2*Ebound,2*deg['U']+max(0,deg['H']+2*deg['c']))
assert (Dbound,Ebound,first_bound,main_bound)==(5,13,17,30)
upper=first_bound+main_bound+deg['Fa']+deg['Fs'];assert upper==99
# Exact top-20 jet of the univariate ray where every witness equals t.
# Coefficients are sparse polynomials in all four ports. Each gate stores
# every coefficient from (syntactic degree bound−20) through that bound.
# Truncation is sound by induction because no omitted coefficient can
# combine with an input above its own degree bound to reach that interval.
W=20;zz=(0,0,0,0)
def cp(v):return {zz:v} if v else {}
def port(i):return variable(4,i)
def get(x):return jets[x] if isinstance(x,str) else (0,{0:cp(x)})
jets={n:(1,{1:cp(1)}) for n in g['witnesses']};jets.update({n:(0,{0:port(i)}) for i,n in enumerate(g['fixed_numerals'])})
for n,op,l,r in g['source']:
 ld,L=get(l);rd,R=get(r);bound=ld+rd if op=='*' else max(ld,rd);P={}
 if op=='*':
  for i,x in L.items():
   for j,y in R.items():
    if i+j>=bound-W:P[i+j]=plus(P.get(i+j,{}),times(x,y))
 else:
  for i in set(L)|set(R):
   if i>=bound-W:P[i]=plus(L.get(i,{}),R.get(i,{}),1 if op=='+' else -1)
 P={k:v for k,v in P.items() if v};assert P,(n,bound)
 jets[n]=(bound,P)
ray=jets[g['output']][1];lead=max(ray);assert lead==99
assert ray[99]=={(58,0,0,0):-16,(57,0,0,0):32}
assert all(n<=99 for n in ray)
# Independently expand the full t-polynomial at two small special port
# tuples. These are controls for the symbolic-port jet, not the compact proof.
def full_ray(ports):
 d={n:[0,1] for n in g['witnesses']};d.update({n:[ports[i]] for i,n in enumerate(g['fixed_numerals'])})
 def get(x):return d[x] if isinstance(x,str) else [x]
 for n,op,l,r in g['source']:
  a=get(l);b=get(r)
  if op=='*':
   z=[0]*(len(a)+len(b)-1)
   for i,x in enumerate(a):
    for j,y in enumerate(b):z[i+j]+=x*y
  else:
   z=[0]*max(len(a),len(b))
   for i,x in enumerate(a):z[i]+=x
   for i,y in enumerate(b):z[i]+=y if op=='+' else -y
  while len(z)>1 and z[-1]==0:z.pop()
  d[n]=z
 return d[g['output']]
for ports in ([3,0,0,0],[4,-2,3,7]):
 ray_special=full_ray(ports);assert len(ray_special)-1==99
 assert ray_special[-1]==-16*ports[0]**57*(ports[0]-2)
# Parent is obtained by the invertible integral linear change
# child k=parent eta+zeta; inverse parent zeta=child k-eta.
parent=json.loads(Path('research/ordinary13-eta85-zeta-zero-boundary-audit/probe.json').read_text())
assert len(parent['source'])==85 and parent['witnesses'][9:11]==['n_eta','n_zeta']
assert g['witnesses'][9:11]==['n_eta','n_k'] and parent['fixed_numerals']==g['fixed_numerals']
assert [r for r in parent['source'] if 'n_zeta' in r]==[['kbase','+','n_eta','n_zeta']]
transcript=[]
for row in parent['source']:
 if row==['kbase','+','n_eta','n_zeta']:continue
 transcript.append([('n_k' if x=='kbase' else x) for x in row])
assert transcript==g['source']
# Formal 2x2 matrices (eta,zeta)->(eta,k) and inverse have product I.
M=((1,0),(1,1));N=((1,0),(-1,1))
assert tuple(tuple(sum(M[i][t]*N[t][j] for t in range(2)) for j in range(2)) for i in range(2))==((1,0),(0,1))
assert tuple(tuple(sum(N[i][t]*M[t][j] for t in range(2)) for j in range(2)) for i in range(2))==((1,0),(0,1))
assert 67*8807>=3 and 2**3-1>=3
beta=Path('Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean').read_text()
assert 'def betaNat : ℕ := 2^(67*8807)-1' in beta
print(json.dumps({'candidate_sha256':sha256(raw).hexdigest(),'formal_first_main_cancellation_identities':True,'global_total_degree_upper_bound':upper,'all_witnesses_equal_ray_degree':lead,'independent_small_port_full_ray_controls':2,'ray_leading_coefficient':'-16*beta^57*(beta-2)','compact_beta_symbolically_at_least_3':True,'other_port_values_unrestricted':True,'exact_degree_when_beta_at_least_3':99,'parent_exact_degree_by_invertible_linear_change':99,'zero_equivalence_proved':False,'lean_executed':False},sort_keys=True,indent=2))
