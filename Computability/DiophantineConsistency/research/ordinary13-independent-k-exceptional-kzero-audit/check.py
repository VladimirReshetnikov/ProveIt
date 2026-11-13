from pathlib import Path
from hashlib import sha256
import itertools,json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-independent-k-exceptional-kzero-audit')
for path,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(path).read_bytes()).hexdigest()==h,path
# Exact syntax of all four unit factors in the independent-k graph.
graph=json.loads(Path('research/ordinary13-eta-zeta84-independent-k-candidate/candidate.json').read_text());table={}
def node(*xs):
 if xs not in table:table[xs]=len(table)
 return table[xs]
def num(n):return node('num',n)
def add(x,y):return node('+',x,y)
def sub(x,y):return node('-',x,y)
def mul(x,y):return node('*',x,y)
d={}
for i,name in enumerate(graph['witnesses']):d[name]=node('v',i)
for i,name in enumerate(graph['fixed_numerals']):d[name]=node('p',i)
for name,op,l,r in graph['source']:
 a=d[l] if isinstance(l,str) else num(l);b=d[r] if isinstance(r,str) else num(r)
 d[name]={'+':add,'-':sub,'*':mul}[op](a,b)
one=num(1);three=num(3);four=num(4)
b,z,x,s,k,U,a,c,root,y,vv,f,I=(d[n] for n in ['qm','Z','X','s','n_k','U','a','c','Dstar','n_y','V','n_f','I'])
q0=add(one,b);Y=mul(mul(q0,mul(q0,q0)),s);ell=mul(mul(x,Y),mul(Y,k))
first=add(one,sub(mul(z,z),mul(mul(b,b),add(one,mul(ell,add(ell,k))))))
D0=add(add(three,mul(four,a)),mul(a,a));Q=mul(D0,sub(mul(f,f),one))
main=add(one,sub(mul(root,root),mul(mul(U,U),add(one,mul(D0,mul(c,c))))))
aux=sub(mul(y,y),mul(Q,sub(mul(y,y),mul(vv,vv))))
strong=add(one,sub(mul(I,I),Q))
assert (d['F0'],d['F1'],d['Fa'],d['Fs'])==(first,main,aux,strong)
assert d['out']==sub(mul(mul(mul(first,main),aux),strong),one)
for b,z,x,s,k in itertools.product(range(4),repeat=5):
 Y=(1+b)**3*s;ell=x*Y*Y*k
 assert (1+z*z-b*b*(1+ell*(ell+k)))%4!=3
for u,a,c,d0 in itertools.product(range(4),repeat=4):
 delta=3+4*a+a*a
 assert (1+d0*d0-u*u*(1+delta*c*c))%4!=3
for y,v,a,f in itertools.product(range(4),repeat=4):
 delta=3+4*a+a*a
 assert (y*y-delta*(f*f-1)*(y*y-v*v))%4!=3
for I,a,f in itertools.product(range(4),repeat=3):
 delta=3+4*a+a*a
 assert (1+I*I-delta*(f*f-1))%4!=3

# Polynomial certificate of the exceptional rank residue. Variables q,
# qF,t,J,MC,MF; beta*J=q-1 and alpha=qF+t.
N=6;z=(0,)*N
class P:
 def __init__(self,d):self.d={k:v for k,v in d.items() if v}
 def __add__(self,o):
  o=pol(o);r=self.d.copy()
  for k,v in o.d.items():r[k]=r.get(k,0)+v
  return P(r)
 __radd__=__add__
 def __neg__(self):return P({k:-v for k,v in self.d.items()})
 def __sub__(self,o):return self+-pol(o)
 def __rsub__(self,o):return pol(o)+-self
 def __mul__(self,o):
  o=pol(o);r={}
  for k,v in self.d.items():
   for j,w in o.d.items():
    key=tuple(a+b for a,b in zip(k,j));r[key]=r.get(key,0)+v*w
  return P(r)
 __rmul__=__mul__
 def __eq__(self,o):return self.d==pol(o).d
def pol(x):return x if isinstance(x,P) else P({z:x})
def var(i):
 e=[0]*N;e[i]=1;return P({tuple(e):1})
q,qF,t,J,MC,MF=(var(i) for i in range(N));alpha=qF+t;b=q-1
R=(alpha+qF*b)*(q*q-1)+J*(MC+q*MF);u=J*MC+1-t
assert R+1-u==q*(qF*(q*q-1)+t*q+J*MF)
# Check exactly the relevant compact top-digit and kernel source recipes.
support_src=Path('Lean/DiophantineConsistency/Compact44/CompactConcreteMask.lean').read_text()
for token in ['range 943 ∪ Ico 983 993 ∪ Ico 1003 1012 ∪ Ico 1013 1032','{1063,1064,1095,2195,3296}) \\ {1}']:
 assert token in support_src,token
support=(set(range(943))|set(range(983,993))|set(range(1003,1012))|set(range(1013,1032))|{1063,1064,1095,2195,3296})-{1}
assert 8806 not in support and 8806!=1063 and max(support)==3296
ls=Path('Lean/DiophantineConsistency/Compact44/CompactListMask.lean').read_text()
assert 'if j=special then B-4 else if j∈S then B-2 else B-1' in ls
assert 'Nat.ofDigits B ((List.range n).map f) = ∑ j ∈ range n, f j * B^j' in ls
ports=Path('Lean/DiophantineConsistency/Compact44/CompactSymbolicPorts.lean').read_text()
assert 'def lowNat : ℕ := Nat.ofDigits (2^67) (CompactListMask.digits (2^67) 8807 1063 CompactConcreteMask.support)' in ports
beta=Path('Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean').read_text()
assert 'def betaNat : ℕ := 2^(67*8807)-1' in beta and '0<β ∧ L<β' in beta
kernel=Path('Lean/DiophantineConsistency/Compact44/CompactSymbolicKernelOpaque.lean').read_text()
assert 'r^30+r^62+r^1100+r^2201' in kernel
assert 'def rho : ℕ := 2^67' in Path('Lean/DiophantineConsistency/Compact44/CompactSymbolicKernel.lean').read_text()
assert 2**67>6 and 67*8807==590069
# Finite controls for the final interval; this is not the proof of it.
cases=0
for beta0 in (7,15,31,63,127):
 for mc0 in range(beta0):
  if 6*mc0<=5*beta0:continue
  for j in range(1,8):
   q0=1+j*beta0
   for tt in range((q0-2)//7+1):
    u0=j*mc0+1-tt
    assert 2*q0<3*u0<3*q0 and (3*u0)%q0!=0
    cases+=1
print(json.dumps({'exact_four_unit_factor_syntax_and_mod4_exclusions':True,'exact_exceptional_rank_residue_identity':True,'compact_mask_top_digit_index':8806,'compact_top_digit_is_B_minus_1':True,'fixed_kernel_contains_rho_pow_30':True,'abstract_interval_controls':cases,'no_full_graph_zero_asserted':True,'model_formalization_or_provider_replay':False,'lean_executed':False},sort_keys=True,indent=2))
