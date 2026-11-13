from pathlib import Path
from hashlib import sha256
import json,sys,random,math
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-free-aux-square-compact-factor-obstruction')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
parent=json.loads(Path('research/ordinary13-eta85-zeta-zero-boundary-audit/probe.json').read_text())
assert len(parent['source'])==85 and parent['witnesses'][11]=='n_y'
rows=[]
for n,op,a,b in parent['source']:
 if n=='y2':assert [n,op,a,b]==['y2','*','n_y','n_y'];continue
 a='n_y2' if a=='y2' else a;b='n_y2' if b=='y2' else b
 rows.append([n,op,a,b])
witnesses=parent['witnesses'].copy();witnesses[11]='n_y2'
child={'name':'free auxiliary-square boundary probe; no zero-equivalence claimed','domain':parent['domain'],'witnesses':witnesses,'fixed_numerals':parent['fixed_numerals'],'source':rows,'output':parent['output']}
assert len(rows)==84
encoded=(json.dumps(child,indent=2)+'\n').encode()
if '--write' in sys.argv:(D/'candidate.json').write_bytes(encoded)
else:assert (D/'candidate.json').read_bytes()==encoded
def ev(g,v,p,mod=None):
 d=dict(zip(g['witnesses'],v));d.update(zip(g['fixed_numerals'],p))
 for n,op,x,y in g['source']:
  x=d[x] if isinstance(x,str) else x;y=d[y] if isinstance(y,str) else y
  z={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()
  d[n]=z if mod is None else z%mod
 return d
rng=random.Random(57123)
for _ in range(300):
 v=[rng.randrange(12) for i in range(13)];p=[rng.randrange(-4,8) for i in range(4)];u=v.copy();u[11]=v[11]**2
 x=ev(parent,v,p,1000000007);y=ev(child,u,p,1000000007)
 assert all(x[n]==y[n] for n in ('A0','A1','Q','g72','Fa','out'))
# Fixed-compact gcd argument: c=(a+2)^2+1; a=q³(q+1).
N=67*8807;assert pow(2,N,17)==15 and pow(2,N,5)==2
assert math.gcd(15-1,17)==1 and math.gcd(2+1,5)==1
src=Path('Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean').read_text()
assert 'def betaNat : ℕ := 2^(67*8807)-1' in src
p=Path('Lean/DiophantineConsistency/Compact44/CompactSymbolicPorts.lean').read_text();assert '![β,K,L,β+H]' in p
# Exact identities in Z[Delta,I]. The first is strong, the second auxiliary.
Z=(0,0)
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
def pol(x):return x if isinstance(x,P) else P({Z:x})
I=P({(0,1):1});z=I*I*I*I-3*I*I+1;V=I*I-2
assert z-I*I*(z-V*V)==1
assert z-V*V==I*I-3 and (I*I-1)*(I*I-1)-z==I*I
# Complete graph control at small noncompact q=2. Find a genuine Pell
# identity period modulo c², then obtain the exact huge f and free y².
q=2;beta=q-1;Y=q**3;X=0;a=Y*(X+1);A=a+2;Delta=A*A-1;c=Delta+2;C=q*q-1;MC=MF=0
assert math.gcd(C,c)==1
B=beta*beta*C+MC+q*MF;alpha=1+(((2-B)*pow(C,-1,c)-1)%c)
R=(alpha+beta*beta)*C+MC+q*MF;assert R%c==2
mod=c*c;x,y=1,0
for h in range(1,10000):
 x,y=(A*x+Delta*y)%mod,(x+A*y)%mod
 if (x,y)==(1,0):break
else:raise AssertionError('toy period limit')
def pell_pow(A,n):
 D0=A*A-1;x,y=1,0;u,v=A,1
 while n:
  if n&1:x,y=x*u+D0*y*v,x*v+y*u
  u,v=u*u+D0*v*v,2*u*v;n//=2
 return x,y
f,v=pell_pow(A,h);assert v>0 and v%(c*c)==0 and f*f==1+Delta*v*v
i=Delta*(v//(c*c));I=i*c*c;T=(R+Delta)//c;assert (R+Delta)%c==0 and T>=1
z=I**4-3*I*I+1;V=I*I-2;k,eta=divmod(c,Y);zeta=k-eta
assert i>0 and zeta>=0 and (I*I-2)**2<z<(I*I-1)**2
vals=[1,0,alpha-1,f,i-1,T-1,0,0,0,eta,zeta,z,0];ports=[beta,1,MC,MF]
d=ev(child,vals,ports)
assert d['R']==R and d['c']==c and d['I']==I and d['V']==V
assert d['g72']==0 and d['Fa']==1 and d['A0']!=0 and d['A1']!=0
print(json.dumps({'parent_rows':85,'candidate_rows':84,'forward_square_substitution_controls':300,'fixed_compact_q_mod17':15,'fixed_compact_q_mod5':2,'rank_modulus_coprimality_argument':'source exponents and q even','strong_aux_exact_polynomial_identity':True,'toy_q':q,'toy_period':h,'toy_f_bit_length':f.bit_length(),'toy_nonsquare_y2_bit_length':z.bit_length(),'toy_full_graph_strong_and_aux_checked':True,'toy_first_main_residual_nonzero':True,'fixed_compact_full_zero_claim':False,'lean_executed':False},sort_keys=True,indent=2))
