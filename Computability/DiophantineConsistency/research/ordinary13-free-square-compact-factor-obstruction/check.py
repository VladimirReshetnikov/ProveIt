from pathlib import Path
from hashlib import sha256
import sys,json,math
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-free-square-compact-factor-obstruction')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
root=Path('Lean/DiophantineConsistency/Compact44')
assert 'def betaNat : ℕ := 2^(67*8807)-1' in (root/'CompactFixedBeta.lean').read_text()
ports=(root/'CompactSymbolicPorts.lean').read_text()
assert 'def ports (β K L H : ℕ) : Fin 4 → ℕ := ![β,K,L,β+H]' in ports
assert '8807 1063 CompactConcreteMask.support' in ports and 'CompactHighPopulation.highDigits' in ports
assert 'abbrev c44 : Fin 4 → ℕ := ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat' in (root/'C44Short15Facts.lean').read_text()
assert 'if j=special then B-4 else if j∈S then B-2 else B-1' in (root/'CompactListMask.lean').read_text()
mask=(root/'CompactConcreteMask.lean').read_text()
assert 'range 943 ∪ Ico 983 993 ∪ Ico 1003 1012 ∪ Ico 1013 1032' in mask and '{1063,1064,1095,2195,3296}) \\ {1}' in mask
hi=(root/'CompactHighPopulation.lean').read_text()
for x in ('def mu : ℕ := 2^51-2','def padding : ℕ := 2^65-1','def lastPadding : ℕ := 2^19-1','[4] ++ List.replicate 1012 0 ++ List.replicate 10 1','List.replicate 42 0 ++ List.replicate 9 1','List.replicate 1121 0 ++ [1] ++ List.replicate 1100 0 ++ [1]','List.replicate 1096 0 ++ [mu] ++ List.replicate 1101 0 ++ [mu]','List.replicate 3296 0 ++ List.replicate 13 padding ++ [lastPadding,0]'):
 assert x in hi
N=67*8807;assert pow(2,N,63)==32 and pow(2,N,15)==2 and pow(2,N,7)==4
rho=pow(2,67,3);q=pow(2,N,3);beta=(q-1)%3
support=(set(range(943))|set(range(983,993))|set(range(1003,1012))|set(range(1013,1032))|{1063,1064,1095,2195,3296})-{1}
MC=sum((rho-4 if j==1063 else rho-2 if j in support else rho-1)*pow(rho,j,3) for j in range(8807))%3
high=[4]+[0]*1012+[1]*10+[0]*42+[1]*9+[0]*1121+[1]+[0]*1100+[1]+[0]*1096+[2**51-2]+[0]*1101+[2**51-2]+[0]*3296+[2**65-1]*13+[2**19-1,0]
assert len(high)==8807
H=sum(x*pow(rho,j,3) for j,x in enumerate(high))%3;MF=(beta+H)%3
assert (q,MC,H,MF,(MC+q*MF)%3)==(2,1,0,1,0)
q7=pow(2,N,7);Y7=q7**3%7;a7=Y7*(q7+1)%7;delta7=((a7+2)**2-1)%7;c7=(4*delta7+3)%7
v7=3*c7*c7%7;L7=(1+delta7*v7*v7)%7
assert (q7,Y7,a7,delta7,c7,v7,L7)==(4,1,5,6,6,3,6)
assert L7 not in {x*x%7 for x in range(7)}
# Verify source-to-candidate wiring.
g=json.loads(Path('research/ordinary13-eta-zeta84-free-square-obstruction/candidate.json').read_text());r={row[0]:row[1:] for row in g['source']}
assert len(g['source'])==84 and g['witnesses'][3]=='n_t'
for n,row in {'f2':['+','n_t',1],'Q':['*','Delta','n_t'],'I':['*','c2','i'],'g72':['-','g71','Q'],'g75':['-','g74','R'],'g76':['*','f2','g75'],'V':['-','g76','c'],'Fa':['-','y2','g82']}.items():assert r[n]==row,(n,r[n])
# Exact finite toy uses the same residue pattern and complete 84-row evaluation.
q=32;beta=q-1;Y=q**3;a=Y*(q+1);delta=(a+2)**2-1;c=4*delta+3;C=q*q-1;MC=1;MF=1;B=beta*beta*C+MC+q*MF
assert math.gcd(C,c)==3 and B%3==0
m=c//3;alpha=1+((((3-B)//3)*pow(C//3,-1,m)-1)%m)
R=(alpha+beta*beta)*C+MC+q*MF;assert R%c==3 and R>=3
k,eta=divmod(c,Y);zeta=k-eta;assert zeta>=0
v=3*c*c;t=delta*v*v;L=t+1;i=3*delta;I=i*c*c;T=1+(R-3)//c;y=4*I*I-1
vals=[1,0,alpha-1,t,i-1,T-1,1,0,0,eta,zeta,y,0];ports=[beta,0,MC,MF]
d=dict(zip(g['witnesses'],vals));d.update(zip(g['fixed_numerals'],ports))
for n,op,x,z in g['source']:
 x=d[x] if isinstance(x,str) else x;z=d[z] if isinstance(z,str) else z
 d[n]={'+':lambda:x+z,'-':lambda:x-z,'*':lambda:x*z}[op]()
assert d['R']==R and d['c']==c and d['I']==I and d['f2']==L and d['Q']==I*I
assert d['g72']==0 and d['Fa']==1 and d['V']==4*I*I-3 and L%7==6
assert d['A0']!=0 and d['A1']!=0
# Exact free-ring algebra, in variables Delta and v.
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
D0=P({(1,0):1});V0=P({(0,1):1});C0=4*D0+3;L0=1+D0*V0*V0;I0=D0*V0
VV=4*I0*I0-3;YY=4*I0*I0-1
assert I0*I0==D0*(L0-1) and VV==L0*(C0-3)-C0
assert YY*YY-I0*I0*(YY*YY-VV*VV)==1
print(json.dumps({'source_residues_mod3':{'q':2,'MC':MC%3,'high':H,'MF':MF%3,'MC_plus_qMF':0},'q_mod63':32,'q_mod15':2,'compact_L_mod7':6,'toy_q':32,'toy_rank_mod_c':3,'toy_strong_residual':0,'toy_auxiliary_factor':1,'toy_first_and_main_residuals_nonzero':True,'full_compact_child_zero_claim':False,'lean_executed':False},sort_keys=True,indent=2))
