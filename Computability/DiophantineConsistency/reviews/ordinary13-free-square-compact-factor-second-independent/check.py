from pathlib import Path
from hashlib import sha256
from math import gcd
import json,sys,subprocess
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-free-square-compact-factor-second-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
p=Path('research/ordinary13-free-square-compact-factor-obstruction')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
C=Path('Lean/DiophantineConsistency/Compact44');assert 'def betaNat : ℕ := 2^(67*8807)-1' in (C/'CompactFixedBeta.lean').read_text()
assert 'range 943 ∪ Ico 983 993 ∪ Ico 1003 1012 ∪ Ico 1013 1032' in (C/'CompactConcreteMask.lean').read_text()
assert 'if j=special then B-4 else if j∈S then B-2 else B-1' in (C/'CompactListMask.lean').read_text()
highsrc=(C/'CompactHighPopulation.lean').read_text()
for x in ('[4] ++ List.replicate 1012 0 ++ List.replicate 10 1', 'List.replicate 42 0 ++ List.replicate 9 1','List.replicate 1121 0 ++ [1] ++ List.replicate 1100 0 ++ [1]','List.replicate 1096 0 ++ [mu] ++ List.replicate 1101 0 ++ [mu]','List.replicate 3296 0 ++ List.replicate 13 padding ++ [lastPadding,0]'):assert x in highsrc
N=67*8807;assert (pow(2,N,63),pow(2,N,15),pow(2,N,7))==(32,2,4)
support=(set(range(943))|set(range(983,993))|set(range(1003,1012))|set(range(1013,1032))|{1063,1064,1095,2195,3296})-{1}
low=[2**67-(4 if j==1063 else 2 if j in support else 1) for j in range(8807)]
high=[4]+[0]*1012+[1]*10+[0]*42+[1]*9+[0]*1121+[1]+[0]*1100+[1]+[0]*1096+[2**51-2]+[0]*1101+[2**51-2]+[0]*3296+[2**65-1]*13+[2**19-1,0]
assert len(low)==len(high)==8807
def evaldigits(ds,radix,m):
 r=0
 for x in reversed(ds):r=(radix*r+x)%m
 return r
rho=pow(2,67,3);mc=evaldigits(low,rho,3);h=evaldigits(high,rho,3);q=pow(2,N,3);beta=(q-1)%3;mf=(beta+h)%3
assert (q,mc,h,mf,(mc+q*mf)%3)==(2,1,0,1,0)
# Both factors of q²−1 are odd and coprime; fixed residues imply gcd 1 and 3 respectively.
assert gcd(31,63)==1 and gcd(3,15)==3
q=pow(2,N,7);Y=q**3%7;a=Y*(q+1)%7;Delta=((a+2)**2-1)%7;c=(4*Delta+3)%7;v=3*c*c%7;L=(1+Delta*v*v)%7
assert (q,Y,a,Delta,c,v,L)==(4,1,5,6,6,3,6) and L not in {x*x%7 for x in range(7)}
g=json.loads(Path('research/ordinary13-eta-zeta84-free-square-obstruction/candidate.json').read_text());rows={n:(op,a,b) for n,op,a,b in g['source']}
for n,row in {'kbase':('+','n_eta','n_zeta'),'c':('+','n_eta','kY'),
'f2':('+','n_t',1),'Q':('*','Delta','n_t'),'I':('*','c2','i'),
'g72':('-','g71','Q'),'V':('-','g76','c'),'Fa':('-','y2','g82')}.items():assert rows[n]==row
# Construct two separate small controls with exact all-row evaluation.
controls=[]
for q in (32,662):
 beta=q-1;Y=q**3;a=Y*(q+1);Delta=(a+2)**2-1;c=4*Delta+3;C=q*q-1;MC=4;MF=4
 assert gcd(C,c)==3 and (MC+q*MF)%3==0
 base=beta*beta*C+MC+q*MF;m=c//3
 alpha=1+((((3-base)//3)*pow(C//3,-1,m)-1)%m)
 R=(alpha+beta*beta)*C+MC+q*MF;assert R>=3 and R%c==3
 k,eta=divmod(c,Y);zeta=k-eta
 assert k>=Y>eta and zeta>=0
 v=3*c*c;t=Delta*v*v;L=t+1;i=3*Delta;I=i*c*c;T=1+(R-3)//c;y=4*I*I-1
 assert i>=1 and T>=1
 vals=[1,0,alpha-1,t,i-1,T-1,1,0,0,eta,zeta,y,0];ports=[beta,0,MC,MF]
 d=dict(zip(g['witnesses'],vals));d.update(zip(g['fixed_numerals'],ports))
 for n,op,x,y0 in g['source']:
  x=d[x] if isinstance(x,str) else x;y0=d[y0] if isinstance(y0,str) else y0
  d[n]={'+':lambda:x+y0,'-':lambda:x-y0,'*':lambda:x*y0}[op]()
 assert d['c']==c and d['R']==R and d['g72']==0 and d['Fa']==1 and d['V']==4*I*I-3 and L%7==6
 controls.append({'q':q,'strong_residual':d['g72'],'aux_factor':d['Fa'],'L_mod7':L%7})
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'author_receipt_reproduced':True,'independent_digit_Horner_mod3':True,
 'compact_gcd_and_mod7_checks':True,'full_row_partial_controls':controls,
 'full_compact_graph_zero_claim':False,'lean_executed':False},sort_keys=True,indent=2))
