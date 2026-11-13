from pathlib import Path
from hashlib import sha256
import json,math,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-squarefree-even-compact-residue-constraints')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
beta=Path('Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean').read_text();assert 'def betaNat : ℕ := 2^(67*8807)-1' in beta
n=67*8807;assert n==590069 and (pow(2,n,5),pow(2,n,9),pow(2,n,25))==(2,5,12)
graph=json.loads(Path('research/ordinary9-shifted-free-aux-two-norm64/candidate.json').read_text());r={row[0]:row[1:] for row in graph['source']}
expected={'q':['+',1,'qm'],'X':['*','q','n_w'],'q2':['*','q','q'],'q3':['*','q','q2'],'s':['+','n_s',1],'Y':['*','q3','s'],'U':['*','Y','q2'],'kbase':['+','n_eta','n_zeta'],'k':['+','kbase',1],'kY':['*','Y','k'],'c':['+','n_eta','kY'],'E':['*','X','Y'],'a':['+','E','Y'],'g15':['*',4,'a'],'H':['+',3,'g15'],'g17':['*','a','a'],'Delta':['+','H','g17'],'r0':['-','kbase','R'],'shift':['-','g54','r0'],'Dstar':['+','g58','g59'],'A0':['-','g38','g42'],'A1':['-','g61','g65']}
for x,y in expected.items():assert r[x]==y,x
# Independently enumerate main-root signed Pell phase when 5 | H.
cases=[]
for w in range(5):
 for s in range(5):
  X=(2*w)%5;a=(3*s*(X+1))%5
  if (4*a+3)%5:continue
  allowed=[]
  for m in range(4):
   x,c=1,0
   for _ in range(m):x,c=((a+2)*x+(a*a+4*a+3)*c)%5,(x+(a+2)*c)%5
   for sign in (1,-1):
    if (sign*x-a*c-X)%5==0:allowed.append([m,sign])
  cases.append([w,s,allowed])
assert cases==[[0,1,[]],[1,2,[[1,1],[1,-1]]],[3,3,[[0,1],[2,-1]]],[4,4,[[3,1],[3,-1]]]]
# Derived squarefree necessary conditions, for every residue in the two moduli.
for w in range(9):
 for s in range(9):
  a=(8*s*(5*w+1))%9;u=s*(5*w+1)%9
  assert (((a+1)*(a+3))%9==0)==(u in (1,3))
  assert (((a+1)*(a+3))%3!=0)==(a%3==1)
for w in range(25):
 for s in range(25):
  a=(3*s*(12*w+1))%25;v=s*(12*w+1)%25
  assert (((a+1)*(a+3))%25==0)==(v in (8,24))
# Main Pell matrix Q modulo 8: Q^4=I; its ordinate residues are 0,1,4,7.
def mm(a,b):return tuple(sum(a[2*i+k]*b[2*k+j] for k in range(2))%8 for i in range(2) for j in range(2))
Q=(2,3,1,2);v=(1,0,0,1);ordinates=[]
for m in range(4):ordinates.append(v[2]);v=mm(v,Q)
assert v==(1,0,0,1) and ordinates==[0,1,4,7]
for m in range(0,80,2):assert ordinates[m%4]==2*m%8
# A residue assignment obeys all reported local conditions, without being a graph zero.
w,s,m,eta,zeta=3,8,4,0,1
u=s*(5*w+1)%9;v=s*(12*w+1)%25
assert (w%5,s%5)==(3,3) and u not in (1,3) and v not in (8,24)
assert u%3==2 and eta%8==2*m%8 and zeta%2==1 and m%2==0
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),'q_residues':{'5':2,'9':5,'25':12},'main_root_mod5_cases':cases,'even_ordinate_mod8':True,'squarefree_p3_and_p5_residue_conditions_checked':True,'local_residue_only_assignment':{'w':w,'s':s,'m':m,'eta':eta,'n_zeta':zeta},'full_zero_or_squarefree_compact_witness_constructed':False,'lean_executed':False},sort_keys=True,indent=2))
