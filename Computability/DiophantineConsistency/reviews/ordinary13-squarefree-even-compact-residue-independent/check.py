from pathlib import Path
from hashlib import sha256
import json,math,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-squarefree-even-compact-residue-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
beta=Path('Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean').read_text();assert 'def betaNat : ℕ := 2^(67*8807)-1' in beta
N=67*8807;assert N==590069 and [pow(2,N,p) for p in (5,9,25)]==[2,5,12]
g=json.loads(Path('research/ordinary9-shifted-free-aux-two-norm64/candidate.json').read_text());rows={x[0]:x[1:] for x in g['source']}
for x,r in {'q':['+',1,'qm'],'X':['*','q','n_w'],'s':['+','n_s',1],
 'q2':['*','q','q'],'q3':['*','q','q2'],'Y':['*','q3','s'],'U':['*','Y','q2'],
 'E':['*','X','Y'],'a':['+','E','Y'],'g15':['*',4,'a'],'H':['+',3,'g15'],
 'g17':['*','a','a'],'Delta':['+','H','g17'],'kbase':['+','n_eta','n_zeta'],
 'k':['+','kbase',1],'kY':['*','Y','k'],'c':['+','n_eta','kY'],
 'r0':['-','kbase','R'],'g54':['*','U','n_gamma'],'shift':['-','g54','r0'],
 'g58':['*','U','b0'],'g59':['*','H','shift'],'Dstar':['+','g58','g59'],
 'g61':['*','Dstar','Dstar'],'g62':['*','U','U'],'g63':['*','Delta','c2'],
 'g64':['+',1,'g63'],'g65':['*','g62','g64'],'A1':['-','g61','g65']}.items():assert rows[x]==r,(x,rows[x])
# Independently derive mod-5 rows from 2^m and -2^(-m), not Pell iteration.
cases=[]
for w in range(5):
 for s in range(5):
  X=2*w%5;a=3*s*(X+1)%5
  if (4*a+3)%5:continue
  assert a==3
  signs=[(m,sign) for m in range(4) for sign in (1,-1)
         if ((pow(2,m,5) if sign==1 else -pow(pow(2,m,5),-1,5))-X)%5==0]
  cases.append((w,s,signs))
assert cases==[(0,1,[]),(1,2,[(1,1),(1,-1)]),(3,3,[(0,1),(2,-1)]),(4,4,[(3,1),(3,-1)])]
# Derive complete recurrence period modulo 8 and the even-index restriction.
x,y=1,0; seq=[]
for j in range(8):
 seq.append((x,y));x,y=(2*x+3*y)%8,(x+2*y)%8
assert seq[:4]==[(1,0),(2,1),(7,4),(2,7)] and seq[4:]==seq[:4]
for j in range(0,8,2):assert seq[j][1]==(2*j)%8
# Independent check of individual factors, allowing either to carry p².
for modulus,q in ((9,5),(25,12)):
 for w in range(modulus):
  for s in range(modulus):
   a=pow(q,3,modulus)*s*(q*w+1)%modulus
   first=(a+1)%modulus==0;second=(a+3)%modulus==0
   inner=s*(q*w+1)%modulus
   assert (first or second)==(inner in ((1,3) if modulus==9 else (8,24)))
   assert not(first and second)
for a in range(3):assert (((a+1)*(a+3))%3!=0)==(a==1)
# Literal local assignment satisfies every necessary residue, without asserting any norm.
w,s,m,eta,nz=3,8,4,0,1
assert (w%5,s%5)==(3,3) and (s*(5*w+1))%9 not in (1,3)
assert (s*(12*w+1))%25 not in (8,24) and eta%8==(2*m)%8 and nz%2==1
assert math.gcd(m,((pow(2,N,16)**3*s*(pow(2,N,16)*w+1)+1)*(pow(2,N,16)**3*s*(pow(2,N,16)*w+1)+3)))==1
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'signed_mod5_phases_independently_enumerated':True,'mod8_period_and_coordinate_checked':True,
 'prime_square_residue_classes_checked':True,'graph_operand_rows_checked':True,
 'local_assignment_only':True,'full_zero_or_squarefreeness_proved':False,'lean_executed':False},indent=2,sort_keys=True))
