from pathlib import Path
from hashlib import sha256
import json,math,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-shifted-two-norm-lift-obstructions-independent')
for f,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(f).read_bytes()).hexdigest()==h,f
Q=Path('research/ordinary13-shifted-two-norm-lift-obligation-obstructions')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(Q/'check.py')])==(Q/'receipt.json').read_bytes()
g=json.loads(Path('research/ordinary9-shifted-free-aux-two-norm64/candidate.json').read_text()); rows={x[0]:x[1:] for x in g['source']}
expect={'qm':['*','n_J','beta'],'q':['+',1,'qm'],'X':['*','q','n_w'],'q2':['*','q','q'],'q3':['*','q','q2'],'s':['+','n_s',1],'Y':['*','q3','s'],'U':['*','Y','q2'],'E':['*','X','Y'],'kbase':['+','n_eta','n_zeta'],'k':['+','kbase',1],'kY':['*','Y','k'],'c':['+','n_eta','kY'],'a':['+','E','Y'],'g15':['*',4,'a'],'H':['+',3,'g15'],'g17':['*','a','a'],'Delta':['+','H','g17'],'g19':['*','a','c'],'b0':['+','X','g19'],'ell':['*','E','kY'],'R':['+','g47','g50'],'r0':['-','kbase','R'],'g54':['*','U','n_gamma'],'shift':['-','g54','r0'],'g58':['*','U','b0'],'g59':['*','H','shift'],'Dstar':['+','g58','g59'],'g38':['*','Z','Z'],'g39':['*','qm','qm'],'g40':['*','ell','g30'],'g41':['+',1,'g40'],'g42':['*','g39','g41'],'A0':['-','g38','g42'],'g61':['*','Dstar','Dstar'],'g62':['*','U','U'],'g63':['*','Delta','c2'],'g64':['+',1,'g63'],'g65':['*','g62','g64'],'A1':['-','g61','g65']}
for k,v in expect.items():assert rows[k]==v,(k,rows[k])
assert rows['g30']==['+','ell','k'] and rows['c2']==['*','c','c']
fixed=Path('Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean').read_text();assert 'def betaNat : ℕ := 2^(67*8807)-1' in fixed
N=67*8807;assert N%4==1 and pow(2,N,5)==2
# Direct modular Pell-pair recurrence: both signed branches independently.
for m in range(80):
 x,c=1,0
 for _ in range(m):x,c=(4*c)%5,x%5 # a=3, A=a+2=0, Delta=4 (mod 5)
 assert (x-3*c)%5==pow(2,m,5)
 assert ((x-3*c)*(x+3*c))%5==1
 for sign in (1,-1):
  if (sign*x-3*c)%5==2:assert m%4==1,(m,sign,x,c)
for m in range(4):
 if m!=1:
  assert pow(2,m,5)!=2 and (-pow(pow(2,m,5),-1,5))%5!=2
# Independently check the GCD simplification on a bounded grid; general proof is in README.
count=0
for e in range(1,7):
 q=2**e
 for w in range(16):
  for s in range(1,17):
   Y=q**3*s;H=4*Y*(q*w+1)+3;U=q**5*s
   assert math.gcd(H,U)==math.gcd(s,3) and math.gcd(H,q)==1 and H//math.gcd(s,3)>1
   count+=1
# The first Pell recurrence and main parity in bounded controls.
for M in range(1,31):
 x,k=1,0
 for n in range(12):
  assert k%2==0 and x*x-M*(M+1)*k*k==1
  x,k=(2*M+1)*x+2*M*(M+1)*k,2*x+(2*M+1)*k
for A in range(2,22,2):
 x,c=1,0
 for m in range(30):
  assert c%2==m%2
  x,c=A*x+(A*A-1)*c,x+A*c
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),'author_receipt_reproduced':True,'literal_rows':len(expect)+2,'q_mod_5':2,'both_signs_force_index_mod_4':1,'gcd_grid_controls':count,'scope':'conditional standard-integer consequences of actual two-norm graph; no full zero or universal lift claim','lean_executed':False},sort_keys=True,indent=2))
