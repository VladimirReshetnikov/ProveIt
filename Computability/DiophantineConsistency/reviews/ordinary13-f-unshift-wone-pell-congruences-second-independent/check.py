from pathlib import Path
from hashlib import sha256
from math import gcd
import itertools,json,sys,subprocess
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-f-unshift-wone-pell-congruences-second-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
p=Path('research/ordinary13-f-unshift-fixed-wone-pell-congruences')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
g=json.loads(Path('research/ordinary13-eta85-shift-boundary-probes/F-probe.json').read_text());r={n:(op,a,b) for n,op,a,b in g['source']}
for n,row in {'qm':('*','n_J','beta'),'q':('+',1,'qm'),'X':('*','q','n_w'),
 'Y':('*','q3','s'),'U':('*','Y','q2'),'G':('+','alpha','g44'),
 'R':('+','g47','g50'),'r0':('-','kbase','R'),'shift':('-','g54','r0'),
 'Dstar':('+','g58','g59'),'A1':('-','g61','g65'),'g72':('-','g71','Q'),
 'Fa':('-','y2','g82')}.items():assert r[n]==row
assert 'range 943 ∪ Ico 983 993' in Path('Lean/DiophantineConsistency/Compact44/CompactConcreteMask.lean').read_text()
assert 'if j=special then B-4 else if j∈S then B-2 else B-1' in Path('Lean/DiophantineConsistency/Compact44/CompactListMask.lean').read_text()
assert 0 in (set(range(943))-{1}) and 0!=1063
N=67*8807;rho=2**67;assert N==590069 and N%2==1 and (rho-2)%rho==rho-2
assert ((rho-2)//2)%(2**66)==2**66-1
# GCD and both sign formulas, using a second exact recurrence simulation.
controls=0;sign_hits=[0,0]
for q in (2,4,8,16,32):
 for s in range(1,10):
  Y=q**3*s;a=Y*(q+1);H=4*a+3;U=q**5*s;d=gcd(s,3);L=H//d
  assert H%2==1 and gcd(H,U)==d
  A=a+2;Delta=A*A-1;x,y=1,0
  for m in range(32):
   assert x*x-Delta*y*y==1
   assert (x-a*y)%H==pow(2,m,H)
   assert ((x-a*y)*(x+a*y))%H==1%H
   assert y%2==m%2
   pos=(x-a*y-q)%L==0;neg=(-x-a*y-q)%L==0
   assert pos==((pow(2,m,L)-q)%L==0)
   assert neg==((-pow(pow(2,m,L),-1,L)-q)%L==0)
   if q%3==2 and s%3:
    if pos:assert m%2==1;sign_hits[0]+=1
    if neg:assert m%2==0;sign_hits[1]+=1
   x,y=A*x+Delta*y,x+A*y;controls+=1
# Negative branch: c even => I multiple 4. Check unit equations mod 8/4.
for f,I in itertools.product(range(8),repeat=2):
 if I%4==0 and (I*I-3*(f*f-1))%8==0:assert f%2==1
for y,V,I in itertools.product(range(4),repeat=3):
 if I%2==0 and (y*y-I*I*(y*y-V*V)-1)%4==0:assert y%2==1
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'author_receipt_reproduced':True,'literal_root_rank_rows_checked':True,
 'fixed_low_digit_index_congruence':True,'gcd_and_signed_Pell_controls':controls,
 'positive_negative_sign_hits':sign_hits,'negative_branch_modular_parities':True,
 'scope':'Fixed compact ports, full zero, J=1, F=0, C>0, w=1; parity conclusions additionally need 3 not dividing s.',
 'lean_executed':False},sort_keys=True,indent=2))
