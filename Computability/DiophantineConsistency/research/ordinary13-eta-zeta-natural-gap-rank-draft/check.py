from pathlib import Path
from hashlib import sha256
import json,sys,itertools
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-eta-zeta-natural-gap-rank-draft')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
src=(D/'EtaZetaNaturalGapRank.lean.src').read_text()
assert src.count('(hk1 : 1≤k v)')==3
assert 'have hk1 : 1≤k v := by dsimp [k]; simp' not in src
for n in ['theorem first_norm','theorem gap_of_J','theorem gap ','theorem rank_representation','theorem compact_rank_window','gap p v hz hbeta hk1']:
 assert n in src,n
cases=0
for q,X,Y,F,A,K,k,r in itertools.product(range(2,7),range(4),range(1,5),range(1,6),range(1,6),range(4),range(1,5),range(4)):
 C=q-F-A
 if C>0:continue
 Bt=C*(X+K)-F;b=q-1;m=X*Y*Y;ell=m*k
 z=b*(ell+k+r-k*Bt)-Bt
 assert Bt<0 and z>b*(ell+k)>=0
 assert (ell+k)**2>=1+m*(m+1)*k*k
 assert z*z>b*b*(1+m*(m+1)*k*k)
 cases+=1
assert cases>0
print(json.dumps({'first_norm_gap_controls':cases,'k_positive_explicit':True,'zero_k_not_covered':True,'lean_executed':False},sort_keys=True,indent=2))
