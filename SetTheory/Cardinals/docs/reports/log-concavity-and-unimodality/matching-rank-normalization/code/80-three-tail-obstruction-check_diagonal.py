#!/usr/bin/env python3
if not __debug__:raise SystemExit('Run without -O; assertions are required')
from itertools import combinations
from fractions import Fraction
from math import comb
from pathlib import Path
import argparse,json,time
p=argparse.ArgumentParser();p.add_argument('--output-dir',type=Path,default=Path(__file__).resolve().parent);args=p.parse_args();start=time.monotonic()
rows=[73,82,100,7,1,2];tail=[100,100,100,100,1,1];head=[1,1,1,8,8,8,1]
gamma=[0]*7;poly={};generic={};candidate=0;feasible=0
for tm in range(64):
 k=tm.bit_count()
 for hs in combinations(range(7),k):
  hm=sum(1<<j for j in hs);candidate+=1;sub=tm;ok=True
  while sub:
   nbr=0
   for i in range(6):
    if sub>>i&1:nbr|=rows[i]
   if (nbr&hm).bit_count()<sub.bit_count():ok=False;break
   sub=(sub-1)&tm
  if not ok:continue
  feasible+=1;w=1
  for i in range(6):
   if tm>>i&1:w*=tail[i]
  for j in hs:w*=head[j]
  q_unused=3-sum(j<3 for j in hs);y_used=sum(j>=3 for j in hs)
  monomial=(k,q_unused,3-y_used);assert sum(monomial)==6
  poly[monomial]=poly.get(monomial,0)+w;gamma[k]+=w
  if k==4:
   key=(q_unused,3-y_used,(tm&15).bit_count()-2,sum(3<=j<6 for j in hs))
   generic[key]=generic.get(key,0)+1
coefficient={e[1:]:v for e,v in poly.items()if e[0]==4}
expected={(2,0):21260800*10000,(1,1):4688240*10000,(0,2):258845*10000}
assert coefficient==expected,coefficient
generic_expected={(2,0,2,3):3,(2,0,2,2):9,(2,0,1,3):2,(2,0,1,2):6,(1,1,2,2):6,(1,1,2,1):9,(1,1,1,2):16,(1,1,1,1):32,(1,1,0,2):3,(1,1,0,1):6,(0,2,2,1):3,(0,2,2,0):1,(0,2,1,1):10,(0,2,1,0):8,(0,2,0,1):5,(0,2,0,0):5}
assert generic==generic_expected,generic
assert gamma==[1,3302,3846201,1806662900,262078850000,313024000000,70400000000],gamma
A,B,C=21260800,4688240,258845;disc=B*B-4*A*C;assert disc==-33412806400
assert A>0 and C>0 and disc<0
ulc=[Fraction(gamma[k]**2)-Fraction(comb(6,k)**2,comb(6,k-1)*comb(6,k+1))*gamma[k-1]*gamma[k+1]for k in range(1,6)];assert all(x>0 for x in ulc)
rec={'status':'PASS','parametric_L_p_t4_identity':'PASS','left_rows':rows,'tail_activities':tail,'head_activities':head,'endpoint_candidates':candidate,'feasible_endpoint_pairs':feasible,'gamma':gamma,'homogeneous_terms':{','.join(map(str,k)):v for k,v in sorted(poly.items())},'t4_coefficient_divided_by_10000':[A,B,C],'quadratic_discriminant':disc,'quadratic_hessian_positive_definite':True,'strict_scalar_rank_six_ULC_gaps':[str(g)for g in ulc],'scope':'Failure of diagonal cover-order Lorentzianity; scalar rank-six ULC holds strictly in this example','seconds':round(time.monotonic()-start,3)}
args.output_dir.mkdir(parents=True,exist_ok=True);(args.output_dir/'diagonal_verification.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec,indent=2))
