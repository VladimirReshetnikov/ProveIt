#!/usr/bin/env python3
if not __debug__:raise SystemExit('Run without -O; assertions are required')
from pathlib import Path
from math import comb
from fractions import Fraction
import argparse,json,time
pa=argparse.ArgumentParser();pa.add_argument('--output-dir',type=Path,default=Path(__file__).resolve().parent);args=pa.parse_args();start=time.monotonic()
def choose(n,k):return comb(n,k)if 0<=k<=n else 0
quota_checks=0;feasible=0
for k in range(7):
 for i in range(min(3,k)+1):
  for j in range(min(3,k)+1):
   x,y=k-i,k-j
   rows=[(1<<k)-1]*i+[(1<<j)-1]*x
   ok=True
   for sub in range(1,1<<k):
    nbr=0
    for l in range(k):
     if sub>>l&1:nbr|=rows[l]
    if nbr.bit_count()<sub.bit_count():ok=False;break
   assert ok==(i+j>=k),(i,j,x,y,ok)
   quota_checks+=1;feasible+=ok
N=40;L=10000
coeff=[sum(choose(3,i)*choose(3,j)*L**(i+j)*choose(N,k-i)*choose(N,k-j)for i in range(4)for j in range(4)if i+j>=k)for k in range(7)]
expected=[1,902400000,90721908000000000,1024191381360000000000000,1618798468000000000000000000,613023840000000000000000000000,97614400000000000000000000000000]
assert coeff==expected
A=choose(N,2);B=choose(N,3)
assert coeff[4]==L**6*N*N+6*L**5*N*A+L**4*(6*N*B+9*A*A)
assert coeff[5]==L**6*A*A+6*L**5*A*B
assert coeff[6]==L**6*B*B
G=5*coeff[5]**2-12*coeff[4]*coeff[6]
assert G==-172253520551424*10**44<0
# Derive the parameter identity using elementary polynomial operations, without SymPy.
def add(a,b):
 c=dict(a)
 for k,v in b.items():c[k]=c.get(k,0)+v
 return {k:v for k,v in c.items()if v}
def scale(a,c):return {k:v*c for k,v in a.items()if v*c}
def mul(a,b):
 c={}
 for i,u in a.items():
  for j,v in b.items():c[i+j]=c.get(i+j,0)+u*v
 return {k:v for k,v in c.items()if v}
n={1:Fraction(1)};n1=add(n,{0:Fraction(-1)});n2=add(n,{0:Fraction(-2)})
a=scale(mul(n,n1),Fraction(1,2));b=scale(mul(mul(n,n1),n2),Fraction(1,6));n_sq=mul(n,n)
p2=add(scale(mul(mul(a,a),mul(a,a)),5),scale(mul(n_sq,mul(b,b)),-12))
p1=scale(mul(mul(a,b),add(scale(mul(a,a),5),scale(mul(n,b),-6))),12)
p0=scale(mul(mul(b,b),add(mul(a,a),scale(mul(n,b),-1))),72)
factor=scale(mul(mul(n_sq,n_sq),mul(n1,n1)),Fraction(1,48))
assert p2==mul(factor,{2:Fraction(-1),1:Fraction(34),0:Fraction(-49)})
assert p1==scale(mul(factor,mul(mul(n1,n2),add(n,{0:Fraction(3)}))),12)
assert p0==scale(mul(factor,mul(mul(n1,mul(n2,n2)),add(n,{0:Fraction(1)}))),8)
# Leading-coefficient threshold is exactly N>=33 for integers N>=3.
assert all(((-n*n+34*n-49)<0)==(n>=33)for n in range(3,1001))
ratio=Fraction(A**4,N*N*B*B);assert ratio==Fraction(9*(N-1)**2,4*(N-2)**2)<Fraction(12,5)
# First four gaps are included to locate the failure, but are not needed to refute ULC.
gaps=[k*(6-k)*coeff[k]**2-(k+1)*(7-k)*coeff[k-1]*coeff[k+1]for k in range(1,6)]
assert gaps[-1]==G
scaled=[coeff[k]//L**k for k in range(7)]
assert all(coeff[k]==scaled[k]*L**k for k in range(7))
assert scaled==[1,90240,907219080,1024191381360,161879846800,6130238400,97614400]
variant=[sum(choose(3,i)*choose(3,j)*30000**(i+j-k)*choose(33,k-i)*choose(33,k-j)for i in range(4)for j in range(4)if i+j>=k)for k in range(7)]
assert variant==[1,270198,8117832969,27178589394544,983239909344,8380804608,29767936]
variant_gap=5*variant[5]**2-12*variant[4]*variant[6]
assert variant_gap==-38842940605759488<0
rec={'scaled_gamma':scaled,'scaled_last_gap':G//L**10,'variant_72_vertices':{'N':33,'core_activity':30000,'scaled_gamma':variant,'last_gap':variant_gap},'status':'PASS','N':N,'core_activity':L,'vertices':2*(N+3),'matching_rank':6,'quota_Hall_checks':quota_checks,'feasible_quotas':feasible,'gamma':coeff,'normalized_gap_numerators':gaps,'last_gap':G,'last_gap_compact':'-172253520551424 * 10^44','exact_parameter_gap_factorization':'PASS','asymptotic_last_ratio':str(ratio),'asymptotic_threshold':'N>=33','scope':'Weighted bipartite endpoint-support ULC counterexample at actual rank six; also a height-two preorder and single-vertex-activity counterexample','seconds':round(time.monotonic()-start,3)}
args.output_dir.mkdir(parents=True,exist_ok=True);(args.output_dir/'verification.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec,indent=2))
