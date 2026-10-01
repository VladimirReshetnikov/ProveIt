"""Exact finite-grid regression of the continuous proof's residue symmetries.
The proof is continuous; these rational checks test the maps and accounting.
"""
from fractions import Fraction as F
from itertools import product,combinations
from collections import defaultdict
from pathlib import Path
import json

# ed. (2026-10-01): results are written to <output-dir>/<name>, by default
# rerun/ beside this program, with LF line endings (as delivered the program
# overwrote its recorded result beside itself, with CRLF on Windows). Pass
# --output-dir with this program's own directory, on a copy, to regenerate
# the recorded file.
def _ed_write(name, text):
    import argparse
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument('--output-dir', type=Path,
                        default=Path(__file__).resolve().parent / 'rerun')
    out = parser.parse_known_args()[0].output_dir
    out.mkdir(parents=True, exist_ok=True)
    (out / name).write_bytes(text.encode('utf-8'))
caps=(8,4,2,1); grid=F(1,2); counts=tuple(int(F(a)/grid)for a in caps)
states=list(product(*(range(n)for n in counts)))
maxdegree=sum(n-1 for n in counts)
S=lambda x:grid*(sum(x)+F(len(x),2))
q={x:F(2**(maxdegree-sum(x)))for x in states}
mu=sum(q[x]*S(x)for x in states)/sum(q.values())
models={
 'reference':q,
 'quadratic_weight':{x:q[x]*(1+S(x)**2)for x in states},
 'threshold_reweight':{x:q[x]*(S(x)<=mu)for x in states},
 'original_uniform_conditioned':{x:F(S(x)<=mu)for x in states},
 'periodic_weight':{x:q[x]*(1+(S(x)%1))for x in states},
}

def norm(weights):
 z=sum(weights.values());assert z>0
 return{x:v/z for x,v in weights.items()if v}
models={k:norm(v)for k,v in models.items()}
def marginal(P,mask,targets=None):
 D=defaultdict(F)
 for x,p in P.items():
  obs=tuple(x[i]if targets is None else x[i]%counts[j]for i,j in zip(mask, mask if targets is None else targets))
  D[obs]+=p
 return dict(D)
def tv(P,Q):return sum(abs(P.get(x,0)-Q.get(x,0))for x in set(P)|set(Q))/2
def chi(P,Q):return sum((P.get(x,0)-v)**2/v for x,v in Q.items())
# Pointwise involution, cap bounds and preservation of both S and reference weight.
pointwise=0
for i,j in combinations(range(4),2):
 assert counts[i]%counts[j]==0
 for x in states:
  k,r=divmod(x[i],counts[j]);y=list(x);y[i]=k*counts[j]+x[j];y[j]=r;y=tuple(y)
  assert all(0<=v<n for v,n in zip(y,counts))
  k2,r2=divmod(y[i],counts[j]);z=list(y);z[i]=k2*counts[j]+y[j];z[j]=r2
  assert tuple(z)==x and S(y)==S(x) and q[y]==q[x]
  pointwise+=1
pairs=[]
for k in range(1,5):
 for E in combinations(range(4),k):
  for L in combinations(range(4),k):
   if all(i<=j for i,j in zip(E,L)):pairs.append((E,L))
comparisons=0;strict_tv=0;periodic_equalities=0
for name,P in models.items():
 for E,L in pairs:
  PE=marginal(P,E);PL=marginal(P,L);QE=marginal(models['reference'],E);QL=marginal(models['reference'],L)
  assert marginal(P,E,L)==PL,(name,E,L)
  assert marginal(models['reference'],E,L)==QL
  assert tv(PL,QL)<=tv(PE,QE)
  assert chi(PL,QL)<=chi(PE,QE)
  strict_tv+=tv(PL,QL)<tv(PE,QE)
  if name=='periodic_weight':
   assert tv(PL,QL)==tv(PE,QE) and chi(PL,QL)==chi(PE,QE)
   periodic_equalities+=1
  comparisons+=1
# Condition on each discrete total; same map works at every supported total.
conditioned=0
for total in sorted({S(x)for x in states}):
 P=norm({x:v for x,v in q.items()if S(x)==total})
 for E,L in pairs:
  assert marginal(P,E,L)==marginal(P,L),(total,E,L)
  conditioned+=1
# Retain all other coordinates through each elementary swap.
common=0
for i,j in combinations(range(4),2):
 C=tuple(k for k in range(4)if k not in(i,j))
 for P in models.values():
  assert marginal(P,C+(i,),C+(j,))==marginal(P,C+(j,))
  common+=1
result={'status':'passed','scope':'exact finite-grid regression, not a replacement for the continuous proof','caps':caps,'grid':str(grid),'states':len(states),'pointwise_involution_checks':pointwise,'ordered_mask_pairs':len(pairs),'joint_pushforward_divergence_checks':comparisons,'strict_tv_comparisons_observed':strict_tv,'periodic_equality_checks':periodic_equalities,'supported_exact_total_mask_checks':conditioned,'common_observation_checks':common,'tilted_mean':str(mu)}
# ed. (2026-10-01): written by _ed_write (see above).
_ed_write('verification.json', json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
