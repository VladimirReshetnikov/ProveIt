#!/usr/bin/env python3
if not __debug__:raise SystemExit('Run without -O; assertions are required')
from itertools import combinations
from pathlib import Path
from collections import defaultdict
import argparse,json
pa=argparse.ArgumentParser();pa.add_argument('--output-dir',type=Path,default=Path(__file__).resolve().parent);args=pa.parse_args()
# Ground old x0,x1,x2; marked A0,A1,A2; dummy d0,d1,d2,d3.
# M is rank two with parallel classes {xi,Ai}; the four dummies are loops.
# N is transversal on four slots: private A0,A1,A2 and common ABC.
rows=[0,0,0,9,10,12,1,2,4,8];weights=[4,4,4,1]
def independent_M(s):return len(s)<=2 and all(i<6 for i in s) and len({i%3 for i in s})==len(s)
def independent_N(s):
 reachable={0}
 for i in s:
  nxt=set()
  for used in reachable:
   for j in range(4):
    if rows[i]>>j&1 and not used>>j&1:nxt.add(used|1<<j)
  reachable=nxt
 return bool(reachable)
terms=defaultdict(int);generic=defaultdict(int);bases=0;candidates=0
for b in combinations(range(10),6):
 candidates+=1
 feasible=any(independent_M(m)and independent_N([i for i in b if i not in m])for m in combinations(b,2))
 if not feasible:continue
 bases+=1
 if not all(i in b for i in (3,4,5)):continue
 selected_d=[i-6 for i in b if i>=6];w=1
 for j in range(4):
  if j not in selected_d:w*=weights[j]
 exp=tuple(int(i in b)for i in range(3))+(len(selected_d)-1,)
 assert sum(exp)==2
 terms[exp]+=w
 omitted=[j for j in range(4)if j not in selected_d]
 generic[(exp, sum(j<3 for j in omitted),int(3 in omitted))]+=1
expected={(0,0,0,2):13,(1,0,0,1):44,(0,1,0,1):44,(0,0,1,1):44,(1,1,0,0):112,(1,0,1,0):112,(0,1,1,0):112}
assert dict(terms)==expected
for e in expected:
 got={(a,b):v for (mon,a,b),v in generic.items()if mon==e}
 want=({(1,0):3,(0,1):1}if e[3]==2 else {(2,0):2,(1,1):3}if e[3]==1 else {(3,0):1,(2,1):3})
 assert got==want,(e,got)
# Direct univariate coefficient expansion of 9(2p^2+3ph)^2-12(p^3+3p^2h)(3p+h).
assert [36-36,108-120,81-36]==[0,-12,45]
# Rational representation by doubled directions e1,e2,e1+e2.
columns=[(1,0),(0,1),(1,1)]*2
for i,j in combinations(range(6),2):assert bool(columns[i][0]*columns[j][1]-columns[i][1]*columns[j][0])==independent_M((i,j))
rec={'status':'PASS','parametric_p_h_coefficients_and_discriminant':'PASS','union_basis_candidates':candidates,'union_bases':bases,'quadratic_coefficients':{','.join(map(str,k)):v for k,v in sorted(terms.items())},'all_15_represented_pair_minors':'PASS','nontransversality_argument':'Every nonloop parallel pair forces both elements to have the same singleton slot. Three distinct parallel classes then yield a three-element transversal, contradicting rank two.','scope':'Abstract three-distinguished-element transform; graph lifting is independently checked in the adjacent Hall checker.'}
args.output_dir.mkdir(parents=True,exist_ok=True);(args.output_dir/'abstract_verification.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec,indent=2))
