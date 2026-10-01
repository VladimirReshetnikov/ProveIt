#!/usr/bin/env python3
from itertools import combinations
from collections import Counter
from pathlib import Path
import json
cols=[9,9,9,1,10,10,2,12,12,4,8,15]
counts=Counter();checks=0
for J in combinations(range(12),4):
 S={0}
 for j in J:S={m|(1<<i) for m in S for i in range(4) if cols[j]>>i&1 and not m>>i&1}
 dp=15 in S
 hall=True
 for mask in range(1,16):
  union=0
  for i,j in enumerate(J):
   if mask>>i&1:union|=cols[j]
  if union.bit_count()<mask.bit_count():hall=False;break
 if dp!=hall:raise RuntimeError('basis test disagrees')
 checks+=1
 if dp:counts[(10 in J,11 in J)]+=1
L=sum(counts.values());Le=counts[True,False]+counts[True,True];Lf=counts[False,True]+counts[True,True];Lef=counts[True,True]
out=dict(source='Choe-Wagner, Rayleigh Matroids, Proposition 5.9, arXiv:math/0307096',presentation_masks=cols,independent_four_subset_tests=checks,neither=counts[False,False],e_only=counts[True,False],f_only=counts[False,True],both=Lef,total_bases=L,derivative_e=Le,derivative_f=Lf,rayleigh_difference=Le*Lf-L*Lef,printed_counts_reproduced=False,scope='The printed presentation gives a valid negative Rayleigh difference with corrected counts; this is not a shifted ULC counterexample')
if (L,Le,Lf,Lef)!=(309,69,147,33):raise RuntimeError('unexpected counts')
(Path(__file__).resolve().parents[1] / 'data' / 'rayleigh_seed_checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
