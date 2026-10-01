"""A positive rank-three matrix whose regular-minor counts fail ULC3."""
from pathlib import Path
from itertools import combinations
from math import comb
import json
ns={};source=Path(__file__).with_name('check_matrix_lifts.py').read_text();exec(source[:source.index('lift_checks=0')],ns);det=ns['det']
V=[[1,i,i*i]for i in range(1,10)]
M=[[1+i*j+(i*j)**2 for j in range(1,10)]for i in range(1,10)]
assert all(M[i][j]==sum(V[i][k]*V[j][k]for k in range(3))for i in range(9)for j in range(9))
counts=[]
for k in(1,2,3):
 values=[det([[M[i][j]for j in J]for i in I])for I in combinations(range(9),k)for J in combinations(range(9),k)]
 assert min(values)>0 and len(values)==comb(9,k)**2;counts.append(len(values))
P=[1]+counts;gap=2*P[2]**2-6*P[1]*P[3]
assert P==[1,81,1296,7056]and gap==-69984
out={'status':'passed','matrix':'M_ij=1+i*j+(i*j)^2, 1<=i,j<=9','rank':3,'positive_minors_checked':sum(counts),'coefficients':P,'last_ULC3_gap':gap,'rank_upper_bound':'M=V V^T with three columns','rank_lower_bound':'all3minors positive'}
(Path(__file__).resolve().parents[1]/'data'/'rank_three_boundary_checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
