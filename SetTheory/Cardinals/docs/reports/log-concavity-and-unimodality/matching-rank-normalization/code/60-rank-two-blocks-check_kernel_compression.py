"""Independent exact checks of Hall-slack-two kernel compression, including omitted and parallel lines."""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations
from math import prod,lcm
import random,json,sympy as s
# Import only independent determinant/regular-minor utilities, without running their checks.
ns={};source=Path(__file__).with_name('check_matrix_lifts.py').read_text();exec(source[:source.index('lift_checks=0')],ns)
det,regular,trim=ns['det'],ns['regular'],ns['trim']
rng=random.Random(821371)
def check(Gamma):
 N=len(Gamma);h=len(Gamma[0]);outside=rng.randrange(3);c=2+rng.randrange(3)
 A=s.Matrix(Gamma);assert A.rank()==h
 rows=[[rng.randrange(-3,4)for _ in range(c)]for _ in range(N+outside)]
 M=[Gamma[i]+rows[i]if i<N else [0]*h+rows[i]for i in range(N+outside)]
 u=[F(rng.randrange(1,6))for _ in range(N+outside)];v=[F(rng.randrange(1,6))for _ in range(h+c)]
 Eh=sum(prod(u[i]for i in I)for I in combinations(range(N),h)if det([Gamma[i]for i in I]))
 K=A.T.nullspace();assert len(K)==2
 vectors=[];activity=[];indices=[];omitted=[]
 for i in range(N):
  if K[0][i]==K[1][i]==0:omitted.append(i);continue
  z=K[1][i]*K[0]-K[0][i]*K[1]
  assert z[i]==0 and A.T*z==s.zeros(h,1)
  row=[sum(z[j]*rows[j][k]for j in range(N))for k in range(c)]
  scale=lcm(*(int(x.q)for x in row))
  vectors.append([int(x*scale)for x in row]);activity.append(prod(u[j]for j in range(N)if j!=i)/Eh);indices.append(i)
 Q=F(0);parallel=0
 for a,b in combinations(range(len(indices)),2):
  i,j=indices[a],indices[b]
  independent=K[0][i]*K[1][j]!=K[1][i]*K[0][j]
  comp=[k for k in range(N)if k not in(i,j)]
  assert bool(independent)==bool(det([Gamma[k]for k in comp]))
  if independent:Q+=activity[a]*activity[b]
  else:parallel+=1
 assert Q==prod(u[:N])/Eh
 H=regular(rows[N:]+vectors,u[N:]+activity,v[h:])
 P=regular(M,u,v,tuple(range(h)));rhs=[F(0)]*h+[prod(v[:h])*Eh*x for x in H]
 assert trim(P)==trim(rhs),(Gamma,P,rhs)
 return len(omitted),parallel
checks=[]
# Explicit coloop and parallel-kernel-line cases, all rows nonzero.
for G in [[[1,0],[0,1],[0,1],[0,1]],[[1,0],[1,0],[0,1],[0,1]]]:checks.append(check(G))
for h in range(1,5):
 for trial in range(12):
  while True:
   G=[[rng.randrange(-2,3)for _ in range(h)]for _ in range(h+2)]
   if all(any(row)for row in G)and s.Matrix(G).rank()==h:break
  checks.append(check(G))
out={'full_polynomial_kernel_checks':len(checks),'forced_set_sizes':[1,2,3,4],'cases_with_omitted_kernel_line':sum(a>0 for a,b in checks),'cases_with_parallel_kernel_lines':sum(b>0 for a,b in checks),'all_dual_minor_tests_passed':True,'all_pair_weight_identities_passed':True,'all_conditioned_polynomials_matched':True,'all_checks_passed':True}
(Path(__file__).resolve().parents[1]/'data'/'kernel_compression_checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
