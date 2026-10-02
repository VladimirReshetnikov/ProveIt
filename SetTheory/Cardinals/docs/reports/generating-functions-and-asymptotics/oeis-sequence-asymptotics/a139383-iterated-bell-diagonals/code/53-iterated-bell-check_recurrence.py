"""Exact counts, official OEIS data, and an independent EGF check."""
import math,json,argparse
from pathlib import Path
from fractions import Fraction as F
p=argparse.ArgumentParser();p.add_argument('--max',type=int,default=260);p.add_argument('--out',default='recurrence.json');a=p.parse_args()
N=a.max
if N<20:raise SystemExit('Use max >=20 for the complete official-data check.')
S=[[1]]
for n in range(1,N+1):
 old=S[-1];S.append([0]+[(old[k-1] if k-1<len(old) else 0)+(k*old[k] if k<len(old) else 0) for k in range(1,n+1)])
v=[0]*(N+1);v[1]=1;A={0:1};B={0:1};small={0:v[:9]}
for m in range(1,N+2):
 v=[0]+[sum(S[n][k]*v[k] for k in range(1,n+1)) for n in range(1,N+1)]
 if m<=8:small[m]=v[:9]
 if m<=N:A[m]=v[m]
 if 1<=m-1<=N:B[m-1]=v[m-1]
# EGF exponentiation, independent of the Stirling recurrence.
g=[F(0),F(1)]+[F(0)]*7
for m in range(9):
 assert all(g[n]*math.factorial(n)==small[m][n] for n in range(1,9))
 E=[F(1)]+[F(0)]*8
 for n in range(1,9):E[n]=sum(k*g[k]*E[n-k] for k in range(1,n+1))/n
 g=[F(0)]+E[1:]
base=Path(__file__).resolve().parents[1]
matched={}
for id,seq in [('A139383',A),('A261280',B)]:
 terms=[]
 for line in (base/'source'/f'{id}.seq').read_text().splitlines():
  if line.startswith(('%S ','%T ','%U ')):terms.extend(int(z) for z in line.split(' ',2)[2].strip(',').split(','))
 assert all(seq[n]==v for n,v in enumerate(terms))
 matched[id]=len(terms)
rows=[]
for n in [10,20,40,80,120,160,200,260]:
 if n>N:continue
 core=(2*n-5/6)*math.log(n)-(n-1)*math.log(2)-n
 rows.append(dict(n=n,A_amplitude=math.exp(math.log(A[n])-core),B_amplitude=math.exp(math.log(B[n])-core),B_over_A=B[n]/A[n]))
out={'max_n':N,'official_terms_matched':matched,'independent_egf_checks':72,'assertions_passed':True,'floating_amplitudes_are_uncertified':True,'diagnostics':rows}
Path(a.out).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
