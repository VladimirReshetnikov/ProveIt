"""Exact BB R determinant identities by a degree-unisolvent integer simplex.

A d-variable polynomial of total degree <=D is determined by the integer
points x>=0, sum(x)<=D (the multivariate falling-factorial basis proves this).
The matrix entries have total degree <=2, so D=2*matrix_dimension suffices.
"""
from pathlib import Path
from itertools import permutations,combinations_with_replacement
from functools import lru_cache
from math import comb
import sympy as s
import json,hashlib,time
ROOT=Path(__file__).resolve().parent.parent/'rank6_quartic_truncation';OUT=Path(__file__).resolve().parent
vars=s.symbols('a b c p');loc=dict(zip(('a','b','c','p'),vars))
def need(b,m):
 if not b:raise RuntimeError(m)
@lru_cache(None)
def cnt(cols):
 return len({tuple(sorted(rows)) for rows in permutations(range(3),len(cols)) if all(c>>i&1 for c,i in zip(cols,rows))})
def perm(mask,p):return sum(((mask>>i)&1)<<p[i] for i in range(3))
pairs=sorted({min(tuple(sorted(perm(x,p) for x in pair)) for p in permutations(range(3))) for pair in combinations_with_replacement(range(8),2)})
need(len(pairs)==13,'pair orbits')
def determinant(M):
 a=[list(row) for row in M];n=len(a);prev=1;sign=1
 for k in range(n-1):
  if not a[k][k]:
   j=next((j for j in range(k+1,n) if a[j][k]),None)
   if j is None:return 0
   a[k],a[j]=a[j],a[k];sign=-sign
  pivot=a[k][k]
  for i in range(k+1,n):
   for j in range(k+1,n):
    value=a[i][j]*pivot-a[i][k]*a[k][j]
    need(value%prev==0,'Bareiss division')
    a[i][j]=value//prev
   a[i][k]=0
  prev=pivot
 return sign*a[-1][-1]
def linear(coeff,point):return coeff[4]+sum(coeff[i]*point[i] for i in range(4))
records=[];start=time.time()
for J,K in pairs:
 path=ROOT/f'BB_R_{J}_{K}.json';need(path.exists(),('missing source',J,K))
 data=json.loads(path.read_text());piv=data['pivots'];types=[i+1 for i in piv];dim=len(types);D=2*dim
 need(piv==list(range(6 if (J,K) in [(0,0),(0,1),(1,1)] else 7)),'unexpected pivots')
 E=(K.bit_count(),J.bit_count(),(J|K).bit_count(),1,cnt((J,K)))
 rv=[(cnt((K,S)),cnt((J,S)),cnt((J|K,S)),S.bit_count(),cnt((J,K,S))) for S in types]
 bv=[[(cnt((K,S,T)),cnt((J,S,T)),cnt((J|K,S,T)),cnt((S,T)),0) for T in types] for S in types]
 expr=s.sympify(data['determinant'],locals=loc);constant,factors=expr.as_coeff_mul();need(constant.is_Integer,'integer constant')
 factor_data=[];degree=0
 for factor in factors:
  base,power=factor.as_base_exp();need(power.is_Integer and power>0,'factor exponent');poly=s.Poly(base,*vars)
  need(all(x.q==1 for x in poly.coeffs()),'integer factor');degree+=int(power)*poly.total_degree()
  factor_data.append((int(power),[(e,int(c)) for e,c in poly.terms()]))
 need(degree<=D,'degree bound');num=0;digest=hashlib.sha256()
 for a in range(D+1):
  for b in range(D-a+1):
   for c in range(D-a-b+1):
    for p in range(D-a-b-c+1):
     point=(a,b,c,p);ev=linear(E,point);r=[linear(x,point) for x in rv]
     M=[[3*r[i]*r[j]-4*ev*linear(bv[i][j],point) for j in range(dim)] for i in range(dim)]
     actual=determinant(M);powers=[[x**j for j in range(D+1)] for x in point];expected=int(constant)
     for power,terms in factor_data:
      value=sum(co*powers[0][e[0]]*powers[1][e[1]]*powers[2][e[2]]*powers[3][e[3]] for e,co in terms)
      expected*=value**power
     need(actual==expected,('determinant identity',J,K,point,actual,expected));num+=1
     digest.update((str(point)+':'+str(actual)+'\n').encode())
 need(num==comb(D+4,4),'simplex coverage')
 record={'pair':[J,K],'all_pass':True,'matrix_dimension':dim,'total_degree_bound':D,'evaluation_points':num,'values_sha256':digest.hexdigest(),'source_sha256':hashlib.sha256(path.read_bytes()).hexdigest()};records.append(record)
 print('PASS',J,K,num,flush=True)
out={'all_pass':True,'profiles':len(records),'exact_evaluations':sum(v['evaluation_points'] for v in records),'method':'fraction-free integer determinants on a degree-unisolvent lower simplex','records':records,'seconds':time.time()-start}
(OUT/'determinant_checks.json').write_text(json.dumps(out,indent=2)+'\n');print({k:v for k,v in out.items() if k!='records'})
