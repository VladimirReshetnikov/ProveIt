import sympy as S,json,argparse
from pathlib import Path
parser=argparse.ArgumentParser()
parser.add_argument("--output",required=True,help="Destination for regenerated exact coefficient lists")
args=parser.parse_args()
from math import comb
x,y,a,z=S.symbols('x y a z');n=x+3;m=y+2
bc=lambda N,k:S.prod(N-i for i in range(k))/S.factorial(k) if k>=0 else 0
out=[]
summary=[]
for branch in range(2):
 u=n*(a+z) if branch==0 else n*a
 v=m*a if branch==0 else m*(a+z)
 A=[S.expand(sum(comb(2,i)*comb(3,j)*bc(n,k-i)*bc(m,k-j)*u**i*v**j for i in range(3) for j in range(4) if i+j>=k)) for k in range(6)]
 for k in range(1,5):
  D=S.Poly(S.expand(k*(5-k)*A[k]**2-(k+1)*(6-k)*A[k-1]*A[k+1]),x,y,a,z)
  assert all(c>0 for c in D.coeffs())
  summary.append({'branch':branch,'gap':k,'terms':len(D.terms()),'minimum_coefficient':str(min(D.coeffs()))})
  out.append({'branch':branch,'k':k,'terms':[[list(mon),str(c)] for mon,c in D.terms()]})
Path(args.output).write_text(json.dumps(out))
print(json.dumps({'status':'PASS','sympy_version':S.__version__,'certificate_rows':summary},indent=2))
