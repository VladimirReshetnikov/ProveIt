"""Formal symbolic coefficient checks for the proof's logarithmic hierarchy."""
if not __debug__:
 raise SystemExit("Do not run this checker with -O or PYTHONOPTIMIZE.")
from pathlib import Path
import argparse, json, tempfile
import sympy as s
BASE=Path(__file__).resolve().parent
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument("--output-dir", help="Directory for a fresh symbolic receipt; defaults to a new temporary directory.")
args=parser.parse_args()
OUT=Path(args.output_dir).resolve() if args.output_dir else Path(tempfile.mkdtemp(prefix="a301746-symbolic-"))
if OUT==BASE:
 raise SystemExit("Choose a separate output directory; bundled receipts are immutable.")
OUT.mkdir(parents=True,exist_ok=True)
if (OUT/"log_series_verification.json").exists():
 raise SystemExit("The destination receipt already exists; choose a fresh output directory.")
x,r,c,d=s.symbols('x r c d')
u=s.symbols('u1:5')
K=3
z=1/(2*x)+r/2+sum(u[j-1]*x**j for j in range(1,K+1))
res=2*sum(u[j-1]*x**j for j in range(1,K+1))+3*s.log(2*x*z)+s.log(1+3/z+3*c/z**2+(3*c+d)/z**3)
sol={}
for j in range(1,K+1):
 coeff=s.series(res.subs(sol),x,0,j+1).removeO().expand().coeff(x,j)
 sol[u[j-1]]=s.factor(s.solve(coeff,u[j-1])[0])
z=z.subs(sol)
# log ratio avoids difficult direct rational fractional-power expansion
logForward=s.Rational(3,2)*s.log(2*x*z)+s.log(1+s.Rational(3,2)/z+3*c/z**2+(s.Rational(3,2)*c+d)/z**3)-s.log(1+3/z+3*c/z**2+(3*c+d)/z**3)/2
lf=s.series(logForward,x,0,K+1).removeO()
fwd=s.series(s.exp(lf),x,0,K+1).removeO().expand()
z=1/x+r+sum(u[j-1]*x**j for j in range(1,K+1))
res=sum(u[j-1]*x**j for j in range(1,K+1))+3*s.log(x*z)+s.log(1+s.Rational(3,2)/z+3*c/z**2+(s.Rational(3,2)*c+d)/z**3)
invsol={}
for j in range(1,K+1):
 coeff=s.series(res.subs(invsol),x,0,j+1).removeO().expand().coeff(x,j)
 invsol[u[j-1]]=s.factor(s.solve(coeff,u[j-1])[0])
z=z.subs(invsol)
logInverse=-3*s.log(x*z)+s.log(1+3/z+3*c/z**2+(3*c+d)/z**3)-2*s.log(1+s.Rational(3,2)/z+3*c/z**2+(s.Rational(3,2)*c+d)/z**3)
li=s.series(logInverse,x,0,K+1).removeO()
inv=s.series(s.exp(li),x,0,K+1).removeO().expand()
report={'forward_saddle':{str(k):str(v) for k,v in sol.items()},'forward_coefficients':{str(k):str(s.factor(fwd.coeff(x,k))) for k in range(K+1)},'inverse_saddle':{str(k):str(v) for k,v in invsol.items()},'inverse_coefficients':{str(k):str(s.factor(inv.coeff(x,k))) for k in range(K+1)}}
expected_f=[1,3*r/2,3*r**2/8-9*r/2+6*c-s.Rational(9,2)]
expected_i=[1,-3*r,6*r**2+9*r+s.Rational(9,4)-3*c]
assert all(s.simplify(fwd.coeff(x,k)-expected_f[k])==0 for k in range(3))
assert all(s.simplify(inv.coeff(x,k)-expected_i[k])==0 for k in range(3))
print(json.dumps(report,indent=2))
with (OUT/'log_series_verification.json').open('x') as stream:
 stream.write(json.dumps(report,indent=2)+'\n')
print('Saved', OUT/'log_series_verification.json')
