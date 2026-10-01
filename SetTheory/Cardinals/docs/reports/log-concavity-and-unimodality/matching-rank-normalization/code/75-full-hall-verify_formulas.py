"""Compare the twelve printed formulas with independently generated products."""
import sympy as s,json
from pathlib import Path
from increment_families import raw,ratios,k,N,K,L,z
A=k*(N-k);B=(k+1)*(N-k+1);a=K
T=L[0]*L[-1];S=L[1]*L[-2]
X=L[-1]**2;Y=L[-2]*L[0];Z=L[-3]*L[1]
M=L[-2]*L[-1];NN=L[-3]*L[0]
U=L[-2]**2;W=L[-3]*L[-1]
manual={}
manual[((1,0),0)]=2*A*T-B*a/(a+1)*(T+S)
manual[((2,0),0)]=A*X-B*a/(a+1)*Y
manual[((2,0),1)]=2*manual[((2,0),0)]
manual[((1,1),0)]=2*A*(X+Y)-B*a/(a+1)*(X+2*Y+Z)
manual[((1,1),1)]=4*A*X+2*A*Y-B*(X+4*a/(a+1)*Y+(a-1)/(a+1)*Z)
manual[((2,1),0)]=2*A*M-B*a/(a+1)*(M+NN)
manual[((2,1),1)]=2*manual[((2,1),0)]
S2=2+2*z*(a-1)/a;H2=z+(a-1)/a;J2=(a-1)/a+z*(a-1)*(a-2)/(a*(a+1))
manual[((2,1),2)]=A*M*S2-B*(M*H2+NN*J2)
manual[((2,2),0)]=A*U-B*a/(a+1)*W
manual[((2,2),1)]=2*manual[((2,2),0)]
manual[((2,2),2)]=A*U*(1+2*z*(a-1)/a)-B*W*((a-1)/a+2*z*(a*a-a+1)/(a*(a+1)))
manual[((2,2),3)]=2*z*(A*U-B*(a-1)/a*W)
for (lam,j),f in manual.items():
 assert s.factor(raw(lam,j).subs(ratios(j))-f)==0,(lam,j)
# Delicate endpoints in the printed pattern21 proof.
ell=s.symbols('ell');nu=(k-2)/k
D=k*ell*S2-(k+1)*(ell+1)*(H2+nu*J2)
assert s.factor(D.subs({ell:a,z:0})-2*(a*a+k*k-1)/(a*k))==0
assert s.factor(D.subs({ell:a,z:s.Rational(1,2)})-((k-a)**2+(k-a)+2*a*(a-1))/(a*k))==0
# Explicit pattern22 ratio defect.
S22=1+2*z*(a-1)/a;T22=(a-1)/a+2*z*(a*a-a+1)/(a*(a+1))
assert s.factor(a/(a+1)*S22-T22-(1-2*z)/(a*(a+1)))==0
out={'printed_coefficient_families_verified':len(manual),'pattern21_endpoint_identities_verified':2,'pattern22_ratio_identity_verified':True,'all_checks_passed':True}
Path(__file__).with_name('formula_verification.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
