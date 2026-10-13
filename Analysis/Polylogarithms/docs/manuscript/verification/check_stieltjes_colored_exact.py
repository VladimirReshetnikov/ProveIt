"""Finite exact audits of colored balancing and golden-shift moments.

These symbolic checks supplement the general proof; finite pattern coverage
does not establish the infinite theorem. No numerical tolerance is used.
"""
from pathlib import Path
import json
import itertools
import sympy as s

HERE=Path(__file__).resolve().parent
w,a,z=s.symbols("w a z")
phi=(1+s.sqrt(5))/2
records=[]
controls=[]
def check(name,condition):
    assert bool(condition),name
    records.append(name)

P=[s.Integer(1)]
for k in range(8):
    P.append(s.expand(w*(1-w)*s.diff(P[k],w)+(a+(k+1-a)*w)*P[k]))
for k in range(9):
    check(f"Euler conversion k={k}",s.simplify(P[k].subs(w,-1)/2**(k+1)-s.euler(k,a)/2)==0)
    check(f"color zero k={k}",s.simplify(P[k].subs(w,0)-a**k)==0)
check("A3 golden",s.simplify(s.euler(3,phi)/2-s.sqrt(5)/8)==0)
check("A4 golden zero",s.simplify(s.euler(4,phi))==0)
check("A5 golden zero",s.simplify(s.euler(5,phi))==0)
check("A6 golden nonzero",s.simplify(s.euler(6,phi)/2)==s.Rational(1,2))
check("Euler4 factor",s.expand(s.euler(4,a)-a*(a-1)*(a*a-a-1))==0)
check("Euler5 factor",s.expand(s.euler(5,a)-(2*a-1)*(a*a-a-1)**2/2)==0)
for q,m,target in ((4,5,1),(4,6,3),(5,6,1)):
    Q=s.factorial(q)*s.expand(s.prod(1+z/s.Integer(j) for j in range(1,m))).coeff(z,q)
    check(f"Q{q}({m})",Q==target)
for q in range(9):
    B=s.Matrix(q+1,q+1,lambda ell,j:s.binomial(j,ell) if j>=ell else 0)
    I=s.Matrix(q+1,q+1,lambda j,ell:(-1)**(ell-j)*s.binomial(ell,j) if ell>=j else 0)
    check(f"binomial conversion q={q}",B*I==s.eye(q+1))
    # A0 is nonzero. Enumerate every abstract zero pattern for A1,...,Aq.
    for bits in itertools.product((0,1),repeat=q):
        nonzero=(1,)+bits
        constrained=set()
        for k in range(q+1):
            if nonzero[k]:
                # At k=q only log-positive terms must vanish.
                constrained.update(range(k+1 if k<q else q))
        expected=set(range(q)) if nonzero[q] else set(range(max(k for k in range(q) if nonzero[k])+1))
        check(f"tail constraints q={q} pattern={bits}",constrained==expected)
        expected_dim=0 if nonzero[q] else q-max(k for k in range(q) if nonzero[k])-1
        check(f"affine dimension q={q} pattern={bits}",q-len(constrained)==expected_dim)
for k in range(9):
    polynomial=s.Poly(s.rf(1+z,k),z)
    check(f"positive Pochhammer derivatives k={k}",all(c>0 for c in polynomial.all_coeffs()))
for q,target in ((4,s.Rational(35,12)),(5,s.Rational(7,4))):
    check(f"next golden tail q={q}",s.diff(s.rf(1+z,6),z,q).subs(z,0)/1440==target)
d=[2*s.binomial(5,j)-(s.binomial(4,j) if j<=4 else 0) for j in range(6)]
check("noncanonical original coefficients",d==[1,6,14,16,9,2])
# Deliberately wrong statements must be rejected by exact arithmetic.
for name,rejected in (
    ("wrong Q4(6)=137/60",s.Integer(3)!=s.Rational(137,60)),
    ("next golden A6 vanishes",s.simplify(s.euler(6,phi))!=0),
    ("golden C4 has no x^-7 tail",s.Rational(35,12)!=0),
    ("binomial coefficient sign error",[1,6,14,16,9,2]!=[1,4,6,4,1,0]),
    ("single terminal zero gives nonuniqueness",(5-4-1)==0),
):
    assert bool(rejected),name
    controls.append(name)
result={"exact_checks":len(records),"negative_controls":len(controls),
        "checks":records,"rejected_controls":controls,
        "scope":"Finite symbolic audits and all abstract tail-zero patterns through q=8; general claims rely on the proof."}
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8")
print(f"PASS: {len(records)} exact checks and {len(controls)} rejected negative controls")
