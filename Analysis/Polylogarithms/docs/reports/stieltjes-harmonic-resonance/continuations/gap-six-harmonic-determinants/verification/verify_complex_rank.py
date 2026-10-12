#!/usr/bin/env python3
"""Independent exact checks for complex harmonic degree and rational primitives.

The infinite theorem is proved in complex_rank.tex.  This script checks its
finite identities over QQ(i), including a varying-kernel pencil and an actual
nonreal cutoff exception.  No numeric rank tolerance or fitted polynomial is
used.  Run: python verify_complex_rank.py
"""
from __future__ import annotations

import json
from pathlib import Path
from itertools import combinations
import sympy as s

ROOT = Path(__file__).resolve().parents[1] / "results"
n, N, X, Y, lam = s.symbols("n N X Y lam")
I = s.I
checks: list[dict] = []


def check(name, expression):
    answer = s.cancel(expression)
    if answer != 0:
        raise AssertionError((name, answer))
    checks.append({"name": name, "status": "passed"})


def truth(name, condition):
    if not condition:
        raise AssertionError(name)
    checks.append({"name": name, "status": "passed"})


def psum(k):
    return s.expand((s.bernoulli(k + 1, N + 1) - s.bernoulli(k + 1, 0)) / (k + 1))


def polynomial_sum(f):
    p = s.Poly(s.cancel(f), n)
    return s.expand(sum(c * psum(k[0]) for k, c in p.terms()))


def moment_decomposition(r, groups):
    """groups=[(base, [(nonnegative integer shift,residue),...]),...]."""
    rational_moments = []
    harmonic_moments = [[] for _ in groups]
    for k in range(2 * r - 1):
        total = 0
        for g, (base, entries) in enumerate(groups):
            coeff = 0
            for shift, residue in entries:
                alpha = base + shift
                poly = sum((-alpha) ** j * psum(k - j - 1) for j in range(k))
                endpoint = sum(1 / (N + base + j + 1) - 1 / (base + j)
                               for j in range(shift))
                total += residue * (poly + (-alpha) ** k * endpoint)
                coeff += residue * (-alpha) ** k
            harmonic_moments[g].append(s.simplify(coeff))
        rational_moments.append(s.cancel(total))
    D = s.Matrix(r, r, lambda i, j: rational_moments[i + j])
    Cs = [s.Matrix(r, r, lambda i, j: values[i + j]) for values in harmonic_moments]
    return D, Cs


def direct_matrix(r, cutoff, groups):
    result = s.zeros(r)
    for k in range(cutoff + 1):
        weight = sum(residue / (k + base + shift)
                     for base, entries in groups for shift, residue in entries)
        v = s.Matrix([s.Integer(k) ** j for j in range(r)])
        result += weight * v * v.T
    return result.applyfunc(s.simplify)


# Symbolic rank-one minor identity, including a genuinely complex isotropic tail.
a, b, c, t, x, y, z = s.symbols("a b c t x y z")
A0 = s.Matrix([[a, b], [b, c]])
u = s.Matrix([x, y, z])
A = s.diag(A0, s.zeros(1))
check("rank-one principal minor identity", (A + t * u * u.T).det() - t*z*z*A0.det())
A_iso = s.diag(s.Matrix([[2, 1], [1, 3]]), s.zeros(2))
u_iso = s.Matrix([1 + I, 2 - I, 1, I])
truth("nonzero isotropic lower vector", (u_iso[2:, :].T * u_iso[2:, :])[0] == 0)
truth("isotropic rank update still increases rank", (A_iso + (2+I)*u_iso*u_iso.T).rank() == 3)


# Adjacent-pole family: derive moments via polynomial division, then check the
# displayed coefficients against direct determinant expansion.
groups = [(s.Integer(1), [(0, s.Integer(1)), (1, lam)])]
family = {}
for r in (3, 4):
    D, (C,) = moment_decomposition(r, groups)
    truth(f"family r={r}: pencil rank", C.rank() == 2)
    q = r - 2
    P = (n + 1) * (n + 2)
    K = s.Matrix(r, q, lambda i, j: s.Poly(s.expand(P*n**j), n).coeff_monomial(n**i))
    truth(f"family r={r}: common kernel", C*K == s.zeros(r, q))
    G = (K.T*D*K).applyfunc(s.cancel)
    G_direct = s.Matrix(q, q, lambda i, j: polynomial_sum(P*((n+2)+lam*(n+1))*n**(i+j)))
    for i in range(q):
        for j in range(q):
            check(f"family r={r}: compressed sum {i},{j}", G[i,j]-G_direct[i,j])
            check(f"family r={r}: primitive difference {i},{j}",
                  G[i,j]-G[i,j].subs(N,N-1)
                  -(P*((n+2)+lam*(n+1))*n**(i+j)).subs(n,N))
    if r == 3:
        expected = lam*(N+1)*(N+2)*(N+3)*(3*(lam+1)*N+4*lam+8)/12
    else:
        expected = (lam*N*(N+1)**2*(N+2)**2*(N+3)**2*(N+4)
                    *(6*(lam+1)**2*N**2+(14*lam**2+48*lam+34)*N
                      +10*lam**2+45*lam+50)/3600)
    check(f"family r={r}: displayed leading coefficient", lam*G.det()-expected)
    for cutoff in (0, 1, 2, 3, 5):
        D0, C0 = D.subs({N: cutoff,lam:I}), C.subs(lam,I)
        P0 = s.Poly((D0+X*C0).det(),X)
        check(f"family r={r},N={cutoff}: independent determinant coefficient",
              P0.coeff_monomial(X**2)-expected.subs({N:cutoff,lam:I}))
        actual = direct_matrix(r,cutoff,[(s.Integer(1),[(0,s.Integer(1)),(1,I)])])
        H = s.harmonic(cutoff+1)
        truth(f"family r={r},N={cutoff}: finite matrix equality", (D0+H*C0-actual).applyfunc(s.simplify)==s.zeros(r))
    family[str(r)] = str(s.factor(expected))


# Three-pole nonreal exception, distinct from a real rational weight times a
# constant phase.  At N=3 there are four nonzero nodes, yet harmonic degree drops.
exception_groups=[(s.Integer(1),[(0,s.Integer(39)),(1,78*I),(2,-61-95*I)])]
D,(C,)=moment_decomposition(4,exception_groups)
truth("nonreal example: pencil rank three",C.rank()==3)
K=s.Matrix([6,11,6,1])
truth("nonreal example: exact kernel",C*K==s.zeros(4,1))
G=s.cancel((K.T*D*K)[0])
expected=-(N-3)*(N+1)*(N+2)*(N+3)*(N+4)*((22+17*I)*N+56+22*I)/6
check("nonreal example: complete cutoff polynomial",G-expected)
check("nonreal example: principal multiplier",C[:3,:3].det()-(1155960-742248*I))
P3=s.Poly((D.subs(N,3)+X*C).det(),X)
expected_P3=((-22046418576+2049048144*I)*X**2
             +(s.Rational(455872142232,5)-7792299840*I)*X
             -s.Rational(2356478577592,25)+s.Rational(183512850456,25)*I)
check("nonreal example: full exceptional determinant polynomial",P3.as_expr()-expected_P3)
truth("nonreal example: degree exactly two",P3.degree()==2)
actual=direct_matrix(4,3,exception_groups)
check("nonreal example: nonzero evaluated determinant",actual.det()-(55033-146419*I)/25)
weights=[s.simplify(sum(residue/(k+base+shift) for base,entries in exception_groups for shift,residue in entries))
         for k in range(4)]
truth("nonreal example: all four weights nonzero",all(w!=0 for w in weights))
vandermonde=s.prod((j-i)**2 for i,j in combinations(range(4),2))
check("nonreal example: independent Vandermonde product",actual.det()-vandermonde*s.prod(weights))
check("nonreal example: correct harmonic substitution",P3.as_expr().subs(X,s.Rational(25,12))-actual.det())


# A rational weight with a genuinely varying-kernel harmonic pencil.
# Moment residues in separate integer-shift orbits extract coefficients n^1
# and n^3, respectively, from polynomials of degree <= 4.
Q1=s.prod(n+j for j in range(1,6))
Q2=s.prod(n+s.Rational(1,2)+j for j in range(5))
P1=n**3+15*n**2+85*n+225
P2=n+s.Rational(25,2)
entries1=[(j,s.cancel(P1/s.diff(Q1,n)).subs(n,-j-1)) for j in range(5)]
entries2=[(j,I*s.cancel(P2/s.diff(Q2,n)).subs(n,-s.Rational(1,2)-j)) for j in range(5)]
vgroups=[(s.Integer(1),entries1),(s.Rational(1,2),entries2)]
R=sum(residue/(n+base+shift) for base,entries in vgroups for shift,residue in entries)
check("varying kernel: rational weight construction",R-P1/Q1-I*P2/Q2)
D,Cs=moment_decomposition(3,vgroups)
C=X*Cs[0]+Y*Cs[1]
expected_C=s.Matrix([[0,X,0],[X,0,I*Y],[0,I*Y,0]])
truth("varying kernel: residue pencil",C==expected_C)
truth("varying kernel: generic rank two",C.rank()==2)
truth("varying kernel: no common kernel",s.Matrix.vstack(Cs[0],Cs[1]).rank()==3)
K=s.Matrix([I,0,-1])
truth("varying kernel: one maximal member kernel",C.subs({X:1,Y:1})*K==s.zeros(3,1))
for j,Cj in enumerate(Cs):
    check(f"varying kernel: simultaneous isotropy {j}",(K.T*Cj*K)[0])
G=s.cancel((K.T*D*K)[0])
check("varying kernel: rational primitive identity",G-G.subs(N,N-1)-(R*(I-n*n)**2).subs(n,N))
truth("varying kernel: primitive is not identically zero",G!=0)
for cutoff in (0,1,3,6):
    D0=D.subs(N,cutoff)
    actual=direct_matrix(3,cutoff,vgroups)
    harmonic=[sum(1/(k+base) for k in range(cutoff+1)) for base,_ in vgroups]
    truth(f"varying kernel,N={cutoff}: finite matrix equality",
          (D0+harmonic[0]*Cs[0]+harmonic[1]*Cs[1]-actual).applyfunc(s.simplify)==s.zeros(3))
    P=s.Poly((D0+C).det(),X,Y)
    highest=sum(coeff*X**exps[0]*Y**exps[1] for exps,coeff in P.terms() if sum(exps)==2)
    check(f"varying kernel,N={cutoff}: highest component",
          highest-(D0[0,0]*Y**2+2*I*D0[0,2]*X*Y-D0[2,2]*X**2))

report={"status":"passed","arithmetic":"exact rational arithmetic over QQ(i), plus symbolic parameters",
        "check_count":len(checks),"checks":checks,"adjacent_family_coefficients":family,
        "nonreal_exception":{"compression":str(s.factor(expected)),"polynomial":str(expected_P3),
                             "evaluated_determinant":"(55033 - 146419*I)/25"},
        "varying_kernel":{"weight":str(P1/Q1+I*P2/Q2),
                           "primitive_denominator":str(s.factor(s.denom(G))),
                           "primitive_numerator_degree":s.degree(s.numer(G),N)}}
(ROOT/"complex_rank_verification.json").write_text(json.dumps(report,indent=2,default=str)+"\n")
print(json.dumps({"status":"passed","check_count":len(checks),"result":"complex_rank_verification.json"}))
