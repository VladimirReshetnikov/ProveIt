#!/usr/bin/env python3
"""Deterministic exact-integer tests. These are not a formal proof."""
from __future__ import annotations
import itertools as it
import json
import random
from pathlib import Path
from heisenberg_compiler import (Element, QuadraticRow, compile_quadratics,
                                choose2, hpow, hadd, matvec, circuit_system, from_json)

SEED = 20261002
rng = random.Random(SEED)
counts = {}

def check(name, cond):
    if not cond:
        raise AssertionError(name)
    counts[name] = counts.get(name, 0) + 1


def matrix(h):
    a, b, c = h
    return ((1, a, c), (0, 1, b), (0, 0, 1))


def mm(a, b):
    return tuple(tuple(sum(a[i][k]*b[k][j] for k in range(3)) for j in range(3))
                 for i in range(3))


def repeated_matrix_power(h, p):
    if p < 0:
        a, b, c = h
        h = (-a, -b, a*b-c)
    out = matrix((0, 0, 0))
    for _ in range(abs(p)):
        out = mm(out, matrix(h))
    return out


def add(x, y):
    return tuple(a+b for a,b in zip(x,y))


def combine(base, exponents, N, m):
    out = Element.identity(N,m)
    for g, e in zip(base, exponents):
        out = out * g.power(e)
    return out


for a in range(-30,31):
    for b in range(-30,31):
        check("binomial_addition", choose2(a+b) == choose2(a)+choose2(b)+a*b)
        check("binomial_polarization", a*b == choose2(a+b)-choose2(a)-choose2(b))
for _ in range(1000):
    a=tuple(rng.randint(-9,9) for _ in range(3))
    b=tuple(rng.randint(-9,9) for _ in range(3))
    check("independent_matrix_product", matrix(hadd(a,b)) == mm(matrix(a),matrix(b)))
    p=rng.randint(-12,12)
    check("independent_signed_matrix_power", matrix(hpow(a,p)) == repeated_matrix_power(a,p))

for case in range(80):
    n, m = rng.randint(1,5), rng.randint(1,4)
    rows=[]
    for _ in range(m):
        rows.append(QuadraticRow(rng.randint(-5,5),
                    tuple(rng.randint(-4,4) for _ in range(n)),
                    tuple(rng.randint(-4,4) for _ in range(n)),
                    tuple((i,j,rng.randint(-4,4)) for i in range(n)
                          for j in range(i+1,n) if rng.randrange(3))))
    s=compile_quadratics(n,rows)
    bases=s.bases()
    check("dimension_and_rank", s.N<=n+n*(n-1)//2 and
          tuple(map(len,bases))==(n+s.N,n,s.N))
    for basis in bases:
        for g,h in it.combinations(basis,2):
            check("within_phase_generator_commutation", g*h==h*g)
    for _ in range(40):
        x=tuple(rng.randint(-15,15) for _ in range(n))
        y=tuple(rng.randint(-15,15) for _ in range(n))
        u=tuple(rng.randint(-20,20) for _ in range(s.N))
        r=tuple(rng.randint(-15,15) for _ in range(s.N))
        lx=matvec(s.L,x)
        val=tuple(p+q+c for p,q,c in zip(matvec(s.C,tuple(map(choose2,lx))),
                                                matvec(s.D,x),s.c))
        check("quadratic_binomial_normal_form", val==s.evaluate(x))
        a,b,t=s.canonical(x)
        check("canonical_fiber_forward", a*b*t==s.target(s.evaluate(x)))
        check("canonical_quartic_zero", s.quartic(s.evaluate(x),x,tuple(map(choose2,lx)),x,lx)==0)
        check("basis_matches_phase_a", combine(bases[0],x+u,s.N,s.m)==s.phase_a(x,u))
        check("basis_matches_phase_b", combine(bases[1],y,s.N,s.m)==s.phase_b(y))
        check("basis_matches_phase_t", combine(bases[2],r,s.N,s.m)==s.phase_t(r))
        xp=tuple(rng.randint(-5,5) for _ in range(n))
        up=tuple(rng.randint(-5,5) for _ in range(s.N))
        rp=tuple(rng.randint(-5,5) for _ in range(s.N))
        check("phase_a_homomorphism", s.phase_a(x,u)*s.phase_a(xp,up)==s.phase_a(add(x,xp),add(u,up)))
        check("phase_b_homomorphism", s.phase_b(x)*s.phase_b(xp)==s.phase_b(add(x,xp)))
        check("phase_t_homomorphism", s.phase_t(r)*s.phase_t(rp)==s.phase_t(add(r,rp)))
        # Compare the SOS with independently multiplied group coordinates off zero.
        target=tuple(rng.randint(-50,50) for _ in range(m))
        out=s.product(x,u,y,r)
        residual=sum(a*a+b*b+4*c*c for a,b,c in out.h)
        residual+=sum((z-w)**2 for z,w in zip(out.z,s.target(target).z))
        check("off_zero_quartic_identity", residual==s.quartic(target,x,u,y,r))
        canon_u=list(map(choose2,lx))
        canon_u[rng.randrange(s.N)]+=rng.choice([-1,1])
        check("reject_perturbed_central_witness",s.product(x,canon_u,x,lx)!=s.target(s.evaluate(x)))
        yn=list(x);yn[rng.randrange(n)]+=rng.choice([-1,1])
        check("reject_unsynchronized_copy",s.product(x,tuple(map(choose2,lx)),yn,lx)!=s.target(s.evaluate(x)))
        xn=tuple(rng.randrange(16) for _ in range(n))
        rn=matvec(s.L,xn);un=tuple(map(choose2,rn))
        check("natural_domain_closure", all(z>=0 for z in rn+un))
        check("natural_weight_identity", 2*sum(xn)+sum(rn)+sum(un)==2*sum(xn)+sum(v*(v+1)//2 for v in rn))

# Exhaust all parameters in a small signed box, not merely valid/canonical ones.
s=compile_quadratics(1,[QuadraticRow(3,(-5,),(6,))])
for x,u,y,r in it.product(range(-7,8), repeat=4):
    out=s.product((x,),(u,),(y,),(r,))
    horizontal_zero=out.h[0]==(0,0,0)
    canonical=(y==x and r==x and u==choose2(x))
    check("exhaustive_small_fiber_converse", horizontal_zero==canonical)
    target=(out.z[0]+s.c[0],)
    check("exhaustive_small_quartic_equivalence", (s.quartic(target,(x,),(u,),(y,),(r,))==0)==canonical)

# Circuit y=(a*b)+a*a; residual rows are zero, last two pins a and output.
gates=[("mul",0,1),("mul",0,0),("add",2,3)]
cs=circuit_system(2,gates,[0,4])
for a,b in it.product(range(-12,13), repeat=2):
    x=(a,b,a*b,a*a,a*b+a*a)
    target=(0,0,0,a,a*b+a*a)
    check("circuit_flattening", cs.evaluate(x)==target)
    triple=cs.canonical(x)
    check("circuit_factorization", triple[0]*triple[1]*triple[2]==cs.target(target))

# Explicit non-closed product: F(x)=6x^2-5x; target -1.
local=compile_quadratics(1,[QuadraticRow(0,(-5,),(6,))])
for x in range(-5000,5001):
    check("nonclosure_integer_factorization_identity", local.evaluate((x,))[0]+1==(2*x-1)*(3*x-1))
    check("nonclosure_bounded_no_root", local.evaluate((x,))[0]!=-1)
for M in range(1,2001):
    even=1;odd=M
    while odd%2==0:
        even*=2;odd//=2
    a=pow(3,-1,even) if even>1 else 0
    b=pow(2,-1,odd) if odd>1 else 0
    # CRT by one inverse (even and odd are coprime).
    x=(a+even*((b-a)*pow(even,-1,odd)%odd))%M if odd>1 else a%M
    check("nonclosure_modular_root", ((2*x-1)*(3*x-1))%M==0)
    A,B,T=local.canonical((x,));out=A*B*T
    check("nonclosure_finite_quotient_factorization",out.h==((0,0,0),) and (out.z[0]+1)%M==0)

# Integer logarithm identities underlying the two-phase theorem.
def logs(g):
    return tuple((a,b,2*c-a*b) for a,b,c in g.h)
for _ in range(3000):
    a=tuple(rng.randint(-20,20) for _ in range(3))
    b=tuple(rng.randint(-20,20) for _ in range(3))
    g=hadd(a,b)
    la=2*a[2]-a[0]*a[1];lb=2*b[2]-b[0]*b[1]
    lg=2*g[2]-g[0]*g[1]
    check("two_phase_linearization",lg==la+lb+a[0]*g[1]-a[1]*g[0])

invalid=[{"n":True,"rows":[]},
 {"n":1,"rows":[{"constant":0,"linear":[0.0],"diagonal":[0]}]},
 {"n":1,"rows":[{"constant":0,"linear":[0],"diagonal":[0],"cross":[[0,0,1]]}]}]
for obj in invalid:
    try:
        from_json(obj)
    except (ValueError, TypeError):
        check("invalid_input_rejection",True)
    else:
        raise AssertionError("invalid input accepted")

root=Path(__file__).resolve().parents[1]
mult=compile_quadratics(3,[QuadraticRow(0,(0,0,-1),(0,0,0),((0,1,1),))])
for name,spec in [("multiplication",mult),("profinite_obstruction",local),("circuit",cs)]:
    (root/"examples"/(name+".json")).write_text(json.dumps(spec.to_json(),indent=2)+"\n")
    (root/"examples"/(name+"_input.json")).write_text(json.dumps(spec.to_json()["input"],indent=2)+"\n")
receipt={"status":"PASS","seed":SEED,"arithmetic":"exact Python integers",
         "tests":counts,"total_assertions":sum(counts.values()),
         "scope":"finite deterministic checks; proofs are in the article; no Lean or universal matrix instantiation"}
(root/"verification_receipt.json").write_text(json.dumps(receipt,indent=2)+"\n")
print(json.dumps(receipt,indent=2))
