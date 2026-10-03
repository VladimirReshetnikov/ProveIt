#!/usr/bin/env python3
"""Run reproducible exact tests and export the example quartic.

Usage from the bundle root: python code/verify.py
Requires Python >=3.10 and SymPy. Most tests use the standard library only.
Finite tests support the implementation; the general theorems are proved in
article.tex. They do not constitute Lean or Rocq verification.
"""
from __future__ import annotations
from decimal import Decimal, localcontext
from fractions import Fraction
from itertools import product
from pathlib import Path
import json
import math
import random
import sys
import sympy as sp
from normalization import optimal_budget, make_assignment, numeric_residuals, compile_system
from quantum_exact import Circuit, sign_sqrt2
from prefix_allocator import PrefixAllocator

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "artifacts"
OUT.mkdir(exist_ok=True)
report = {"status":"PASS", "seed":20260930, "python":sys.version.split()[0],
          "sympy":sp.__version__, "limitations":[
              "Finite implementation tests are not general mathematical proofs.",
              "No Lean/Rocq kernel verification was run.",
              "The fixed universal MRDP polynomial is not expanded by this code.",
              "Only the finite normalization certificate is symbolically compiled."]}

def check_assign(a,n,m):
    residuals=numeric_residuals(a,n,m)
    assert len(residuals)==5*n*m+m+6*n+4
    return all(x>=0 for x in a.values()) and all(x==0 for x in residuals)

# Exhaustive schedules and independent exhaustive pivot choices.
choices=[(1,3),(1,2),(1,1),(2,1),(3,1)]
deltas=[(1,10),(1,3),(1,2),(1,1)]
schedules=cases=pivot_candidates=feasible=0
for n in range(4):
    for rows in product(choices, repeat=n+1):
        schedules+=1
        budget,_,_=optimal_budget(rows)
        for alpha,beta in deltas:
            cases+=1
            expected=Fraction(alpha,beta)<=budget
            candidate=make_assignment(rows,alpha,beta)
            assert check_assign(candidate,n,2)==expected
            hits=0
            for pivots in product(range(2), repeat=n):
                pivot_candidates+=1
                a=make_assignment(rows,alpha,beta,pivots)
                hits+=check_assign(a,n,2)
            assert hits==int(expected)
            feasible+=int(expected)
report["normalization_exhaustive"]={"schedules":schedules,"parameter_cases":cases,
    "pivot_candidates":pivot_candidates,"feasible_cases":feasible,
    "claim":"Every case has exactly one valid forced-pivot candidate iff the budget test holds."}

# Random multi-label schedules, ties, denominator rescaling, and large integers.
rng=random.Random(20260930)
random_cases=large_cases=0
for m in (2,3,4,7):
    for n in range(6):
        for _ in range(8):
            rows=[[rng.randint(1,100) for _ in range(m)] for _ in range(n+1)]
            budget,_,_=optimal_budget(rows)
            scaled=[]
            for row in rows:
                factor=rng.randint(1,30)
                scaled.append([factor*x for x in row])
            assert optimal_budget(scaled)[0]==budget
            alpha,beta=budget.numerator,budget.denominator
            assert check_assign(make_assignment(rows,alpha,beta),n,m)
            random_cases+=1
            if n==2:
                big=[[x*10**100 for x in row] for row in rows]
                assert optimal_budget(big)[0]==budget
                assert check_assign(make_assignment(big,alpha,beta),n,m)
                large_cases+=1
report["normalization_random"]={"cases":random_cases,"large_integer_cases":large_cases,
                                "large_integer_scale":"10^100"}

# Symbolic quartic, exact example, and independent substitution checks.
S=compile_system(2,2)
P=sp.Poly(sp.expand(S.polynomial),*(S.parameters+S.witnesses))
assert P.total_degree()==4
assert len(S.witnesses)==33 and len(S.residuals)==38
rows=[[1,1],[2,1],[1,1]]
a=make_assignment(rows,1,2)
sub={x:a[str(x)] for x in S.parameters+S.witnesses}
assert all(r.subs(sub)==0 for r in S.residuals)
mutations=0
for w in S.witnesses:
    b=dict(a); b[str(w)]+=1
    assert not check_assign(b,2,2)
    mutations+=1
# This checks each single-coordinate +1 mutation, not all possible bad witnesses.
report["symbolic_certificate"]={"N":2,"m":2,"parameters":len(S.parameters),
    "witnesses":len(S.witnesses),"residuals":len(S.residuals),
    "total_degree":P.total_degree(),"expanded_monomials":len(P.terms()),
    "single_coordinate_mutations_rejected":mutations,
    "optimal_initial_mass":"1/2","example_rows":rows}
(OUT/"normalization_quartic_N2_m2.txt").write_text(
    "P = sum of the squares of the residuals in the JSON file.\n\nExpanded P:\n"+str(P.as_expr())+"\n")
(OUT/"normalization_quartic_N2_m2.json").write_text(json.dumps({
    "parameters":[str(x) for x in S.parameters],"witnesses":[str(x) for x in S.witnesses],
    "residuals":[str(r) for r in S.residuals],
    "polynomial_definition":"sum(r*r for r in residuals)","domain":"all variables natural",
    "example_assignment":a},indent=2)+"\n")

# Exact quadratic-field signs, with Decimal only as an independent small-value oracle.
sign_cases=0
with localcontext() as ctx:
    ctx.prec=80
    root=Decimal(2).sqrt()
    for A in range(-80,81):
        for B in range(-80,81):
            x=Decimal(A)+Decimal(B)*root
            expected=int(x>0)-int(x<0)
            assert sign_sqrt2(A,B)==expected
            sign_cases+=1
p,q=1,0
for k in range(1,201):
    p,q=p+2*q,p+q
    assert p*p-2*q*q==(-1)**k
    assert sign_sqrt2(p,-q)==(-1)**k
report["quadratic_field_sign"]={"lattice_cases":sign_cases,
    "near_cancelling_Pell_cases":200,"largest_Pell_digits":len(str(p))}

# Quantum exact examples.
hh=Circuit(1).apply("H",0).apply("H",0)
assert hh.probability([0])==(Fraction(1),Fraction(0))
hth=Circuit(1).apply("H",0).apply("T",0).apply("H",0)
assert hth.probability([0])==(Fraction(1,2),Fraction(1,4))
assert hth.probability([1])==(Fraction(1,2),Fraction(-1,4))
bell=Circuit(2).apply("H",0).apply("CNOT",1,0)
assert bell.probability([0,3])==(Fraction(1),Fraction(0))
assert bell.probability([0])==(Fraction(1,2),Fraction(0))
quantum_cases=0
for qubits in (1,2,3,4):
    for _ in range(25):
        c=Circuit(qubits)
        for j in range(30):
            gate=rng.choice(["H","T","S","X"]+(["CNOT"] if qubits>1 else []))
            target=rng.randrange(qubits)
            control=rng.choice([k for k in range(qubits) if k!=target]) if gate=="CNOT" else None
            c.apply(gate,target,control)
            c.assert_normalized()
        quantum_cases+=1
report["quantum_exact"]={"random_circuits":quantum_cases,"gates_per_circuit":30,
    "exact_norm_checks":quantum_cases*30,"HTH_P0":"1/2 + sqrt(2)/4",
    "HH_P0":"1","Bell_P00":"1/2"}

# Exact dyadic allocation of lower bounds for the irrational HTH output law.
def dyadic_floor(A: Fraction,B: Fraction,k:int)->Fraction:
    lo,hi=0,1<<k
    while lo<hi:
        mid=(lo+hi+1)//2
        X=A*(1<<k)-mid; Y=B*(1<<k)
        D=math.lcm(X.denominator,Y.denominator)
        if sign_sqrt2(int(X*D),int(Y*D))>=0: lo=mid
        else: hi=mid-1
    return Fraction(lo,1<<k)
alloc=PrefixAllocator(); old=[Fraction(0),Fraction(0)]
for k in range(1,13):
    new=[dyadic_floor(Fraction(1,2),Fraction(1,4),k),
         dyadic_floor(Fraction(1,2),Fraction(-1,4),k)]
    for i in range(2):
        alloc.add_dyadic(new[i]-old[i],str(i))
        assert alloc.total(str(i))==new[i]
    alloc.check(); old=new
report["prefix_allocation"]={"stages":12,"allocated_words":len(alloc.allocated),
    "mass_0":str(old[0]),"mass_1":str(old[1]),"total":str(alloc.total())}
(OUT/"HTH_prefix_allocation.json").write_text(json.dumps(alloc.allocated,indent=2)+"\n")

# Coherent-density interpretation example: I/2 -> coherent sigma -> I/2.
I=sp.eye(2)/2
matrix_cases=0
for t in [sp.Rational(1,20),sp.Rational(1,6),sp.Rational(1,4),sp.Rational(2,5)]:
    sigma=sp.Matrix([[sp.Rational(1,2),t],[t,sp.Rational(1,2)]])
    R1=1/(1-2*t); R2=1+2*t
    for D in (R1*sigma-I,R2*I-sigma):
        assert D.det()==0 and D.trace()>0
        assert D[0,0]>=0 and D[1,1]>=0
    assert sp.simplify(1/(R1*R2)-(1-2*t)/(1+2*t))==0
    matrix_cases+=1
# A genuinely noncommuting cycle with algebraic optimal factors.
rho=sp.diag(sp.Rational(2,3),sp.Rational(1,3))
sigma=sp.Matrix([[sp.Rational(1,2),sp.Rational(1,6)],
                 [sp.Rational(1,6),sp.Rational(1,2)]])
assert rho*sigma != sigma*rho
K=(9+sp.sqrt(17))/8
for D in (K*sigma-rho,K*rho-sigma):
    assert sp.simplify(D.det())==0
    assert sp.simplify(D.trace()).is_positive
assert sp.simplify(K**2-(49+9*sp.sqrt(17))/32)==0
assert sp.simplify(1/K**2-(49-9*sp.sqrt(17))/32)==0
report["matrix_budget"]={"exact_cases":matrix_cases,
    "t_1_over_6_cost":"2","t_1_over_6_max_initial_mass":"1/2",
    "dephased_cost":"1","noncommuting_cycle_checked":True,
    "noncommuting_cycle_cost":"(49 + 9 sqrt(17))/32",
    "noncommuting_cycle_max_initial_mass":"(49 - 9 sqrt(17))/32",
    "noncommuting_cycle_dephased_cost":"2"}

# Symbolic checks of the integrands in the exact binary path identity.
u=sp.Symbol("u",positive=True)
phi=-sp.log(u*(1-u))/2
density=1/(2*u*(1-u))
assert sp.simplify(density+sp.diff(phi,u)-1/(1-u))==0
assert sp.simplify(-density+sp.diff(phi,u)+1/u)==0
report["binary_variation_symbolic"]={"upward_identity":True,"downward_identity":True}

# The logarithmic variation inequality: diagnostic checks, separate from exact certificates.
max_ratio=0.0
for n in (1,2,5,10,50,100):
    delta=0.5
    factor=math.exp(math.log(1/delta)/n)
    eps=(factor-1)/(2*(factor+1))
    variation=2*n*eps
    bound=0.5*math.log(1/delta)
    assert variation<=bound+1e-12
    max_ratio=max(max_ratio,variation/bound)
report["variation_diagnostics"]={"arithmetic":"floating point; illustrative only",
    "largest_sharpness_ratio":max_ratio}

(OUT/"verification.json").write_text(json.dumps(report,indent=2)+"\n")
print(json.dumps(report,indent=2))
