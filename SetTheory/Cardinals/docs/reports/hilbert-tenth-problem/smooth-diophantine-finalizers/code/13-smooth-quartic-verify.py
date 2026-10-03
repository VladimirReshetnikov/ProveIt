"""Reproduce exact symbolic identities, finite checks, and exported examples.

Run from any directory: python code/verify.py
Finite checks supplement, but do not replace, the proofs in article.tex.
"""
from __future__ import annotations
from collections import Counter
from fractions import Fraction
from itertools import product
from pathlib import Path
import json
import random
import sys
import platform
import sympy as sp
from smooth_compiler import (QuadraticSystem, compile_smooth, dyadic_point,
                             polynomial_terms, two_adic_residues, four_squares, weighted_four_squares)
from counter_frontend import Program, Instruction, compile_counter, countdown

ROOT = Path(__file__).resolve().parents[1]
COUNTS = Counter()


def check(name: str, statement: bool):
    if not statement:
        raise AssertionError(name)
    COUNTS[name] += 1


def rejected(call):
    try:
        call()
    except (TypeError, ValueError):
        COUNTS["invalid_input_rejections"] += 1
    else:
        raise AssertionError("Invalid input was accepted")


def independent_eval(export: dict, point):
    if len(point) != len(export["variables"]):
        raise ValueError("Wrong dimension")
    total = 0
    for term in export["terms"]:
        value = term["coefficient"]
        for x, e in zip(point, term["exponents"]):
            value *= x**e
        total += value
    return total


def check_symbolic(cert):
    jc = cert.jacobian_certificate()
    R = cert.t*cert.u-1
    check("symbolic_Euler", sp.expand(jc["E"] - 4*cert.H) == 0)
    check("symbolic_J", sp.expand(jc["J"] - (8*R**2-4)) == 0)
    check("symbolic_constant_four", jc["four"] == 4)
    check("symbolic_Jacobian_unit", jc["unit"] == 1)
    check("exact_quartic", sp.Poly(cert.F, *cert.variables).total_degree() == 4)
    A, B = cert.jacobian_coefficients()
    bezout = A*cert.F + sum(b*sp.diff(cert.F,v) for b,v in zip(B, cert.variables))
    check("explicit_Bezout_identity", sp.expand(bezout) == 1)
    check("Bezout_coefficient_degree", all(sp.Poly(b,*cert.variables).total_degree() <= 4 for b in (A,)+B))
    for f, q in zip(cert.source.residuals, cert.homogeneous):
        check("homogenization", sp.expand(q.subs(cert.t, 1)-f) == 0)
        for alpha, _ in polynomial_terms(q, cert.source.variables+(cert.t,)):
            check("homogeneous_quadratic_source", sum(alpha) == 2 or q == 0)


def test_core():
    x, y = sp.symbols("x y")
    sources = [QuadraticSystem((x,), (x*x-1,)),
               QuadraticSystem((x,), (2*x-1,)),
               QuadraticSystem((x,), (sp.Integer(1),)),
               QuadraticSystem((x,y), (x-y*y, y-2)),
               QuadraticSystem((), (sp.Integer(1),)),
               QuadraticSystem((), ())]
    rng = random.Random(20261002)
    basis = (sp.Integer(1), x, y, x*x, x*y, y*y)
    for _ in range(20):
        sources.append(QuadraticSystem((x,y), tuple(sum(rng.randint(-3,3)*b for b in basis)
                                                   for _ in range(rng.randint(1,3)))))
    for i, source in enumerate(sources):
        cert = compile_smooth(source)
        check_symbolic(cert)
        point, metadata = dyadic_point(cert)
        check("dyadic_point_exact", cert.evaluate(point) == 0)
        check("dyadic_denominators", all(int(sp.denom(v)) & (int(sp.denom(v))-1) == 0 for v in point))
        check("dyadic_nonnegative", all(v >= 0 for v in point))
        c = metadata["c"]
        residues = two_adic_residues(c, 16)
        previous = None
        for rr in residues:
            m, z = rr["modulus"], rr["z"]
            check("two_adic_equation", (c+2*z*z-z) % m == 0)
            check("two_adic_unit_derivative", (4*z-1) % 2 == 1)
            if previous:
                check("two_adic_compatibility", z % previous["modulus"] == previous["z"])
            previous = rr
        exported = cert.export()
        for _ in range(20):
            values = tuple(rng.randint(-3,3) for _ in cert.variables)
            # Direct residual formula, evaluated without using the expanded F.
            n = len(source.variables)
            xx, t, u, zz = values[:n], values[n], values[n+1], values[n+2:]
            sub = dict(zip(source.variables+(cert.t,), xx+(t,)))
            direct = sum(int(q.subs(sub))**2 for q in cert.homogeneous)
            direct += (t*u-1)**2 + sum(w*(2*z*z-z) for w,z in zip((1,1,2),zz))
            check("independent_sparse_evaluation", independent_eval(exported, values) == direct)
        # The dyadic point reduces integrally at every odd prime.
        for p in (3,5,7,11,13,17,19,23,29,31):
            modular = tuple(int(sp.numer(v))*pow(int(sp.denom(v)), -1, p) % p for v in point)
            check("odd_prime_points", independent_eval(exported, modular) % p == 0)
        if i == 2:
            save_example("inconsistent", cert, point, metadata, residues)
        if i < 3:
            # Exhaust all tuples in an explicitly declared 6-dimensional box.
            f_fast = sp.lambdify((x,), source.residuals[0], "math")
            F_fast = sp.lambdify(cert.variables, cert.F, "math")
            integer_roots = []
            natural_roots = []
            for a,t,u in product(range(-2,3), repeat=3):
                for zz in product(range(-1,2), repeat=3):
                    values = (a,t,u)+zz
                    actual = F_fast(*values) == 0
                    expected = (t == u and t in (-1,1) and zz == (0,0,0)
                                and f_fast(t*a) == 0)
                    check("exhaustive_integer_box", actual == expected)
                    if actual:
                        integer_roots.append(values)
                    if all(v >= 0 for v in values):
                        exp_nat = t == u == 1 and zz == (0,0,0) and f_fast(a) == 0
                        check("exhaustive_natural_subbox", actual == exp_nat)
                        if actual:
                            natural_roots.append(values)
            if i == 0:
                check("integer_sign_copies", len(integer_roots) == 4)
                check("natural_unique_copy", len(natural_roots) == 1)
            else:
                check("inconsistent_box_empty", not integer_roots)
    # The printed simple dyadic example, independently from the constructor.
    cert = compile_smooth(QuadraticSystem((), (sp.Integer(1),)))
    manual = (sp.Rational(1,2), sp.Integer(3), sp.Rational(1,4), sp.Rational(1,2),
              sp.Rational(3,8))
    check("printed_inconsistent_dyadic_point", cert.evaluate(manual) == 0)
    # Verify the characteristic-2 affine-space graph identity.
    cert = compile_smooth(QuadraticSystem((x,y), (x*x+x*y-3, y+4)))
    expected_mod2 = cert.H + (cert.t*cert.u-1)**2 - sum(w*z for w,z in zip((1,1,2),cert.z))
    check("characteristic_two_graph", all(int(c) % 2 == 0 for _,c in polynomial_terms(cert.F-expected_mod2, cert.variables)))
    # Explicit bad-prime witnesses for k=1,2,3 guards.
    for k,p in ((1,7),(2,3),(3,5)):
        Fk = cert.H+(cert.t*cert.u-1)**2+sum(2*z*z-z for z in cert.z[:k])
        vv = cert.source.variables+(cert.t,cert.u)+cert.z[:k]
        sub = {v: 0 for v in vv}
        sub.update({z: pow(4,-1,p) for z in cert.z[:k]})
        check("restricted_guard_bad_prime_value", int(Fk.subs(sub)) % p == 0)
        for v in vv:
            check("restricted_guard_bad_prime_gradient", int(sp.diff(Fk,v).subs(sub)) % p == 0)
    # Universal guard-family elimination, including the second good size k=16.
    R = cert.t*cert.u-1
    for k in range(1,25):
        Jk = 8*R**2-k
        Fu = 2*cert.t*R
        rhs = 4*cert.u*(8*R-k)*Fu-(8*R+8-k)*Jk
        check("general_guard_elimination", sp.expand(rhs-k*(8-k)) == 0)
        good = k != 8 and all(p == 2 for p in sp.factorint(abs(k*(8-k))))
        check("guard_classification_finite_replay", good == (k in (4,16)))
    # Lagrange finite search and constructor rejection paths.
    for n in range(201):
        aa = four_squares(n)
        check("four_square_replay", sum(a*a for a in aa) == n)
        aa = weighted_four_squares(aa)
        check("weighted_four_square_replay", aa[0]**2+aa[1]**2+2*aa[2]**2+2*aa[3]**2 == n)
    for X,Y,Z in product(range(16),repeat=3):
        check("binary_guard_mod16_obstruction", (X*X+3*Y*Y+2*Z*Z) % 16 != 10)
    for X,Y,Z in product(range(8),repeat=3):
        if any(v % 2 for v in (X,Y,Z)):
            check("binary_guard_primitive_mod8_obstruction", (X*X+3*Y*Y+2*Z*Z) % 8 != 0)
    rejected(lambda: QuadraticSystem((x,), (x**3,)))
    rejected(lambda: QuadraticSystem((x,), (sp.Rational(1,2)*x,)))
    rejected(lambda: QuadraticSystem((x,), (1.5*x,)))
    rejected(lambda: QuadraticSystem((x,), (x+y,)))
    rejected(lambda: QuadraticSystem((x,x), (x,)))
    rejected(lambda: QuadraticSystem((x,), (x,), ("a","b")))
    rejected(lambda: compile_smooth(QuadraticSystem((sp.Symbol("aux_t"),), (0,))))
    rejected(lambda: four_squares(True))
    rejected(lambda: four_squares(-1))
    rejected(lambda: four_squares(10, search_limit=5))
    rejected(lambda: two_adic_residues(0, 0))
    rejected(lambda: cert.lift((0,0), sign=0))
    rejected(lambda: cert.lift((0.0,0)))
    rejected(lambda: dyadic_point(cert, (0,0,0,0)))


def save_example(name, cert, point, metadata, residues, extra=None):
    obj = cert.export()
    obj["dyadic_point"] = [str(v) for v in point]
    obj["dyadic_metadata"] = metadata
    obj["two_adic_residues"] = residues
    obj["Jacobian_certificate"] = {k: str(v) for k,v in cert.jacobian_certificate().items()}
    if extra:
        obj.update(extra)
    (ROOT/"examples"/f"{name}.json").write_text(json.dumps(obj, indent=2)+"\n")


def test_counter():
    programs = [countdown(),
                Program(2, (Instruction("inc",0,1), Instruction("dec",1,1,2), Instruction("halt")))]
    for program in programs:
        ell, r, edges = len(program.instructions), program.counters, program.edges
        pcount = sum(e.guard == "positive" for e in edges)
        gcount = sum(e.guard != "any" for e in edges)
        for initial in product(range(4), repeat=r):
            for T in range(7):
                bounded = compile_counter(program, initial, T)
                vals = bounded.system.evaluate(bounded.point)
                check("counter_initial_transition_rows", not any(vals[:-1]))
                check("counter_endpoint", (vals[-1] == 0) == bounded.accepting)
                expected_n = (ell+r)*(T+1)+(len(edges)+pcount)*T
                expected_m = ell+r+T*(1+2*ell+r+gcount)+1
                check("counter_variable_formula", len(bounded.system.variables) == expected_n)
                check("counter_residual_formula", len(bounded.system.residuals) == expected_m)
                check("counter_natural_witness", all(v >= 0 for v in bounded.point))
    # Exhaust every one-step natural assignment of the countdown machine
    # when source/target states are one-hot and counter values are <=3.
    program = countdown()
    one = compile_counter(program, (0,), 1)
    operational = sp.lambdify(one.system.variables, one.system.residuals[3:-1], "math")
    vv = one.system.variables
    edges = program.edges
    for s0,s1,c0,c1 in product(range(2),range(2),range(4),range(4)):
        for bits in product(range(2), repeat=3):
            for slack in range(4):
                values = {f"q_0_{i}": int(i == s0) for i in range(2)}
                values.update({f"q_1_{i}": int(i == s1) for i in range(2)})
                values.update({"c_0_0": c0, "c_1_0": c1, "d_0_0": slack})
                values.update({f"a_0_{i}": bits[i] for i in range(3)})
                actual = not any(operational(*(values[str(v)] for v in vv)))
                k = 2 if s0 == 1 else (0 if c0 else 1)
                expected_s1 = edges[k].target
                expected_c1 = c0+edges[k].delta
                expected = (s1 == expected_s1 and c1 == expected_c1
                            and bits == tuple(int(i == k) for i in range(3))
                            and slack == (c0-1 if k == 0 else 0))
                check("exhaustive_counter_one_step", actual == expected)
    bounded = compile_counter(countdown(), (2,), 3)
    cert = compile_smooth(bounded.system)
    check_symbolic(cert)
    lifted = cert.lift(bounded.point)
    check("countdown_accepted_lift", cert.evaluate(lifted) == 0)
    dyadic, metadata = dyadic_point(cert)
    save_example("countdown_T3", cert, dyadic, metadata, two_adic_residues(metadata["c"], 16),
                 {"input": [2], "horizon": 3, "natural_point": list(lifted),
                  "history": bounded.history, "chosen_edges": bounded.selected,
                  "source_counts": {"variables": len(bounded.system.variables),
                                    "residuals": len(bounded.system.residuals)}})
    # Test genuinely quadratic source homogenization after the finalizer.
    rejected(lambda: Program(True, (Instruction("halt"),)))
    rejected(lambda: Program(1, (Instruction("inc",0,2),Instruction("halt"))))
    rejected(lambda: Program(1, (Instruction("dec",0,0,None),Instruction("halt"))))
    rejected(lambda: Program(1, (Instruction("halt"),Instruction("halt"))))
    rejected(lambda: compile_counter(countdown(), (-1,), 2))
    rejected(lambda: compile_counter(countdown(), (0,), 1.0))
    rejected(lambda: compile_counter(countdown(), (True,), 2))


def main():
    (ROOT/"examples").mkdir(exist_ok=True)
    (ROOT/"verification").mkdir(exist_ok=True)
    test_core()
    test_counter()
    report = {"status": "PASS", "checks": dict(sorted(COUNTS.items())),
              "total_checks": sum(COUNTS.values()), "seed": 20261002,
              "python": platform.python_version(), "sympy": sp.__version__,
              "scope": "Exact symbolic identities plus finite exhaustive/seeded tests; not proof-assistant verification"}
    text = json.dumps(report, indent=2)+"\n"
    (ROOT/"verification"/"results.json").write_text(text)
    print(text)


if __name__ == "__main__":
    main()
