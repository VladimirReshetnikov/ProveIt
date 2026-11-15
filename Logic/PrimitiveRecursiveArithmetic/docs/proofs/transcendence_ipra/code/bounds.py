#!/usr/bin/env python3
"""Executable specifications of the paper's primitive recursive bounds.

Structural polynomial/matrix data are computed exactly. The subsequent
arithmetic is returned as a finite straight-line expression graph, rather
than attempting to materialize its enormous factorials.

This is a specification and demonstration, not an iPRA proof checker.
Dependency: SymPy, plus matrix_checks.py from this archive.
"""
from __future__ import annotations
import argparse
import json
from math import factorial
from pathlib import Path
import sympy as sp
from matrix_checks import X, companion, exterior_sum, zero_factor

def ref(name):
    return {"ref": name}

def op(kind, *args):
    return {"op": kind, "args": list(args)}

class Program:
    def __init__(self, values):
        self.initial_values = values
        self.steps = []

    def put(self, name, expression):
        self.steps.append({"name": name, "expression": expression})
        return ref(name)

    def result(self, **metadata):
        return {**metadata, "initial_values": self.initial_values,
                "steps": self.steps,
                "outputs": ["B", "N", "direct_threshold"],
                "operation_semantics": {
                    "add": "sum of arguments",
                    "mul": "product of arguments",
                    "pow": "natural exponentiation",
                    "factorial": "natural factorial",
                    "sub": "natural subtraction (all used differences nonnegative)",
                    "max": "maximum of finite argument list"},
                "status": "exact bound specification; large outputs not evaluated"}

def normalized(coefficients):
    a = [int(x) for x in coefficients]
    while a and a[-1] == 0:
        a.pop()
    if not a:
        return a, 0, a
    v = next(j for j, value in enumerate(a) if value)
    return a, v, a[v:]

def lip(a):
    return 1 + sum(j * abs(a[j]) * 4**(j-1) for j in range(1, len(a)))

def trivial(a, v, core, constant):
    p = Program({"lambda": lip(a)})
    p.put("B", 1)
    p.put("N", op("add", op("mul", 4, ref("lambda")), 1))
    p.put("direct_threshold", 0)
    return p.result(constant=constant, coefficients=a, stripped_power=v,
                    core=core, zero_polynomial=not a,
                    note="Monomial/zero branch; zero input is vacuous.")

def e_bound(coefficients):
    a, v, core = normalized(coefficients)
    if len(core) < 2:
        return trivial(a, v, core, "e")
    n = len(core)-1
    prog = Program({"n": n, "S": sum(abs(x) for x in core),
                    "M": abs(core[0])*factorial(n), "lambda": lip(a)})
    n, S, M = ref("n"), ref("S"), ref("M")
    R = prog.put("R", op("pow", op("mul", 2, n), op("add", n, 1)))
    A = prog.put("A", op("mul", n, op("pow", 3, op("mul", 2, n)), S))
    L = prog.put("L", op("add", op("mul", 4, op("pow", R, 2)),
                             op("mul", 4, A, R), 1))
    q = prog.put("q", op("mul", M, L))
    p = prog.put("p", op("add", op("mul", 2, q), 1))
    ell = prog.put("ell", op("sub", op("mul", op("add", n, 1), p), 1))
    D = prog.put("D", op("mul", op("factorial", ell),
                        op("pow", op("factorial", op("add", n, 1)), p)))
    B = prog.put("B", op("mul", 2, D))
    prog.put("N", op("add", op("mul", 4, B, ref("lambda")), 1))
    HF = prog.put("H_F", op("mul", op("add", ell, 1), D, op("pow", n, ell)))
    W = prog.put("W", op("mul", S, n, op("add", HF, op("mul", 2, D))))
    R1 = prog.put("R_1", op("mul", 2, n))
    t0 = prog.put("t_0", op("add", op("mul", 4, op("pow", R1, 2)),
                                op("mul", 4, W), 1))
    prog.put("direct_threshold", op("mul", 2, t0))
    return prog.result(constant="e", coefficients=a, stripped_power=v, core=core,
                       equation_references=["4.1", "4.8", "4.11", "1.5"],
                       name="e_s = sum_(j=0)^(s+1) 1/j!")

def pi_bound(coefficients):
    a, v, core = normalized(coefficients)
    if len(core) < 2:
        return trivial(a, v, core, "pi")
    P = sum(sp.Integer(value)*X**j for j, value in enumerate(core))
    qpoly = sp.Poly(sp.expand(P.subs(X, -sp.I*X)*P.subs(X, sp.I*X)), X)
    n, c = qpoly.degree(), int(qpoly.LC())
    assert c > 0 and all(value.is_Integer for value in qpoly.all_coeffs())
    Amat = companion(sp.Poly(qpoly.as_expr()/c, X))
    Bmat = exterior_sum(Amat)
    Mmat = c*Bmat
    chi = sp.Poly(Mmat.charpoly(X).as_expr(), X)
    m, G = zero_factor(chi)
    assert m >= 1 and G.nth(0) != 0
    r = G.degree()
    L = max(1, sum(abs(int(qpoly.nth(j))) for j in range(n)))
    values = {
        "n": int(n), "c": c, "L": L, "D_0": 2**n,
        "m": int(m), "r": int(r),
        "H_G": sum(abs(int(x)) for x in G.all_coeffs()),
        "abs_G_0": abs(int(G.nth(0))),
        "H": sum(abs(x)*4**j for j, x in enumerate(core)),
        "lambda": lip(a)
    }
    prog = Program(values)
    n,c,L,D0,m,r,HG,g0,H = (ref(name) for name in
                             ("n","c","L","D_0","m","r","H_G","abs_G_0","H"))
    b = prog.put("b", op("mul", n, L))
    V = prog.put("V", op("mul", c, b))
    R = prog.put("R", op("mul", HG, op("pow", V, op("add", r, 1))))
    A0 = prog.put("A_0", op("mul", D0, b, op("pow", 3, b)))
    M0 = prog.put("M_0", op("mul", m, c, g0))
    L0 = prog.put("L_0", op("add", op("mul", 4, op("pow", R, 2)),
                                 op("mul", 4, A0, R), 1))
    q0 = prog.put("q_0", op("mul", M0, L0))
    p = prog.put("p", op("add", op("mul", 2, q0), 1))
    ell = prog.put("ell", op("sub", op("mul", op("add", r, 1), p), 1))
    U = prog.put("U", op("mul", op("factorial", ell),
                        op("pow", c, ell), op("pow", HG, p)))
    T0 = prog.put("T_0", op("add", 1, op("pow", 3, L)))
    Kadj = prog.put("K_adj", op("mul", op("factorial", n),
                               op("pow", T0, op("sub", n, 1))))
    K = prog.put("K", op("mul", Kadj, op("pow", 3, op("add", L, 4))))
    B = prog.put("B", op("mul", 2, U, K, H))
    prog.put("N", op("add", op("mul", 4, B, ref("lambda")), 1))
    VF = prog.put("V_F", op("mul", op("add", ell, 1), U, op("pow", b, ell)))
    kH = prog.put("k_H", op("add", op("mul", 16, D0, b, VF), 1))
    kE = prog.put("k_E", op("add", op("mul", 16, U, Kadj,
                                    op("pow", 4, op("sub", n, 1))), 1))
    prog.put("direct_threshold", op("add", kE, 30))
    Cext = prog.put("C_ext", op("mul", op("factorial", n),
                              op("pow", op("add", 1,
                                  op("pow", 3, op("mul", 2, L))), n)))
    hH = prog.put("h_H", op("add", op("mul", 4,
                                op("pow", op("add", b, 1), 2)), kH, 4))
    hExt = prog.put("h_ext", op("add", op("mul", 16, U, Cext), 1))
    hEuler = prog.put("h_Euler", op("add", 4*5**2, kE, 30, 4))
    prog.put("h", op("max", hH, hExt, hEuler))
    return prog.result(
        constant="pi", coefficients=a, stripped_power=v, core=core,
        transformed_polynomial_low_to_high=[int(qpoly.nth(j)) for j in range(values["n"]+1)],
        characteristic_polynomial=str(chi.as_expr()),
        nonzero_factor_low_to_high=[int(G.nth(j)) for j in range(values["r"]+1)],
        equation_references=["6.1", "7.3", "7.7", "7.9", "7.10", "1.5"],
        name="pi_s = 16*A_s(1/5) - 4*A_s(1/239)")

def validate_graph(data):
    known = set(data["initial_values"])
    def check(expr):
        if isinstance(expr, int):
            assert expr >= 0
        elif "ref" in expr:
            assert expr["ref"] in known
        else:
            assert expr["op"] in data["operation_semantics"]
            for item in expr["args"]:
                check(item)
    for step in data["steps"]:
        assert step["name"] not in known
        check(step["expression"])
        known.add(step["name"])
    assert set(data["outputs"]) <= known

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--coeffs", default="-3,1",
                        help="comma-separated integer coefficients, lowest degree first")
    parser.add_argument("--constant", choices=["e", "pi", "both"], default="both")
    parser.add_argument("--output", help="optional JSON output path")
    args = parser.parse_args()
    coefficients = [int(x.strip()) for x in args.coeffs.split(",")]
    out = {}
    if args.constant in ("e", "both"):
        out["e"] = e_bound(coefficients)
    if args.constant in ("pi", "both"):
        out["pi"] = pi_bound(coefficients)
    for data in out.values():
        validate_graph(data)
    content = json.dumps(out, indent=2)
    if args.output:
        Path(args.output).write_text(content+"\n")
        print(json.dumps({"status": "bound graphs created and references validated",
                          "file": args.output, "coefficients": coefficients,
                          "large_bound_integers_evaluated": False}))
    else:
        print(content)

if __name__ == "__main__":
    main()

