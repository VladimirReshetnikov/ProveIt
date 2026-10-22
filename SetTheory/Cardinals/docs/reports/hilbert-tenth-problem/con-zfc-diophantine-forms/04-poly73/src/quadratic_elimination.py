#!/usr/bin/env python3
"""Exact, standard-library affine elimination for the fixed-input system.

No arithmetic evaluation of the enormous fixed compiler numerals is needed:
they remain coefficient symbols in Z[Bm1,Kconstant,twice_cell_bits,MC,MF,W0].
Every serialized residual is a literal integer polynomial after those fixed
numerals are substituted. This verifies compilation identities, not ZFC's
consistency or existence of a complete accepting witness.
"""

from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path


HERE = Path(__file__).resolve().parent
FIXED = ("Bm1", "Kconstant", "twice_cell_bits", "MC", "MF", "W0")
WITNESSES = (
    "Jrep", "F", "alpha", "transport_quotient", "f", "h", "i",
    "auxiliary_quotient", "s", "w", "tau_root", "eta", "zeta",
    "y_aux", "Z", "gamma",
)
FINALIZER = {
    "norm_pair", "norm_triple", "norm_four", "norm_product",
    "all_units", "seven_units", "polynomial",
}
INPUT_GUARD = {"input_scaled", "norm_input"}
PIVOTS = (
    ("first_norm", "tau_square"),
    ("main_norm", "L15"),
    ("strong_norm", "L16"),
    ("auxiliary_norm", "L17"),
    ("index", "hpm1"),
    ("transport", "local_rhs"),
    ("fixed_marker", "alpha"),
)

# A polynomial maps sorted tuples of symbol names to nonzero coefficients.
# Fixed symbols count toward formal coefficient size but not unknown degree.
def clean(p):
    return {m: c for m, c in p.items() if c}


def const(n):
    return {(): n} if n else {}


def var(s):
    return {(s,): 1}


def add(a, b):
    out = dict(a)
    for m, c in b.items():
        out[m] = out.get(m, 0) + c
    return clean(out)


def scale(a, n):
    return clean({m: n*c for m, c in a.items()})


def sub(a, b):
    return add(a, scale(b, -1))


def mul(a, b):
    out = {}
    for m, c in a.items():
        for n, d in b.items():
            mn = tuple(sorted(m+n))
            out[mn] = out.get(mn, 0) + c*d
    return clean(out)


def substitute(p, symbol, replacement):
    out = {}
    for monomial, coefficient in p.items():
        term = const(coefficient)
        for factor in monomial:
            term = mul(term, replacement if factor == symbol else var(factor))
        out = add(out, term)
    return out


def unknown_degree(p):
    return max((sum(s not in FIXED for s in monomial) for monomial in p), default=0)


def coefficient_only(p):
    return all(all(s in FIXED for s in monomial) for monomial in p)


def encode(p):
    return [
        {"coefficient": c, "powers": dict(sorted(Counter(m).items()))}
        for m, c in sorted(p.items())
    ]


def expr(p):
    if not p:
        return "0"
    pieces = []
    for m, c in sorted(p.items()):
        powers = Counter(m)
        factors = [s if n == 1 else f"{s}^{n}" for s, n in sorted(powers.items())]
        body = "*".join(factors)
        body = str(abs(c)) if not body else (body if abs(c) == 1 else f"{abs(c)}*{body}")
        pieces.append(("-" if c < 0 else "+", body))
    sign, body = pieces[0]
    return ("-" if sign == "-" else "")+body+"".join(f" {sgn} {b}" for sgn, b in pieces[1:])


def ensure(condition, message):
    if not condition:
        raise RuntimeError(message)


def source_system():
    packet = json.loads((HERE.parent / "data/fixed_input_linear_guard_sources.json").read_text())
    full = packet["source74"]
    source = [row for row in full if row[0] not in FINALIZER | INPUT_GUARD]
    ensure(len(source) == 65, "Wrong complete comparison-system length")
    ensure(sum(row[1] == "*" for row in source) == 35, "Wrong multiplication count")
    available = set(WITNESSES) | set(FIXED)
    for name, op, a, b in source:
        ensure(name not in available, f"Duplicate gate {name}")
        ensure(op in {"+", "-", "*"}, "Unexpected primitive")
        ensure(all(type(x) is int or x in available for x in (a,b)), f"Unavailable input at {name}")
        available.add(name)
    # The sign relaxation is exact because each root occurs only in its square.
    for root, square in (("tau_root", "tau_square"), ("y_aux", "aux_y2")):
        uses = [row for row in source if root in row[2:]]
        ensure(uses == [[square, "*", root, root]], f"Root {root} has a nonsquare use")
    return source


def build(signed_roots=True):
    source = source_system()
    env = {s: var(s) for s in WITNESSES + FIXED}
    nonlinear = []
    affine_multiplications = []
    multiplication_equations = []
    for name, op, a, b in source:
        aa = const(a) if type(a) is int else env[a]
        bb = const(b) if type(b) is int else env[b]
        if op == "+":
            env[name] = add(aa, bb)
        elif op == "-":
            env[name] = sub(aa, bb)
        elif coefficient_only(aa) or coefficient_only(bb):
            env[name] = mul(aa, bb)
            affine_multiplications.append(name)
        else:
            nonlinear.append(name)
            multiplication_equations.append((name, sub(var(name), mul(aa, bb))))
            env[name] = var(name)
        ensure(unknown_degree(env[name]) <= 1, f"Nonaffine inline expression {name}")
    ensure(len(nonlinear) == 32, "Expected exactly 32 nonlinear products")
    ensure(affine_multiplications == ["repunit", "a4", "qMF"], "Wrong affine-product census")

    comparisons = [
        ("first_norm", sub(env["norm_first"], const(1))),
        ("main_norm", sub(env["norm_main"], const(1))),
        ("strong_norm", sub(env["norm_strong"], const(1))),
        ("auxiliary_norm", sub(env["norm_aux"], const(1))),
        ("index", sub(env["norm_index"], const(1))),
        ("transport", sub(env["norm_transport"], const(1))),
        ("fixed_marker", sub(env["W"], var("W0"))),
    ]
    ensure(all(unknown_degree(p) == 1 for _, p in comparisons), "A final comparison is not affine")
    original_equations = list(multiplication_equations)
    original_comparisons = list(comparisons)
    eliminations = []

    for comp_name, pivot in PIVOTS:
        p = dict(comparisons)[comp_name]
        coefficient = p.get((pivot,), 0)
        ensure(coefficient in (1, -1), f"Pivot {pivot} is not an integer-unit coefficient")
        ensure(all(pivot not in m or m == (pivot,) for m in p), f"Pivot {pivot} occurs in its coefficient")
        remainder = sub(p, scale(var(pivot), coefficient))
        replacement = scale(remainder, -coefficient)
        ensure(unknown_degree(replacement) <= 1, "Nonaffine pivot replacement")
        ensure(substitute(p, pivot, replacement) == {}, "Solved comparison is not an identity")
        eliminations.append((pivot, replacement))
        multiplication_equations = [(name, substitute(eq, pivot, replacement)) for name, eq in multiplication_equations]
        comparisons = [(name, substitute(eq, pivot, replacement)) for name, eq in comparisons]
        env = {name: substitute(eq, pivot, replacement) for name, eq in env.items()}

    ensure(all(not p for _, p in comparisons), "A final comparison survived")
    eliminated = {s for s, _ in eliminations}
    ensure(eliminated == {"tau_square", "L15", "L16", "L17", "hpm1", "local_rhs", "alpha"}, "Pivot census mismatch")
    # Independently compose all substitutions on each pre-elimination equation.
    for (name, old), (name2, new) in zip(original_equations, multiplication_equations):
        for symbol, replacement in eliminations:
            old = substitute(old, symbol, replacement)
        ensure(name == name2 and old == new, "Full equation substitution mismatch")
    for _, old in original_comparisons:
        for symbol, replacement in eliminations:
            old = substitute(old, symbol, replacement)
        ensure(not old, "Original comparison not identically restored")

    positive = [s for s in WITNESSES if not (signed_roots and s in {"tau_root", "y_aux"})]
    parameters = [f"pos_{s}_{j}" for s in positive for j in (1,2,3)]
    base_variables = [s for s in WITNESSES if s not in eliminated]
    product_variables = [s for s in nonlinear if s not in eliminated]
    variables = base_variables + product_variables + parameters
    equations = list(multiplication_equations)
    for s in positive:
        # A positive integer v is characterized by 4v-3 = a sum of three squares.
        lhs = sub(scale(env[s], 4), const(3))
        for j in (1,2,3):
            z = var(f"pos_{s}_{j}")
            lhs = sub(lhs, mul(z,z))
        equations.append((f"positive_{s}", lhs))

    ensure(len(variables) == (83 if signed_roots else 89), "Unexpected variable count")
    ensure(len(equations) == (46 if signed_roots else 48), "Unexpected equation count")
    ensure(len(set(variables)) == len(variables), "Duplicate variable")
    allowed = set(variables) | set(FIXED)
    ensure(all(s in allowed for _, p in equations for m in p for s in m), "Unlisted symbol")
    ensure(all(unknown_degree(p) <= 2 for _, p in equations), "Nonquadratic equation")
    ensure(set(variables) == {s for _, p in equations for m in p for s in m if s not in FIXED}, "Unused variable")

    # Expand the actual quartic over the coefficient ring to verify its degree.
    quartic = {}
    for _, residual in equations:
        quartic = add(quartic, mul(residual, residual))
    ensure(unknown_degree(quartic) == 4, "SOS is not a quartic")
    # pos_Jrep_1 appears only squared in its domain equation, so coefficient 1
    # of its fourth power proves exact degree for every fixed compiler slice.
    pure_fourth = ("pos_Jrep_1",) * 4
    ensure(quartic.get(pure_fourth) == 1, "Uniform quartic leading coefficient lost")

    result = {
        "schema": "fixed-input-quadratic-system-v1",
        "fixed_coefficient_symbols": list(FIXED),
        "domains": "All listed variables are unrestricted integers.",
        "signed_roots": ["tau_root", "y_aux"] if signed_roots else [],
        "source_ledger": {"operations":65, "multiplications":35, "additions_subtractions":30},
        "affine_product_rows": affine_multiplications,
        "nonlinear_product_rows_before_elimination": nonlinear,
        "variables": variables,
        "variable_count": len(variables),
        "equation_count": len(equations),
        "max_degree": 2,
        "single_equation": "sum(residual_j^2)=0",
        "single_equation_degree": 4,
        "uniform_degree_witness": {"monomial": {"pos_Jrep_1":4}, "coefficient":1},
        "equations": [{"name":name, "residual":encode(p), "text":expr(p)} for name,p in equations],
        "eliminations": [{"variable":s, "replacement":encode(p), "text":expr(p)} for s,p in eliminations],
        "restoration": {s:encode(env[s]) for s in WITNESSES},
        "proof_obligations": [
            "The mathematical polynomial/Pell proof establishes equivalence of the 65-gate seven-comparison system with fixed-program acceptance.",
            "Affine inlining is literal polynomial substitution; each deleted comparison solves a variable with coefficient +1 or -1.",
            "For integers v, v>=1 iff 4v-3 is a sum of three integer squares (Legendre's three-square theorem).",
            "tau_root and y_aux occur only squared. At a system zero neither is zero, so absolute values restore positive roots.",
            "Over the integers a sum of squares vanishes iff every squared residual vanishes.",
        ],
        "checks": {
            "topological_source": True,
            "complete_comparison_identities":7,
            "complete_product_equation_substitutions":32,
            "all_variables_live":True,
            "exact_quartic_degree":True,
            "fixed_coefficients_not_materialized":True,
            "kernel_formalization":False,
        },
    }
    digest = hashlib.sha256(json.dumps(result, sort_keys=True,separators=(",", ":")).encode()).hexdigest()
    result["canonical_sha256_without_this_field"] = digest
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    parser.add_argument("--expect", type=Path)
    parser.add_argument("--all-positive", action="store_true")
    args = parser.parse_args()
    result = build(signed_roots=not args.all_positive)
    if args.expect:
        ensure(json.loads(args.expect.read_text()) == result, "Receipt does not match exact fresh result")
    if args.output:
        args.output.write_text(json.dumps(result, indent=2,sort_keys=True)+"\n")
    print(json.dumps({key:result[key] for key in ("variable_count","equation_count","single_equation_degree","canonical_sha256_without_this_field")},sort_keys=True))


if __name__ == "__main__":
    main()
