#!/usr/bin/env python3
"""Independent exact reconstruction of the four new integer forms.

Uses only the Python standard library and no author/build polynomial code.
Sparse monomials are sorted strings repeated by exponent. All public source
rows are parsed through a small AST reader; no Python evaluation is used.
"""
import ast
from collections import Counter
from hashlib import sha256
import json
from math import isqrt
from pathlib import Path
import sys


HERE = Path(__file__).resolve().parent
WORK = HERE.parent.parent
ROOT = WORK / "ProveIt/Computability/DiophantineConsistency/con-zfc-diophantine-forms"
if len(sys.argv) > 1:
    ARTIFACT = Path(sys.argv[1]).resolve()
elif (HERE.parent / "forms").is_dir():
    ARTIFACT = HERE.parent.parent
else:
    ARTIFACT = WORK / "deliverable/con-zfc-cross-guard-descent-2026-10-23"
SOURCE = ARTIFACT / "integer/upstream/quartic41.json"
PIN = "2605669a532342f153b13eb6b4a0af4b54f5fa37"


def require(condition, text):
    if not condition:
        raise AssertionError(text)


def clean(p):
    return {m: c for m, c in p.items() if c}


def add(p, q, factor=1):
    out = dict(p)
    for m, c in q.items():
        out[m] = out.get(m, 0) + factor * c
    return clean(out)


def multiply(p, q):
    out = Counter()
    for m, a in p.items():
        for n, b in q.items():
            out[tuple(sorted(m + n))] += a * b
    return clean(out)


def power(p, n):
    out = {(): 1}
    for _ in range(n):
        out = multiply(out, p)
    return out


def read_poly(text):
    def go(n):
        if isinstance(n, ast.Constant) and type(n.value) is int:
            return clean({(): n.value})
        if isinstance(n, ast.Name):
            return {(n.id,): 1}
        if isinstance(n, ast.UnaryOp) and isinstance(n.op, ast.USub):
            return {m: -c for m, c in go(n.operand).items()}
        if isinstance(n, ast.BinOp):
            if isinstance(n.op, ast.Pow):
                require(isinstance(n.right, ast.Constant) and type(n.right.value) is int
                        and n.right.value >= 0, "nonconstant power")
                return power(go(n.left), n.right.value)
            if isinstance(n.op, ast.Add):
                return add(go(n.left), go(n.right))
            if isinstance(n.op, ast.Sub):
                return add(go(n.left), go(n.right), -1)
            if isinstance(n.op, ast.Mult):
                return multiply(go(n.left), go(n.right))
        raise ValueError(ast.dump(n))
    return go(ast.parse(text, mode="eval").body)


def substitute(poly, replacements):
    out = {}
    for m, c in poly.items():
        term = {(): c}
        for name in m:
            term = multiply(term, replacements.get(name, {(name,): 1}))
        out = add(out, term)
    return out


def symbols(poly):
    return set().union(*(set(m) for m in poly)) if poly else set()


def degree(poly, variables):
    return max((sum(s in variables for s in m) for m in poly), default=-1)


def fixed_coefficient(poly, monomial, variables):
    wanted = tuple(sorted(monomial))
    out = {}
    for m, c in poly.items():
        if tuple(n for n in m if n in variables) == wanted:
            fixed = tuple(n for n in m if n not in variables)
            out[fixed] = out.get(fixed, 0) + c
    return clean(out)


def build_parent(source, signed, paired=True, reduced=False):
    rows = [read_poly(r) for r in source["residuals"]]
    if signed:
        rows[13] = read_poly("(K0*(beta*J+1)+X)*(beta*J+1-F-alpha)-(beta*J+1)*F-Z*beta*J")
        rows[22] = read_poly("X-4*(beta*J+1)*u**2")
    if reduced:
        # Independent polynomial row operation, before ANY monic substitution.
        rows[21] = add(rows[21], multiply(read_poly("g"), rows[20]))
    selected = [(i, p) for i, p in enumerate(rows)
                if (i < 23 or (not paired and i == 25)) and not (signed and i == 2)]
    G = read_poly("cone_A*F*cone_B*(beta*J+1-F-alpha)-(beta*J+1-cone_A*F-cone_B*(beta*J+1-F-alpha))**2")
    H = read_poly("eta*zeta")
    inner = add(add(add(read_poly("t**2"), G, -1), H, -1), {(): 1})
    if paired:
        guard = add(add(multiply(G, H), power(inner, 2), -1), read_poly("1+p1**2+p2**2+p3*(p3+1)"), -1)
        selected.append(("joint_guard", guard))
    else:
        selected.append(("determinant_guard", add(G, read_poly("1+p1**2+p2**2+p3*(p3+1)"), -1)))
    return selected


def restoration(signed, reduced=False, sextic=False):
    values = {}
    if sextic:
        recipes = [("P", "eta+zeta+E*(c-eta)"),
                   ("tau", "tau_tail+P-eta-zeta"),
                   ("F2", "f**2"), ("g", "y**2-V**2"),
                   ("N", "(beta*J+1)*(L+1)"), ("C2", "c**2"),
                   ("X", "D-a*c-gamma*(4*a+3)")]
        for name, text in recipes:
            values[name] = substitute(read_poly(text), values)
        return values
    if reduced:
        values["I"] = read_poly("(2*r+1)*c**2")
        values["y"] = read_poly("f*o-c+y_tail")
    recipes = [
        ("L", "(beta*J+1)**2-1"), ("N", "(beta*J+1)**3"),
        ("C2", "c**2"), ("F2", "f**2"), ("Baux", "I**2"),
        ("Delta", "a**2+4*a+3"),
    ]
    if signed:
        recipes.extend([("V", "f*o-c"), ("zeta", "1-V+j*c+h*E-eta"),
                        ("X", "4*(beta*J+1)*u**2")])
    else:
        recipes.append(("X", "2*u**2"))
    recipes.extend([("g", "y**2-V**2"), ("D", "X+a*c+gamma*(4*a+3)"),
                    ("P", "eta+zeta+E*(c-eta)")])
    for name, text in recipes:
        values[name] = substitute(read_poly(text), values)
    return values


def audit(source, name, signed, count, d, witness, witness_coefficient=1,
          reduced=False, sextic=False):
    candidate_path = ARTIFACT / "integer/forms" / (name + ".json")
    candidate = json.loads(candidate_path.read_text())
    variables = set(candidate["variables"])
    require(len(variables) == count == len(candidate["variables"]), "variable count " + name)
    restore = restoration(signed, reduced=reduced, sextic=sextic)
    surviving = []
    zero_rows = []
    for index, p in build_parent(source, signed, paired=not sextic, reduced=reduced):
        q = substitute(p, restore)
        if q:
            surviving.append((index, q))
        else:
            zero_rows.append(index)
    actual = [read_poly(r) for r in candidate["residuals"]]
    require(len(surviving) == len(actual), "residual count " + name)
    for (index, expected), delivered in zip(surviving, actual):
        require(expected == delivered, "independent restored row " + name + " index " + str(index))
    require(set(restore).isdisjoint(variables), "eliminated or renamed variables remain")
    all_symbols = set().union(*(symbols(p) for p in actual))
    ports = set(source["fixed_numerals"]) | {"cone_A", "cone_B"}
    require(all_symbols - ports == variables, "live variables " + name)
    residual_degrees = [degree(p, variables) for p in actual]
    require(2 * max(residual_degrees) == d, "degree upper bound " + name)
    sos = {}
    for p in actual:
        sos = add(sos, power(p, 2))
    coefficient = fixed_coefficient(sos, witness, variables)
    require(coefficient == {(): witness_coefficient}, "fixed-slice exact degree witness " + name)
    return {
        "file": str(candidate_path.relative_to(ARTIFACT)),
        "sha256": sha256(candidate_path.read_bytes()).hexdigest(),
        "variables": count, "residuals": len(actual), "exact_degree": d,
        "residual_degrees": residual_degrees,
        "all_restored_rows_equal": True, "zero_definition_rows": zero_rows,
        "surviving_parent_rows": [i for i, _ in surviving],
        "exact_degree_monomial": dict(Counter(witness)),
        "exact_degree_monomial_coefficient": witness_coefficient,
        "symbolic_sos_terms": len(sos),
    }


def finite_guard_checks():
    sound = complete = 0
    for a in range(-25, 26):
        for b in range(-25, 26):
            for t in range(-12, 13):
                value = a*b-(t*t-a-b+1)**2
                if value > 0:
                    require(a > 0 and b > 0, "joint guard sign")
                sound += 1
    for a in range(1, 151):
        for b in range(1, 151):
            n = a + b - 1
            t = isqrt(n)
            if n-t*t > t:
                t += 1
            require(a*b-(t*t-a-b+1)**2 > 0, "nearest-square witness")
            complete += 1
    return {"signed_triples": sound, "positive_pairs": complete}


def main():
    source = json.loads(SOURCE.read_text())
    require(sha256(SOURCE.read_bytes()).hexdigest() ==
            "a1b5d9bacff52bd864695bd89646cb81eabdee1685b5ebc0348f594f40f4ff82",
            "source pin")
    output = {"status": "pass", "pin": PIN,
              "source_sha256": sha256(SOURCE.read_bytes()).hexdigest(),
              "independence": "does not import the construction or its polynomial engine",
              "forms": [
                  audit(source, "degree12_23", True, 23, 12, ["eta"]*4+["f"]*4+["o"]*4),
                  audit(source, "octic26", False, 26, 8, ["t"]*8),
                  audit(source, "degree14_22", True, 22, 14,
                        ["a"]*4+["f"]*6+["o"]*2+["y_tail"]*2,
                        witness_coefficient=4, reduced=True),
                  audit(source, "sextic31", True, 31, 6,
                        ["r"]*2+["c"]*4, witness_coefficient=4, sextic=True),
              ],
              "finite_guard_checks": finite_guard_checks(),
              "scope": "exact algebra and ordinary-proof review; inherited native/Pell calibration not kernel-reproved"}
    # A local all-input transport identity, independent of solving the system.
    cleared = read_poly("(K0*(beta*J+1)+X)*(beta*J+1-F-alpha)-(beta*J+1)*F-(beta*J+1)*z*beta*J")
    old_scaled = read_poly("(beta*J+1)*((K0+4*u**2)*(beta*J+1-F-alpha)-F-z*beta*J)")
    correction = read_poly("(X-4*(beta*J+1)*u**2)*(beta*J+1-F-alpha)")
    require(add(cleared, old_scaled, -1) == correction, "cleared transport identity")
    output["transport_identity"] = "new(Z=qz)-q*old(w=u^2)=(X-4qu^2)*C"
    original_aux = read_poly("y**2-I**2*(y**2-V**2)-1")
    new_aux = read_poly("y**2-(a**2+4*a+3)*(f**2-1)*(y**2-V**2)-1")
    strong_multiple = read_poly("(I**2-(a**2+4*a+3)*(f**2-1))*(y**2-V**2)")
    require(add(new_aux, original_aux, -1) == strong_multiple, "invertible row identity")
    output["row_operation_identity"] = "new_aux=old_aux+strong*(y^2-V^2)"
    output["root_centering"] = "y_old=V+y_tail; y_tail=y_old-V; both maps are integer polynomials"
    (HERE / "INDEPENDENT_CHECKS.json").write_text(json.dumps(output, indent=2)+"\n")
    print(json.dumps(output, indent=2))


if __name__ == "__main__":
    main()
