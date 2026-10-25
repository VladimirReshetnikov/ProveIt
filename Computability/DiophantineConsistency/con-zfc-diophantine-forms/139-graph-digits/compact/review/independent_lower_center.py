#!/usr/bin/env python3
"""Independent literal and algebra audit for the 87/323 and 88/318 centers.

No producer, constructor, or primary checker is imported.  Arguments are
the retained parent85 circuit and the new lower-center circuit.
"""
import argparse
import gzip
import hashlib
import json
from collections import Counter
from pathlib import Path


def need(truth, message):
    if not truth:
        raise ValueError(message)


def atom(name):
    return {(name,): 1}


def integer(n):
    return {(): n} if n else {}


def add(a, b, sign=1):
    answer = dict(a)
    for key, value in b.items():
        value = answer.get(key, 0) + sign * value
        if value:
            answer[key] = value
        else:
            answer.pop(key, None)
    return answer


def mul(a, b):
    answer = {}
    for ka, va in a.items():
        for kb, vb in b.items():
            key = tuple(sorted(ka + kb))
            value = answer.get(key, 0) + va * vb
            if value:
                answer[key] = value
            else:
                answer.pop(key, None)
    return answer


def power(a, n):
    answer = integer(1)
    for _ in range(n):
        answer = mul(answer, a)
    return answer


def monomial(coefficient, **powers):
    return {tuple(sorted(name for name, exponent in powers.items()
                         for _ in range(exponent))): coefficient}


def audit_dag(data):
    known = set(data["witnesses"] + data["fixed_numerals"])
    need(len(known) == len(data["witnesses"]) + len(data["fixed_numerals"]),
         "duplicate input leaves")
    rows = {}
    degrees = {name: 1 for name in data["witnesses"]}
    degrees.update({name: 0 for name in data["fixed_numerals"]})
    operations = Counter()
    for name, operation, left, right in data["source"]:
        need(name not in known and operation in ("+", "-", "*"), "invalid gate")
        for value in (left, right):
            need(type(value) is int or (isinstance(value, str) and value in known),
                 "gate uses an unknown input")
        dl = 0 if type(left) is int else degrees[left]
        dr = 0 if type(right) is int else degrees[right]
        degrees[name] = dl + dr if operation == "*" else max(dl, dr)
        rows[name] = [name, operation, left, right]
        known.add(name)
        operations[operation] += 1
    need(data["output"] in rows, "missing output gate")
    needed = {data["output"]}
    for name, operation, left, right in reversed(data["source"]):
        if name in needed:
            needed.update(v for v in (left, right) if isinstance(v, str))
    need(needed == known, "dead gates or unused input leaves")
    need(len(rows) == data["operations"], "incorrect gate count")
    need(dict(operations) == data["operation_breakdown"], "incorrect operation breakdown")
    return rows, degrees, operations


def substitute_symbols(poly, replacements):
    result = {}
    for monomial_, coefficient in poly.items():
        term = integer(coefficient)
        for symbol in monomial_:
            term = mul(term, replacements.get(symbol, atom(symbol)))
        result = add(result, term)
    return result


def leading_prefix(data, degrees, targets):
    """Top components at the gate degree bounds, propagated independently."""
    rows = {row[0]: row for row in data["source"]}
    required = set(targets)
    for name, operation, left, right in reversed(data["source"]):
        if name in required:
            required.update(v for v in (left, right) if isinstance(v, str))
    tops = {name: atom(name) for name in data["witnesses"] + data["fixed_numerals"]}
    for name, operation, left, right in data["source"]:
        if name not in required:
            continue
        la = integer(left) if type(left) is int else tops[left]
        ra = integer(right) if type(right) is int else tops[right]
        dl = 0 if type(left) is int else degrees[left]
        dr = 0 if type(right) is int else degrees[right]
        if operation == "*":
            tops[name] = mul(la, ra)
        else:
            top_degree = max(dl, dr)
            tops[name] = add(la if dl == top_degree else {},
                             ra if dr == top_degree else {},
                             -1 if operation == "-" else 1)
    return {name: tops[name] for name in targets}


def verify(parent, new):
    old_rows, old_degrees, _ = audit_dag(parent)
    rows, degrees, operations = audit_dag(new)
    sharp = "d0" in rows
    operation_count = 88 if sharp else 87
    exact_degree = 318 if sharp else 323
    need(new["domain"] == parent["domain"] == "strictly positive integers", "domain changed")
    for key in ("witnesses", "fixed_numerals", "output"):
        need(new[key] == parent[key], "the coherent parent interface changed: " + key)
    need(new["coefficient_binding"]["tuple"] == parent["coefficient_binding"]["tuple"],
         "coefficient tuple identification changed")
    for port in parent["fixed_numerals"]:
        for key in ("bits", "raw_sha256"):
            need(new["coefficient_binding"]["ports"][port][key]
                 == parent["coefficient_binding"]["ports"][port][key],
                 "the actual fixed integer changed: " + port)
    need(len(new["witnesses"]) == 10, "wrong number of unknowns")
    need(set(old_rows) - set(rows) == {"L", "LBt"}, "unexpected deleted gate")
    extra = {"d", "bB", "dmbB", "Vcenter"} | ({"d0"} if sharp else set())
    need(set(rows) - set(old_rows) == extra,
         "unexpected new gate")
    expected = {
        "d": ["d", "+", "d0", "UE"] if sharp else ["d", "*", "Am1", "UE"],
        "bB": ["bB", "*", "cTR", "Bt"],
        "dmbB": ["dmbB", "-", "d", "bB"],
        "Vcenter": ["Vcenter", "*", "V", "dmbB"],
        "center": ["center", "+", "n", "Vcenter"],
    }
    if sharp:
        expected["d0"] = ["d0", "*", "Am1", "UE"]
    for name, row in expected.items():
        need(rows[name] == row, "wrong carrier gate " + name)
    need(old_rows["L"] == ["L", "*", "cTR", "V"]
         and old_rows["LBt"] == ["LBt", "*", "L", "Bt"]
         and old_rows["center"] == ["center", "-", "n", "LBt"],
         "retained baseline does not have the stated carrier")
    for name in set(rows) & set(old_rows) - {"center"}:
        need(rows[name] == old_rows[name], "unintended prefix/suffix change: " + name)
    need([row[0] for row in parent["source"] if "n" in row[2:]] == ["center"],
         "parent depends on carrier coordinate elsewhere")
    need([row[0] for row in new["source"] if "n" in row[2:]] == ["center"],
         "new equation depends on carrier coordinate elsewhere")
    need(new["operations"] == operation_count
         and dict(operations) == {"*": 52, "+": 21 if sharp else 20, "-": 15},
         "claimed operation count is false")

    # Free-polynomial identity for the carrier shear.
    n, d, V, b, B = map(atom, ("n", "d", "V", "b", "B"))
    new_center = add(n, mul(V, add(d, mul(b, B), -1)))
    old_sheared_center = add(add(n, mul(d, V)), mul(mul(b, V), B), -1)
    need(new_center == old_sheared_center, "carrier shear identity failed")

    # Check the exact radicand defect, writing S=A-1.
    S, U, E = map(atom, ("S", "U", "E"))
    delta = mul(S, add(S, integer(2)))
    G = mul(E, add(integer(1), mul(delta, mul(power(U, 2), E))))
    d_poly = mul(add(S, integer(1)) if sharp else S, mul(U, E))
    defect = add(G, power(d_poly, 2), -1)
    expected_defect = (add(E, mul(power(U, 2), power(E, 2)), -1) if sharp else
                      add(E, mul(integer(2), mul(S, mul(power(U, 2), power(E, 2))))))
    need(defect == expected_defect,
         "radicand defect identity failed")

    # Check the cancellation which gives the global degree upper bound.
    Q, M, G, V, d, Z0 = map(atom, ("Q", "M", "G", "V", "d", "Z0"))
    Z = add(mul(M, mul(d, V)), Z0)
    output = add(mul(add(Q, integer(1), -1), power(Z, 2)),
                 mul(power(M, 2), mul(G, add(mul(Q, power(V, 2)), integer(1), -1))), -1)
    first = mul(integer(-1), mul(power(M, 2), mul(
        add(mul(Q, add(G, power(d, 2), -1)), power(d, 2)), power(V, 2))))
    second = mul(integer(2), mul(add(Q, integer(1), -1), mul(M, mul(d, mul(V, Z0)))))
    third = mul(add(Q, integer(1), -1), power(Z0, 2))
    fourth = mul(power(M, 2), G)
    need(output == add(add(add(first, second), third), fourth),
         "degree-cancellation identity failed")
    expected_degrees = {"Q": 86, "Mtot": 13, "Dg": 56, "V": 80, "d": 28,
                        "Am1": 5, "U": 5, "Dtau": 18}
    need(all(degrees[key] == value for key, value in expected_degrees.items()),
         "prefix degree upper bounds differ from the proof")
    need(old_degrees["Znum"] == 99, "wrong uncentered numerator bound")
    defect_degree = max(18, (0 if sharp else 5) + 2*5 + 2*18)
    term_bounds = [2*13 + max(86 + defect_degree, 2*28) + 2*80,
                   86 + 13 + 28 + 80 + 99, 86 + 2*99, 2*13 + 56]
    need(term_bounds == [exact_degree, 306, 284, 82], "wrong global degree bound")

    # Full top form in q=beta*J and k=eta+zeta, using six formal symbols.
    q_minus_f = add(atom("q"), atom("F"), -1)
    Mtop = monomial(4, q=11, w=1, Y=1)
    Qtop = monomial(4, i=4, q=38, w=10, Y=22, k=12)
    defect_top = (monomial(-1, i=2, q=20, w=4, Y=12, k=8) if sharp else
                  monomial(2, i=2, q=23, w=5, Y=13, k=8))
    Vtop = mul(monomial(-4, i=4, q=35, w=8, Y=20, k=12), q_minus_f)
    # Independently recover these prefix leading forms from the literal DAG.
    prefix = leading_prefix(new, degrees, ["Mtot", "Q", "V", "Am1", "U", "Dtau"])
    substitutions = {"q": mul(atom("beta"), atom("J")),
                     "k": add(atom("eta"), atom("zeta"))}
    for key, claimed in (("Mtot", Mtop), ("Q", Qtop), ("V", Vtop)):
        need(prefix[key] == substitute_symbols(claimed, substitutions),
             "literal leading prefix differs from claimed formula: " + key)
    literal_defect_top = mul(power(prefix["U"], 2), power(prefix["Dtau"], 2))
    literal_defect_top = (mul(integer(-1), literal_defect_top) if sharp else
                          mul(integer(2), mul(prefix["Am1"], literal_defect_top)))
    need(literal_defect_top == substitute_symbols(defect_top, substitutions),
         "literal defect leading form differs from the proof")
    top = mul(integer(-1), mul(power(Mtop, 2), mul(Qtop, mul(defect_top, power(Vtop, 2)))))
    q_power, w_power, y_power, selected_coefficient = ((150, 32, 76, 2**10) if sharp
                                                      else (153, 33, 77, -(2**11)))
    expected_top = mul(monomial(selected_coefficient, q=q_power, w=w_power, Y=y_power, i=14, k=44),
                       power(q_minus_f, 2))
    need(top == expected_top, "incorrect complete leading homogeneous form")
    need(all(len(monomial_) == exact_degree for monomial_ in top), "wrong leading degree")
    selected = tuple(sorted(["q"]*q_power + ["w"]*w_power + ["Y"]*y_power
                            + ["i"]*14 + ["k"]*44 + ["F"]*2))
    need(top.get(selected) == selected_coefficient, "attained leading coefficient is false")
    need(new["exact_degree"] == exact_degree, "wrong degree annotation")
    return {"status": "pass", "variables": 10, "domain": "strictly positive integers",
            "operations": operation_count, "operation_breakdown": dict(operations),
            "degree": exact_degree, "global_final_term_degree_bounds": term_bounds,
            "attained_coefficient": f"[J^{q_power}*w^{w_power}*Y^{y_power}*i^14*eta^44*F^2] = {selected_coefficient}*beta^{q_power}",
            "checks": ["complete DAG topology and liveness", "unchanged coherent coefficient binding",
                       "only stated carrier gates changed", "free-polynomial shear identity",
                       "exact radicand defect", "exact global cancellation identity",
                       "global degree bound", "literal prefix leading-form propagation",
                       "complete top-form multiplication"]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("parent", type=Path)
    parser.add_argument("equation", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--coefficients", type=Path)
    args = parser.parse_args()
    parent, equation = json.loads(args.parent.read_text()), json.loads(args.equation.read_text())
    result = verify(parent, equation)
    if args.coefficients:
        coefficient_values = {}
        coefficient_receipt = {}
        for port, spec in equation["coefficient_binding"]["ports"].items():
            compressed = (args.coefficients / spec["file"]).read_bytes()
            raw = gzip.decompress(compressed)
            need(hashlib.sha256(compressed).hexdigest() == spec["gzip_sha256"],
                 "compressed coefficient hash mismatch: " + port)
            need(hashlib.sha256(raw).hexdigest() == spec["raw_sha256"],
                 "raw coefficient hash mismatch: " + port)
            value = int.from_bytes(raw, "little")
            need(value.bit_length() == spec["bits"], "coefficient bit length mismatch")
            need(raw == value.to_bytes((value.bit_length()+7)//8, "little"),
                 "coefficient bytes have a redundant high zero")
            coefficient_values[port] = value
            coefficient_receipt[port] = {"bits": spec["bits"], "raw_sha256": spec["raw_sha256"]}
        beta = coefficient_values["beta"]
        need(beta == (1 << (67*8807)) - 1 and coefficient_values["K0"] > 0
             and 0 < coefficient_values["MC"] < beta < coefficient_values["MF"] < 2*beta,
             "authentic tuple does not satisfy its declared coefficient box")
        result["coefficient_payloads"] = coefficient_receipt
    result["sha256"] = {"parent": hashlib.sha256(args.parent.read_bytes()).hexdigest(),
                        "equation": hashlib.sha256(args.equation.read_bytes()).hexdigest(),
                        "checker": hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    result["scope"] = "New finite algebra audited independently; unbounded positive-witness proof reviewed separately."
    encoded = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(encoded)
    print(encoded, end="")


if __name__ == "__main__":
    main()
