#!/usr/bin/env python3
"""Independent certificate verifier: reconstructs twice the SOS energy.

Does not import build.py. It checks the normalization's topological monic
definitions and exact symbolic pullbacks, all occurrence maps, all coefficients,
and the complete forward identity at deterministic signed integer samples.
"""
import argparse
import hashlib
import json
import random
from collections import defaultdict
from pathlib import Path


def require(value, message):
    if not value:
        raise ValueError(message)


def add(p, mon, c):
    key = tuple(sorted(mon))
    p[key] = p.get(key, 0) + c
    if p[key] == 0:
        del p[key]


def multiply(a, b):
    out = {}
    for ma, ca in a.items():
        for mb, cb in b.items():
            add(out, ma + mb, ca * cb)
    return out


def collect(terms):
    out = {}
    for c, mon in terms:
        add(out, mon, c)
    return out


def substitute(terms, meanings):
    out = {}
    for c, mon in terms:
        q = {(): c}
        for v in mon:
            q = multiply(q, meanings[v])
        for m, a in q.items():
            add(out, m, a)
    return out


def value(terms, assignment):
    total = 0
    for c, mon in terms:
        z = c
        for v in mon:
            z *= assignment[v]
        total += z
    return total


def verify(source_bytes, polynomial_bytes, certificate_bytes):
    source, artifact, cert = map(json.loads, (source_bytes, polynomial_bytes, certificate_bytes))
    require(hashlib.sha256(source_bytes).hexdigest() == cert["source_sha256"], "Source hash")
    norm, original_n = cert["normalization"], len(source["variables"])
    nvars, rows = norm["variables"], norm["rows"]
    require(norm["original_variables"] == original_n, "Original dimension")
    require({v for r in source["residuals"] for c, m in r["terms"] for v in m}
            == set(range(original_n)), "Every original variable occurs")
    require({v for r in rows for c, m in r["terms"] for v in m}
            == set(range(len(nvars))), "Every normalized variable occurs")
    meanings, targets = [], {}
    for i, v in enumerate(nvars):
        if i < original_n:
            require(v == {"kind": "original", "index": i}, "Original coordinate map")
            meanings.append({(i,): 1})
        elif v["kind"] == "constant":
            c = v["value"]
            require(isinstance(c, int) and c > 1, "Constant data")
            key = ("constant", c)
            require(key not in targets, "Duplicate constant")
            targets[key] = i
            meanings.append({(): c})
        elif v["kind"] == "scale":
            c, old = v["coefficient"], v["variable"]
            require(isinstance(c, int) and c > 1 and 0 <= old < original_n, "Scale data")
            key = ("scale", c, old)
            require(key not in targets, "Duplicate scale")
            targets[key] = i
            meanings.append({(old,): c})
        else:
            raise ValueError("Invalid normalized coordinate")
    definitions, source_rows = set(), set()
    for row in rows:
        terms = row["terms"]
        require(all(c in (-1, 1) and len(m) <= 2 and
                    all(isinstance(v, int) and 0 <= v < len(nvars) for v in m)
                    for c, m in terms), "Unit coefficient quadratic normalization")
        if row["kind"] in ("constant", "scale"):
            key = (("constant", row["value"]) if row["kind"] == "constant" else
                   ("scale", row["coefficient"], row["variable"]))
            target = targets[key]
            require(target not in definitions, "Repeated monic definition")
            definitions.add(target)
            occurrences = [(c, m) for c, m in terms if target in m]
            require(occurrences == [(1, [target])], "Monic defining equation")
            require(all(v <= target for c, m in terms for v in m), "Topological definition")
            require(substitute(terms, meanings) == {}, "Defining equation pullback")
        elif row["kind"] == "source":
            r = row["source_row"]
            require(0 <= r < len(source["residuals"]) and r not in source_rows, "Source row map")
            source_rows.add(r)
            require(substitute(terms, meanings) == collect(source["residuals"][r]["terms"]),
                    "Exact source polynomial pullback")
        else:
            raise ValueError("Unknown normalized row kind")
    require(definitions == set(range(original_n, len(nvars))), "Complete derived definitions")
    require(source_rows == set(range(len(source["residuals"]))), "Complete source rows")

    variables = artifact["variables"]
    n = len(variables)
    aliases, units, used = defaultdict(list), [], set()
    twice_energy = {}

    def reserve(v):
        require(isinstance(v, int) and 0 <= v < n and v not in used, "Fresh coordinate")
        used.add(v)

    def square(terms):
        # Ordered pairs give the literal square, independently of build.py's
        # collision-free closed formula.
        for c, a in terms:
            for d, b in terms:
                add(twice_energy, a + b, c * d)

    require(len(cert["blocks"]) == len(rows), "Complete block list")
    for r, block in enumerate(cert["blocks"]):
        terms = rows[r]["terms"]
        require(block["normalized_row"] == r, "Block order")
        signs, products, witnesses = block["signs"], block["products"], block["witnesses"]
        require(signs == [c for c, m in terms] and len(products) == len(terms) == len(witnesses),
                "Block arity and signs")
        for j, ((sign, oldmon), mon, w) in enumerate(zip(terms, products, witnesses)):
            require(len(mon) == 2, "Homogeneous disjoint product")
            for k, v in enumerate(mon):
                reserve(v)
                if k < len(oldmon):
                    expected = {"kind": "alias", "normalized_variable": oldmon[k],
                                "row": r, "occurrence": j, "slot": k}
                    aliases[oldmon[k]].append(v)
                else:
                    expected = {"kind": "unit", "row": r, "occurrence": j, "slot": k}
                    units.append(v)
                require(variables[v] == expected, "Occurrence binding")
            reserve(w)
            require(variables[w] == {"kind": "product", "row": r, "occurrence": j}, "Product port")
            square([(1, mon), (-1, [w])])
        square(list(zip(signs, products)))
        square([(s, [w]) for s, w in zip(signs, witnesses)])

    seen_groups = set()
    for cycle in cert["equality_cycles"]:
        old, nodes = cycle["normalized_variable"], cycle["aliases"]
        require(old in aliases and old not in seen_groups, "Group source")
        seen_groups.add(old)
        base = aliases[old]
        if len(base) == 1:
            require(cycle["singleton"] and nodes == base, "Singleton class")
            continue
        require(not cycle["singleton"], "Nontrivial class")
        if len(base) == 2:
            require(len(nodes) == 3 and nodes[:2] == base, "Two-class dummy")
            reserve(nodes[2])
            require(variables[nodes[2]] == {"kind": "equality_dummy", "normalized_variable": old},
                    "Equality dummy binding")
        else:
            require(nodes == base, "Cycle class")
        for i, a in enumerate(nodes):
            square([(1, [a]), (-1, [nodes[(i + 1) % len(nodes)]])])
    require(seen_groups == set(aliases), "Every occurrence class linked")
    unit_path = cert["unit_path"]
    require(unit_path[:len(units)] == units and len(unit_path) == max(2, len(units)), "Unit path")
    for v in unit_path[len(units):]:
        reserve(v)
        require(variables[v] == {"kind": "unit_dummy"}, "Unit dummy")
    require(used == set(range(n)), "Every compiled coordinate accounted for")
    square([(1, [unit_path[0]]), (-1, [])])
    for a, b in zip(unit_path, unit_path[1:]):
        square([(1, [a]), (-1, [b])])
    square([(1, [unit_path[-1]]), (-1, [])])
    require(all(c % 2 == 0 for c in twice_energy.values()), "Integral half energy")
    expected = {m: c // 2 for m, c in twice_energy.items()}
    actual = collect(artifact["terms"])
    require(len(actual) == len(artifact["terms"]), "No repeated or zero sparse monomials")
    require(actual == expected, "Exact expanded polynomial")
    require(set(actual.values()) == {-1, 1} and actual.get(()) == 1, "Height one and constant one")
    require(max(map(len, actual)) == 4, "Exact degree four")
    require(all(all(0 <= i < n for i in m) for m in actual), "Variable bounds")
    require({v for m in actual for v in m} == set(range(n)), "Every output variable occurs")
    require(max(m.count(v) for m in actual for v in m) == 2, "Individual degree at most two")
    require(artifact["metrics"]["variables"] == n and artifact["metrics"]["monomials"] == len(actual),
            "Published dimensions")

    # These are supplemental checks of the forward value identity, not a
    # replacement for the all-integer identity and zero-set proof.
    rng = random.Random(20261024)
    samples = [[0] * original_n, [1] * original_n,
               [(-1) ** i * (i % 4) for i in range(original_n)]]
    samples.extend([[rng.randint(-4, 4) for _ in range(original_n)] for _ in range(2)])
    for old_values in samples:
        normalized_values = [sum(c * (old_values[m[0]] if m else 1) for m, c in p.items())
                             for p in meanings]
        out_values = [0] * n
        for i, v in enumerate(variables):
            if v["kind"] in ("alias", "equality_dummy"):
                out_values[i] = normalized_values[v["normalized_variable"]]
            elif v["kind"] in ("unit", "unit_dummy"):
                out_values[i] = 1
        for block in cert["blocks"]:
            for mon, w in zip(block["products"], block["witnesses"]):
                out_values[w] = out_values[mon[0]] * out_values[mon[1]]
        wanted = sum(value(r["terms"], old_values) ** 2 for r in source["residuals"])
        require(value(artifact["terms"], out_values) == wanted, "Signed forward value identity")

    return {"status": "PASS", "source_sha256": hashlib.sha256(source_bytes).hexdigest(),
            "polynomial_sha256": hashlib.sha256(polynomial_bytes).hexdigest(),
            "certificate_sha256": hashlib.sha256(certificate_bytes).hexdigest(),
            "normalized_rows_checked": len(rows), "source_pullbacks_checked": len(source_rows),
            "variables": n, "expanded_monomials_checked": len(actual),
            "exact_degree": 4, "coefficient_height": 1, "constant_coefficient": 1,
            "maximum_individual_degree": 2,
            "all_source_normalized_output_variables_occur": True,
            "signed_forward_samples": len(samples),
            "semantic_scope": "Exact finite compiler certificate; source calibration inherited"}


def main():
    here = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, default=here / "source/equation.json")
    parser.add_argument("--input", type=Path, default=here / "output")
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()
    source_bytes = args.source.read_bytes()
    polynomial_bytes = (args.input / "polynomial.json").read_bytes()
    certificate_bytes = (args.input / "certificate.json").read_bytes()
    result = verify(source_bytes, polynomial_bytes, certificate_bytes)
    rejections = []
    for mutation in ("flip_nonconstant_coefficient", "delete_constant_term"):
        altered = json.loads(polynomial_bytes)
        if mutation == "flip_nonconstant_coefficient":
            next(t for t in altered["terms"] if t[1])[0] *= -1
        else:
            altered["terms"] = [t for t in altered["terms"] if t[1]]
        try:
            verify(source_bytes, json.dumps(altered).encode(), certificate_bytes)
        except ValueError as exc:
            require(str(exc) == "Exact expanded polynomial", "Unexpected corruption rejection")
            rejections.append({"mutation": mutation, "rejection": str(exc)})
        else:
            raise ValueError("Corrupted artifact was accepted")
    result["rejected_artifact_controls"] = rejections
    text_path = args.input / "polynomial.txt"
    if text_path.exists():
        plaintext_terms = []
        for line in text_path.read_text().splitlines():
            if not line or line.startswith("#") or line == "= 0":
                continue
            require(line[0] in "+-", "Plaintext term sign")
            c, body = (1 if line[0] == "+" else -1), line[1:]
            mon = [] if body == "1" else [int(t[1:]) for t in body.split("*")
                                           if t.startswith("x") and t[1:].isdigit()]
            require(body == "1" or len(mon) == len(body.split("*")), "Plaintext monomial")
            plaintext_terms.append([c, mon])
        require(plaintext_terms == json.loads(polynomial_bytes)["terms"], "Complete plaintext equation")
        result["plaintext_equation_sha256"] = hashlib.sha256(text_path.read_bytes()).hexdigest()
    if args.receipt:
        args.receipt.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
