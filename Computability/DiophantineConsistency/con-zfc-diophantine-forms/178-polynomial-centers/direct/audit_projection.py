#!/usr/bin/env python3
"""Independent, exact common-radical coefficient projection checker.

The polynomial identities hold over integers. Natural-domain claims require
the additional checker and ordinary canonical-sign proof in verify_direct.py.

Standard library only.  This checker does not import the discovery/reduction
program.  It constructs projected rows by a row-combination identity, rather
than by the reducer's shear followed by polynomial substitution.
"""
from __future__ import annotations
import argparse
import copy
import hashlib
import json
from math import gcd
from pathlib import Path
import random


class InvalidCertificate(ValueError):
    pass


def demand(condition, message):
    if not condition:
        raise InvalidCertificate(message)


def canonical(value):
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


def sha(value):
    return hashlib.sha256(canonical(value)).hexdigest()


def polynomial(terms, dimension, maximum_degree=2):
    out = {}
    for coefficient, monomial in terms:
        demand(type(coefficient) is int, "noninteger coefficient")
        demand(len(monomial) <= maximum_degree, "excessive residual degree")
        demand(all(type(i) is int and 0 <= i < dimension for i in monomial),
               "invalid variable index")
        key = tuple(sorted(monomial))
        out[key] = out.get(key, 0) + coefficient
    return {key: coefficient for key, coefficient in out.items() if coefficient}


def serial(poly):
    return [[coefficient, list(monomial)] for monomial, coefficient in sorted(poly.items())]


def linear_combine(first, scalar, second):
    out = dict(first)
    for key, coefficient in second.items():
        out[key] = out.get(key, 0) + scalar * coefficient
    return {key: coefficient for key, coefficient in out.items() if coefficient}


def product(first, second):
    out = {}
    for m1, c1 in first.items():
        for m2, c2 in second.items():
            key = tuple(sorted(m1 + m2))
            out[key] = out.get(key, 0) + c1 * c2
    return {key: c for key, c in out.items() if c}


def value(poly, point):
    total = 0
    for monomial, coefficient in poly.items():
        for index in monomial:
            coefficient *= point[index]
        total += coefficient
    return total


def radical_derivative(poly, direction):
    """The coefficients of the degree-one part of D_v(poly)."""
    derivative = {}
    for monomial, coefficient in poly.items():
        if len(monomial) == 2:
            i, j = monomial
            derivative[i] = derivative.get(i, 0) + coefficient * direction.get(j, 0)
            derivative[j] = derivative.get(j, 0) + coefficient * direction.get(i, 0)
    return {i: coefficient for i, coefficient in derivative.items() if coefficient}


def one_step(equation, certificate, numerical_controls=True):
    demand(equation.get("domain") in ("unrestricted integers", "nonnegative integers"), "unsupported domain")
    demand(certificate["input_sha256"] == sha(equation), "input digest mismatch")
    n = len(equation["variables"])
    p = certificate["pivot"]
    r = certificate["deleted_row"]
    demand(type(p) is int and 0 <= p < n, "invalid pivot index")
    demand(type(r) is int and 0 <= r < len(equation["residuals"]), "invalid row index")
    direction = dict(certificate["direction"])
    demand(len(direction) == len(certificate["direction"]), "duplicate direction index")
    demand(all(type(i) is int and 0 <= i < n and type(c) is int and c != 0
               for i, c in direction.items()), "invalid direction")
    demand(direction.get(p) == 1, "pivot coordinate is not positive unit")
    demand(equation["variables"][p]["name"] == certificate["pivot_name"], "pivot name mismatch")
    remaining = [i for i in range(n) if i != p]
    demand(certificate["retained_old_indices"] == remaining, "retained indices mismatch")
    rename = {index: new for new, index in enumerate(remaining)}
    rows = [polynomial(row["terms"], n) for row in equation["residuals"]]
    for index, poly in enumerate(rows):
        demand(not radical_derivative(poly, direction), f"direction not in radical of row {index}")
    slopes = [sum(poly.get((i,), 0) * c for i, c in direction.items()) for poly in rows]
    a = slopes[r]
    demand(a in (-1, 1), "nonunit pivot slope")
    demand(certificate["slope"] == a, "incorrect stated slope")

    # Q_i(y) at y_p=0, then R_i=Q_i(y)-a_r*a_i*Q_r(y).
    restricted = [{mon: coeff for mon, coeff in poly.items() if p not in mon} for poly in rows]
    solution = {mon: -a * coeff for mon, coeff in restricted[r].items()}
    demand(polynomial(certificate["sheared_pivot_solution"], n) == solution,
           "incorrect pivot solution polynomial")
    projected = [linear_combine(poly, -a * slopes[index], restricted[r])
                 for index, poly in enumerate(restricted)]
    demand(not projected[r], "pivot row did not vanish")

    answer = copy.deepcopy(equation)
    answer.pop("metrics", None)
    answer["variables"] = [copy.deepcopy(equation["variables"][i]) for i in remaining]
    for i in remaining:
        if direction.get(i):
            answer["variables"][rename[i]]["name"] = f"radical{n}.{i}"
    answer["residuals"] = []
    for index, poly in enumerate(projected):
        if index == r:
            continue
        row = copy.deepcopy(equation["residuals"][index])
        row["terms"] = serial({tuple(rename[i] for i in mon): coeff for mon, coeff in poly.items()})
        answer["residuals"].append(row)
    answer["variant"] = equation.get("variant", "") + ":radical_projection"
    demand(certificate["output_sha256"] == sha(answer), "projected output digest mismatch")

    # These arithmetic controls supplement the coefficient proof; no roots
    # of the consistency equation are assumed or searched for.
    if numerical_controls:
        generator = random.Random(1729 + n + p)
        for _ in range(12):
            y = [generator.randint(-5, 5) for _ in range(n)]
            y[p] = 0
            t = value(solution, y)
            x = [y[i] + direction.get(i, 0) * t for i in range(n)]
            demand(all(value(poly, x) == value(projected[index], y)
                       for index, poly in enumerate(rows)), "lift identity control failed")
            demand(all(x[i] - direction.get(i, 0) * x[p] == y[i]
                       for i in range(n)), "integer inverse control failed")
    return answer


def expanded_sos(equation):
    n = len(equation["variables"])
    out = {}
    for row in equation["residuals"]:
        poly = polynomial(row["terms"], n)
        for m1, c1 in poly.items():
            for m2, c2 in poly.items():
                mon = tuple(sorted(m1 + m2))
                out[mon] = out.get(mon, 0) + c1 * c2
    return {mon: c for mon, c in out.items() if c}


def radical_rank_certificate(equation):
    """A full column-rank certificate modulo a checked prime proves nullity zero over Q."""
    prime = 1000003
    demand(all(prime % d for d in range(2, int(prime**0.5) + 1)), "rank modulus is not prime")
    n = len(equation["variables"])
    basis = {}
    source_rows = []
    pivots = []
    for row_index, row in enumerate(equation["residuals"]):
        poly = polynomial(row["terms"], n)
        hessian = {}
        for monomial, c in poly.items():
            if len(monomial) == 2:
                i, j = monomial
                hessian.setdefault(i, {})[j] = hessian.setdefault(i, {}).get(j, 0) + c
                hessian.setdefault(j, {})[i] = hessian.setdefault(j, {}).get(i, 0) + c
        for coordinate, hrow in sorted(hessian.items()):
            residual = {i: c % prime for i, c in hrow.items() if c % prime}
            while residual:
                pivot = min(residual)
                if pivot not in basis:
                    lead = residual[pivot]
                    inverse = pow(lead, -1, prime)
                    basis[pivot] = {i: c * inverse % prime for i, c in residual.items()}
                    source_rows.append([row_index, coordinate])
                    pivots.append([pivot, lead])
                    break
                scalar = residual[pivot]
                for i, c in basis[pivot].items():
                    entry = (residual.get(i, 0) - scalar * c) % prime
                    if entry:
                        residual[i] = entry
                    else:
                        residual.pop(i, None)
        if len(basis) == n:
            break
    return {"prime": prime, "rank_mod_prime": len(basis), "columns": n,
            "full_column_rank": len(basis) == n,
            "independent_hessian_rows": source_rows, "pivots": pivots,
            "meaning": "Full column rank modulo a prime implies common Hessian radical is zero over Q."}


def metrics(equation, expansion):
    rows = [polynomial(row["terms"], len(equation["variables"])) for row in equation["residuals"]]
    return {"variables": len(equation["variables"]), "rows": len(rows),
            "residual_terms": sum(len(row) for row in rows),
            "row_height": max(abs(c) for row in rows for c in row.values()),
            "degree": max(map(len, expansion)), "monomials": len(expansion),
            "height": max(map(abs, expansion.values()))}


def mutation_controls(equation, step):
    result = []

    def rejected(name, eq, certificate):
        try:
            one_step(eq, certificate, numerical_controls=False)
        except InvalidCertificate as exc:
            result.append({"mutation": name, "rejected": True, "reason": str(exc)})
        else:
            raise InvalidCertificate("mutation was accepted: " + name)

    c = copy.deepcopy(step)
    c["direction"] = [[i, coefficient + 2 * (i != c["pivot"])] for i, coefficient in c["direction"]]
    rejected("direction coefficient changed", equation, c)
    c = copy.deepcopy(step)
    c["slope"] = -c["slope"]
    rejected("pivot slope sign changed", equation, c)
    c = copy.deepcopy(step)
    c["sheared_pivot_solution"][0][0] += 1
    rejected("pivot solution coefficient changed", equation, c)
    c = copy.deepcopy(step)
    c["retained_old_indices"] = c["retained_old_indices"][1:]
    rejected("retained coordinate omitted", equation, c)
    eq = copy.deepcopy(equation)
    eq["domain"] = "natural numbers"
    c = copy.deepcopy(step)
    c["input_sha256"] = sha(eq)
    rejected("domain silently changed", eq, c)
    eq = copy.deepcopy(equation)
    eq["residuals"][0]["terms"].append([1, [step["pivot"], step["pivot"]]])
    c = copy.deepcopy(step)
    c["input_sha256"] = sha(eq)
    rejected("quadratic term added with input digest refreshed", eq, c)
    eq = copy.deepcopy(equation)
    eq["residuals"][step["deleted_row"]]["terms"].append([1, [step["pivot"]]])
    c = copy.deepcopy(step)
    c["input_sha256"] = sha(eq)
    rejected("nonunit or zero pivot slope with input digest refreshed", eq, c)
    c = copy.deepcopy(step)
    c["output_sha256"] = "0" * 64
    rejected("output digest replaced", equation, c)
    return result


def audit(source_path, result_directory):
    source = json.loads(source_path.read_text())
    certificate = json.loads((result_directory / "projection_certificate.json").read_text())
    target = json.loads((result_directory / "equation.json").read_text())
    demand(certificate.get("schema") == "common_hessian_radical_projection_v1", "unknown certificate schema")
    current = source
    summaries = []
    for index, step in enumerate(certificate["steps"]):
        current = one_step(current, step)
        summaries.append({"step": index + 1, "variables": len(current["variables"]),
                          "rows": len(current["residuals"]), "canonical_sha256": sha(current)})
    demand(current == target, "final equation is not the certificate result")
    expanded = expanded_sos(target)
    supplied_expansion = json.loads((result_directory / "expanded_polynomial.json").read_text())
    demand(supplied_expansion["variables"] == len(target["variables"]), "expansion dimension mismatch")
    demand(polynomial(supplied_expansion["terms"], len(target["variables"]), 4) == expanded,
           "expanded polynomial coefficient mismatch")
    computed_metrics = metrics(target, expanded)
    supplied_metrics = json.loads((result_directory / "metrics.json").read_text())
    demand(computed_metrics == supplied_metrics, "metrics mismatch")
    controls = mutation_controls(source, certificate["steps"][0]) if certificate["steps"] else []
    return {"status": "PASS", "method": "exact directional derivative and row-combination replay",
            "source_path": str(source_path), "result_directory": str(result_directory),
            "source_canonical_sha256": sha(source), "output_canonical_sha256": sha(target),
            "source_metrics": metrics(source, expanded_sos(source)),
            "output_metrics": computed_metrics, "steps": summaries,
            "final_radical_rank_certificate": radical_rank_certificate(target),
            "mutations": controls, "numeric_lift_controls": 12 * len(summaries),
            "limits": ["Checks the new algebraic projection, not inherited calculus-to-ZFC calibration.",
                       "Finite numerical controls supplement exact coefficient identities and are not semantic proofs.",
                       "Full modular rank certifies absence of further common-radical directions only; no global optimality is claimed."]}


def row_operations(source, certificate):
    demand(certificate.get("schema") == "integer_row_operations_v1", "unknown row-operation schema")
    demand(certificate["input_sha256"] == sha(source), "row-operation input digest mismatch")
    n = len(source["variables"])
    rows = [polynomial(row["terms"], n) for row in source["residuals"]]
    original = copy.deepcopy(rows)
    for op in certificate["operations"]:
        demand(isinstance(op, list) and len(op) == 3 and all(type(v) is int for v in op),
               "invalid row-operation data")
        i, j, k = op
        demand(0 <= i < len(rows) and 0 <= j < len(rows) and i != j, "invalid elementary row indices")
        rows[i] = linear_combine(rows[i], k, rows[j])
    target = copy.deepcopy(source)
    target["variant"] += ":integer_row_reduction"
    for row, poly in zip(target["residuals"], rows):
        row["terms"] = serial(poly)
    demand(sha(target) == certificate["output_sha256"], "row-operation output digest mismatch")
    inverse = copy.deepcopy(rows)
    for i, j, k in reversed(certificate["operations"]):
        inverse[i] = linear_combine(inverse[i], -k, inverse[j])
    demand(inverse == original, "inverse row-operation replay failed")
    return target


def audit_rows(source_path, result_directory):
    source = json.loads(source_path.read_text())
    cert = json.loads((result_directory / "row_certificate.json").read_text())
    target = json.loads((result_directory / "equation.json").read_text())
    demand(row_operations(source, cert) == target, "row-reduced equation mismatch")
    expansion = expanded_sos(target)
    expanded_file = json.loads((result_directory / "expanded_polynomial.json").read_text())
    demand(expanded_file["variables"] == len(target["variables"]), "row-reduced expansion dimension mismatch")
    demand(polynomial(expanded_file["terms"], len(target["variables"]), 4) == expansion,
           "row-reduced expansion coefficient mismatch")
    computed = metrics(target, expansion)
    demand(json.loads((result_directory / "metrics.json").read_text()) == computed,
           "row-reduced metrics mismatch")
    mutations = []
    if cert["operations"]:
        for name, mutate in [
            ("source row equals target row", lambda c: c["operations"][0].__setitem__(1, c["operations"][0][0])),
            ("row multiplier changed", lambda c: c["operations"][0].__setitem__(2, c["operations"][0][2] + 1)),
            ("first row operation omitted", lambda c: c["operations"].pop(0)),
            ("output digest changed", lambda c: c.__setitem__("output_sha256", "0" * 64)),
        ]:
            corrupt = copy.deepcopy(cert)
            mutate(corrupt)
            try:
                row_operations(source, corrupt)
            except InvalidCertificate as exc:
                mutations.append({"mutation": name, "rejected": True, "reason": str(exc)})
            else:
                raise InvalidCertificate("row mutation was accepted: " + name)
    return {"status": "PASS", "method": "exact elementary integer row operations and reverse replay",
            "source_path": str(source_path), "result_directory": str(result_directory),
            "source_canonical_sha256": sha(source), "output_canonical_sha256": sha(target),
            "operations": len(cert["operations"]), "source_metrics": metrics(source, expanded_sos(source)),
            "output_metrics": computed, "mutations": mutations,
            "final_radical_rank_certificate": radical_rank_certificate(target),
            "limits": ["The sum-of-squares polynomial changes; its integer zero set is preserved.",
                       "No global variable, degree, monomial, or coefficient-height minimum is proved."]}


def affine_projection(source, certificate):
    demand(certificate.get("schema") == "unit-affine-projection-v1", "unknown affine projection schema")
    demand(source.get("domain") == "unrestricted integers", "affine projection domain is not all integers")
    n = len(source["variables"])
    rows = [polynomial(row["terms"], n) for row in source["residuals"]]
    p = certificate["eliminated_coordinate"]
    r = certificate["omitted_residual"]
    demand(type(p) is int and 0 <= p < n, "invalid affine pivot coordinate")
    demand(type(r) is int and 0 <= r < len(rows), "invalid affine omitted row")
    demand(certificate["eliminated_variable"] == source["variables"][p], "affine pivot metadata mismatch")
    relation = certificate["affine_consequence"]
    combined = {}
    coefficients = {}
    for c, j in relation["row_combination"]:
        demand(type(c) is int and type(j) is int and 0 <= j < len(rows), "invalid affine combination")
        coefficients[j] = coefficients.get(j, 0) + c
        combined = linear_combine(combined, c, rows[j])
    demand(coefficients.get(r, 0) != 0, "omitted row has zero combination coefficient")
    demand(all(len(mon) <= 1 for mon in combined), "row combination is not affine")
    demand(polynomial(relation["affine_terms"], n, 1) == combined, "incorrect affine consequence")
    content = gcd(*(abs(c) for c in combined.values()))
    demand(content > 0 and content == relation["whole_content"], "incorrect affine content")
    demand(gcd(*(abs(c) for mon, c in combined.items() if len(mon) == 1)) == relation["linear_gcd"],
           "incorrect affine linear gcd")
    normalized = {mon: c // content for mon, c in combined.items()}
    a = normalized.get((p,), 0)
    demand(a in (-1, 1), "affine pivot coefficient is not a unit")
    replacement = {mon: -a * c for mon, c in normalized.items() if mon != (p,)}
    demand(polynomial(certificate["restoration_terms_original_indices"], n, 1) == replacement,
           "incorrect affine restoration polynomial")
    demand(all(p not in mon for mon in replacement), "restoration uses eliminated variable")
    replacement_square = product(replacement, replacement)
    projected = []
    # Independent substitution formula: Q=A*x_p^2+B*x_p+C becomes A*S^2+B*S+C.
    for row in rows:
        square_coefficient = row.get((p, p), 0)
        linear_factor = {}
        constant_part = {}
        for mon, c in row.items():
            count = mon.count(p)
            if count == 0:
                constant_part[mon] = c
            elif count == 1:
                other = tuple(i for i in mon if i != p)
                linear_factor[other] = linear_factor.get(other, 0) + c
        new = linear_combine(constant_part, 1, product(linear_factor, replacement))
        new = linear_combine(new, square_coefficient, replacement_square)
        demand(all(len(mon) <= 2 and p not in mon for mon in new), "invalid substituted residual")
        projected.append(new)
    combined_after = {}
    for j, c in coefficients.items():
        combined_after = linear_combine(combined_after, c, projected[j])
    demand(not combined_after, "affine relation does not vanish after substitution")

    target = copy.deepcopy(source)
    target["variables"] = [copy.deepcopy(v) for i, v in enumerate(source["variables"]) if i != p]
    target["residuals"] = []
    for i, row in enumerate(source["residuals"]):
        if i == r:
            continue
        new_row = copy.deepcopy(row)
        new_row["terms"] = serial({tuple(j - (j > p) for j in mon): c for mon, c in projected[i].items()})
        target["residuals"].append(new_row)
    target["variant"] = str(source.get("variant", "")) + "; exact affine projection"
    generator = random.Random(8107 + n + p)
    for _ in range(12):
        point = [generator.randint(-5, 5) for _ in range(n)]
        point[p] = value(replacement, point)
        demand(value(combined, point) == 0, "affine lift does not satisfy exposed relation")
        demand(all(value(q, point) == value(projected[i], point) for i, q in enumerate(rows)),
               "affine substitution evaluation control failed")
    return target


def audit_affine(source_path, result_directory):
    raw_source = source_path.read_bytes()
    raw_target = (result_directory / "equation.json").read_bytes()
    source = json.loads(raw_source)
    target = json.loads(raw_target)
    cert = json.loads((result_directory / "projection_certificate.json").read_text())
    demand(cert["input_sha256"] == hashlib.sha256(raw_source).hexdigest(), "affine input raw digest mismatch")
    demand(cert["output_sha256"] == hashlib.sha256(raw_target).hexdigest(), "affine output raw digest mismatch")
    demand(affine_projection(source, cert) == target, "affine target coefficient mismatch")
    expansion = expanded_sos(target)
    expanded_file = json.loads((result_directory / "expanded_polynomial.json").read_text())
    demand(polynomial(expanded_file["terms"], len(target["variables"]), 4) == expansion,
           "affine expansion coefficient mismatch")
    computed = metrics(target, expansion)
    supplied = json.loads((result_directory / "metrics.json").read_text())
    mapping = {"variables": "variables", "residuals": "rows", "degree": "degree",
               "collected_terms": "monomials", "coefficient_height": "height"}
    demand(all(key in mapping and computed[mapping[key]] == val for key, val in supplied.items()),
           "affine metrics mismatch")
    mutations = []
    def reject(name, c):
        try:
            out = affine_projection(source, c)
            demand(out == target, "mutated affine target differs")
        except InvalidCertificate as exc:
            mutations.append({"mutation": name, "rejected": True, "reason": str(exc)})
        else:
            raise InvalidCertificate("affine mutation was accepted: " + name)
    c = copy.deepcopy(cert)
    c["affine_consequence"]["row_combination"][0][0] += 1
    reject("row-combination coefficient changed", c)
    c = copy.deepcopy(cert)
    c["affine_consequence"]["affine_terms"][0][0] += 1
    reject("affine identity coefficient changed", c)
    c = copy.deepcopy(cert)
    c["restoration_terms_original_indices"][0][0] += 1
    reject("restoration coefficient changed", c)
    c = copy.deepcopy(cert)
    c["omitted_residual"] = next(i for i in range(len(source["residuals"]))
                                 if i not in [j for _, j in c["affine_consequence"]["row_combination"]])
    reject("omitted row not in combination", c)
    c = copy.deepcopy(cert)
    c["affine_consequence"]["whole_content"] *= 2
    reject("false content divisor", c)
    return {"status": "PASS", "method": "exact affine combination and quadratic coefficient substitution",
            "source_path": str(source_path), "result_directory": str(result_directory),
            "source_raw_sha256": hashlib.sha256(raw_source).hexdigest(),
            "output_raw_sha256": hashlib.sha256(raw_target).hexdigest(),
            "source_canonical_sha256": sha(source), "output_canonical_sha256": sha(target),
            "source_metrics": metrics(source, expanded_sos(source)), "output_metrics": computed,
            "exposed_row_combination": cert["affine_consequence"]["row_combination"],
            "eliminated_coordinate": cert["eliminated_coordinate"],
            "omitted_residual": cert["omitted_residual"], "mutations": mutations,
            "numeric_lift_controls": 12, "final_radical_rank_certificate": radical_rank_certificate(target),
            "limits": ["Exact ordinary algebraic certificate, not a proof-assistant verification.",
                       "Preserves zero sets over all integers, using the inherited source calibration separately."]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("result_directory", type=Path)
    parser.add_argument("--output", type=Path)
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--row-mode", action="store_true", help="check an integer row-basis certificate")
    group.add_argument("--affine-mode", action="store_true", help="check a unit affine projection certificate")
    args = parser.parse_args()
    routine = audit_affine if args.affine_mode else audit_rows if args.row_mode else audit
    report = routine(args.source, args.result_directory)
    encoded = canonical(report)
    if args.output:
        args.output.write_bytes(encoded)
    print(encoded.decode(), end="")


if __name__ == "__main__":
    main()
