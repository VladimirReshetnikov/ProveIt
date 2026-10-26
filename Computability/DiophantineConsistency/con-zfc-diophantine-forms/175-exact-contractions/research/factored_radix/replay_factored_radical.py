"""Independently verify the five integral projections from 224 to 219 variables.

Uses only Python's standard library. No constructor or external certificate is
imported. Each shear is inverted on every row, each unit-pivot restoration is
checked, each row operation is reversed, and the entire endpoint is compared.
Checks use exceptions and remain active under python -O.
"""
import argparse
from collections import defaultdict
import copy
import hashlib
import json
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def plus(left, right, multiplier=1):
    result = dict(left)
    for monomial, coefficient in right.items():
        result[monomial] = result.get(monomial, 0) + multiplier * coefficient
        if not result[monomial]:
            del result[monomial]
    return result


def multiply(left, right):
    result = defaultdict(int)
    for monomial, coefficient in left.items():
        for other, value in right.items():
            result[tuple(sorted(monomial + other))] += coefficient * value
    return {m: a for m, a in result.items() if a}


def substitute(polynomial, index, replacement):
    result = {}
    for monomial, coefficient in polynomial.items():
        term = {(): coefficient}
        for variable in monomial:
            term = multiply(term, replacement if variable == index else {(variable,): 1})
        result = plus(result, term)
    return result


def unpack(terms, size):
    result = {}
    for coefficient, indices in terms:
        require(type(coefficient) is int and coefficient != 0, "noninteger/zero coefficient")
        require(all(type(i) is int and 0 <= i < size for i in indices), "invalid variable index")
        monomial = tuple(indices)
        require(tuple(sorted(monomial)) == monomial and monomial not in result,
                "noncanonical monomial")
        result[monomial] = coefficient
    return result


def packed(polynomial):
    return [[a, list(m)] for m, a in sorted(polynomial.items())]


def shear(rows, pivot, direction, sign):
    for index, coefficient in direction:
        if index != pivot:
            replacement = {(index,): 1, (pivot,): sign * coefficient}
            rows = [substitute(row, index, replacement) for row in rows]
    return rows


def audit(source, certificate, endpoint):
    require(source["domain"] == "Z", "source must use unrestricted integers")
    require(len(source["variables"]) == 224 and len(source["residuals"]) == 161,
            "unexpected source dimensions")
    require(len(certificate["steps"]) == 6, "expected five projections and row operations")
    current = copy.deepcopy(source)
    ledger = []
    operation_count = 0
    for step_number, step in enumerate(certificate["steps"]):
        size = len(current["variables"])
        rows = [unpack(row["terms"], size) for row in current["residuals"]]
        if step_number < 5:
            require(step["kind"] == "radical", "expected radical step")
            pivot, deleted = step["pivot"], step["deleted_row"]
            require(type(pivot) is int and 0 <= pivot < size, "invalid pivot")
            require(type(deleted) is int and 0 <= deleted < len(rows), "invalid deleted row")
            direction = step["direction"]
            require(all(type(i) is int and 0 <= i < size and type(a) is int and a != 0
                        for i, a in direction), "invalid integral shear direction")
            require(len(dict(direction)) == len(direction), "repeated direction coordinate")
            require(dict(direction).get(pivot) == 1, "pivot direction coefficient must be one")
            transformed = shear(rows, pivot, direction, 1)
            require(shear(transformed, pivot, direction, -1) == rows, "shear inverse failed")
            require(all(pivot not in m or m == (pivot,) for row in transformed for m in row),
                    "nonlinear pivot occurrence after shear")
            slope = transformed[deleted].get((pivot,), 0)
            require(abs(slope) == 1, "deleted row has no unit pivot")
            restoration = {m: -slope * a for m, a in transformed[deleted].items()
                           if m != (pivot,)}
            require(restoration == unpack(step["replacement"], size), "restoration differs")
            require(not substitute(transformed[deleted], pivot, restoration),
                    "deleted row is not identically zero after restoration")
            new_rows = []
            for row_number, row in enumerate(transformed):
                if row_number == deleted:
                    continue
                value = substitute(row, pivot, restoration)
                require(all(pivot not in m for m in value), "projected pivot survives")
                require(all(len(m) <= 3 for m in value), "residual degree exceeds three")
                value = {tuple(i - (i > pivot) for i in m): a for m, a in value.items()}
                new_rows.append(dict(current["residuals"][row_number], terms=packed(value)))
            del current["variables"][pivot]
            current["residuals"] = new_rows
            ledger.append({"step": step_number + 1, "pivot": pivot, "deleted_row": deleted,
                           "unit_slope": slope, "shear_inverse_checked": True,
                           "restoration_checked": True, "variables": size - 1,
                           "residuals": len(new_rows)})
        else:
            require(step["kind"] == "row_operations", "expected final row operations")
            require(step.get("skipped_parent_operations") == 0, "unexpected skipped operations")
            before = copy.deepcopy(rows)
            operations = step["operations"]
            require(len(operations) == 38, "expected 38 row operations")
            for i, j, coefficient in operations:
                require(type(i) is int and type(j) is int and 0 <= i < len(rows)
                        and 0 <= j < len(rows) and i != j, "invalid row shear")
                require(type(coefficient) is int, "noninteger row multiplier")
                rows[i] = plus(rows[i], rows[j], coefficient)
            restored = copy.deepcopy(rows)
            for i, j, coefficient in reversed(operations):
                restored[i] = plus(restored[i], restored[j], -coefficient)
            require(restored == before, "row-operation inverse failed")
            current["residuals"] = [dict(row, terms=packed(value))
                                    for row, value in zip(current["residuals"], rows)]
            operation_count = len(operations)
    current["variant"] = "factored_radix_with_rechecked_radical_maps"
    require(current == endpoint, "full endpoint including metadata differs")
    require(len(current["variables"]) == 219 and len(current["residuals"]) == 156,
            "unexpected endpoint dimensions")
    rows = [unpack(row["terms"], 219) for row in current["residuals"]]
    live = {i for row in rows for m in row for i in m}
    require(live == set(range(219)), "unused endpoint variable")
    expanded = {}
    for row in rows:
        expanded = plus(expanded, multiply(row, row))
    residual_degree = max(len(m) for row in rows for m in row)
    degree = max(map(len, expanded))
    require(residual_degree == 3 and degree == 6, "unexpected exact endpoint degree")
    return {"status": "passed", "variables": 219, "live_variables": len(live),
            "residuals": len(rows), "residual_degree": residual_degree, "degree": degree,
            "expanded_terms": len(expanded), "height": max(map(abs, expanded.values())),
            "five_shear_inverses_checked": True, "unit_restorations_checked": 5,
            "row_operations": operation_count, "row_operation_inverse_checked": True,
            "full_endpoint_and_metadata_checked": True, "steps": ledger}


def mutation_controls(source, certificate, endpoint):
    mutations = []
    bad = copy.deepcopy(certificate)
    bad["steps"][0]["direction"][1][1] += 2
    mutations.append(("nontrivial_shear_coefficient", bad, endpoint))
    bad = copy.deepcopy(certificate)
    bad["steps"][1]["replacement"][0][0] += 1
    mutations.append(("unit_pivot_restoration_coefficient", bad, endpoint))
    bad = copy.deepcopy(certificate)
    bad["steps"][5]["operations"][0][2] += 1
    mutations.append(("row_operation_coefficient", bad, endpoint))
    bad = copy.deepcopy(endpoint)
    bad["residuals"][0]["terms"][0][0] -= 1
    mutations.append(("endpoint_coefficient", certificate, bad))
    results = []
    for name, mutated_certificate, mutated_endpoint in mutations:
        try:
            audit(source, mutated_certificate, mutated_endpoint)
        except ValueError as error:
            results.append({"mutation": name, "rejected": True, "reason": str(error)})
        else:
            raise ValueError("mutation control was accepted: " + name)
    return results


def main():
    here = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=here / "factored_radix224/equation.json")
    parser.add_argument("--certificate", type=Path, default=here / "factored_radical219/certificate.json")
    parser.add_argument("--equation", type=Path, default=here / "factored_radical219/equation.json")
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()
    raw = [path.read_bytes() for path in (args.source, args.certificate, args.equation)]
    source, certificate, endpoint = [json.loads(data) for data in raw]
    receipt = audit(source, certificate, endpoint)
    receipt["mutation_controls"] = mutation_controls(source, certificate, endpoint)
    for name, data in zip(("source", "certificate", "endpoint"), raw):
        receipt[name + "_sha256"] = hashlib.sha256(data).hexdigest()
    if args.receipt:
        args.receipt.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print(json.dumps(receipt, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
