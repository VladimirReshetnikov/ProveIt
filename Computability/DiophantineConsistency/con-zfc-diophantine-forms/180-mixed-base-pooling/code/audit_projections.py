#!/usr/bin/env python3
"""Independent exact checker for the monic-projection pooling circuits.

Uses only Python's standard library. It imports neither build.py nor
compile_projection.py. Exact symbolic expression matching, not modular
sampling, proves that every output is the stated substituted expression.
The modular evaluations are additional cross-checks. Nonzero derivatives
modulo a fixed prime are exact certificates of genuine input dependence.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import json
import random
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCE_PIN = "e5e14bc0bbabb625f78ce57017fbdb336c4a65c5877f517142c399769992ff39"


class Invalid(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise Invalid(message)


def load(path):
    return json.loads(path.read_text())


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def integer(x):
    return type(x) is int


def polynomial(terms, dimension):
    require(isinstance(terms, list), "A term array is required")
    result = {}
    for term in terms:
        require(isinstance(term, list) and len(term) == 2, "Malformed term")
        coefficient, monomial = term
        require(integer(coefficient) and coefficient != 0, "Noninteger or zero coefficient")
        require(isinstance(monomial, list), "Malformed monomial")
        require(all(integer(i) and 0 <= i < dimension for i in monomial), "Unknown polynomial variable")
        require(monomial == sorted(monomial), "Unsorted monomial")
        key = tuple(monomial)
        require(key not in result, "Duplicate monomial")
        result[key] = coefficient
    return result


def dependencies(definitions):
    return {v: {i for m in p for i in m if i in definitions}
            for v, p in definitions.items()}


def acyclic_order(definitions):
    """Kahn's algorithm, independent of the producer's recursive resolver."""
    deps = dependencies(definitions)
    order = []
    done = set()
    while len(done) < len(definitions):
        ready = sorted(v for v in definitions if v not in done and deps[v] <= done)
        require(bool(ready), "Cyclic monic definitions")
        order.extend(ready)
        done.update(ready)
    return order


class Expressions:
    """Interned exact integer expression trees.

    Normalization uses only constant arithmetic, zero/unit laws, conversion
    of subtraction to addition of the negative, and commutativity. There is
    no probabilistic hashing and no assumption about polynomial identity.
    Equal interned identifiers are structurally identical expressions after
    these valid ring identities. Python's tuple dictionary resolves hash
    collisions by exact equality.
    """

    def __init__(self):
        self.data = []
        self.ids = {}

    def make(self, key):
        if key not in self.ids:
            self.ids[key] = len(self.data)
            self.data.append(key)
        return self.ids[key]

    def number(self, n):
        return self.make(("integer", n))

    def variable(self, v):
        return self.make(("coordinate", v))

    def constant(self, a):
        item = self.data[a]
        return item[1] if item[0] == "integer" else None

    def product(self, a, b):
        ca, cb = self.constant(a), self.constant(b)
        if ca == 0 or cb == 0:
            return self.number(0)
        if ca == 1:
            return b
        if cb == 1:
            return a
        if ca is not None and cb is not None:
            return self.number(ca * cb)
        return self.make(("product", min(a, b), max(a, b)))

    def addition(self, a, b):
        ca, cb = self.constant(a), self.constant(b)
        if ca == 0:
            return b
        if cb == 0:
            return a
        if ca is not None and cb is not None:
            return self.number(ca + cb)
        return self.make(("sum", min(a, b), max(a, b)))

    def difference(self, a, b):
        return self.addition(a, self.product(self.number(-1), b))

    def sum_list(self, items):
        result = self.number(0)
        for item in items:
            result = self.addition(result, item)
        return result

    def product_list(self, items):
        result = self.number(1)
        for item in items:
            result = self.product(result, item)
        return result

    def sparse(self, p, coordinates):
        return self.sum_list([
            self.product(self.number(coefficient),
                         self.product_list([coordinates[i] for i in monomial]))
            for monomial, coefficient in sorted(p.items())
        ])


def verify_certificate(source, interface, certificate, profile):
    dimension = len(source["variables"])
    rows = [polynomial(r["terms"], dimension) for r in source["residuals"]]
    require(source["domain"] == "unrestricted integers", "Wrong source domain")
    require(certificate["schema"] == "monic-projection-v1", "Wrong certificate schema")
    require(certificate["source_sha256"] == SOURCE_PIN, "Unpinned certificate source")
    require(profile["source_sha256"] == SOURCE_PIN, "Unpinned profile source")
    require(not profile.get("weighted", False), "Weighted profile not licensed here")
    private = set(interface["deleted_variables"])
    retained = interface["retained_variables"]
    kept_rows = interface["retained_rows"]
    require(sorted(private | set(retained)) == list(range(dimension)) and not private.intersection(retained),
            "Source coordinate partition is not exact")
    require(sorted(interface["deleted_rows"] + kept_rows) == list(range(len(rows))),
            "Source row partition is not exact")
    require(certificate["pool_deleted_coordinates"] == interface["deleted_variables"], "Private-coordinate mismatch")
    require(certificate["pool_deleted_rows"] == interface["deleted_rows"], "Private-row mismatch")
    steps = certificate["steps"]
    require([{"row": s["row"], "variable": s["variable"]} for s in steps] == profile["steps"],
            "Profile/certificate step mismatch")
    definitions = {}
    removed = set()
    identity_checks = 0
    for step in steps:
        r, v, sign = step["row"], step["variable"], step["unit_coefficient"]
        require(integer(r) and r in kept_rows and r not in removed, "Missing, repeated or protected pivot row")
        require(integer(v) and v in retained and v not in definitions, "Missing, repeated or private pivot variable")
        require(sign in (-1, 1), "Nonunit coefficient")
        row = rows[r]
        require(row.get((v,)) == sign, "Unit coefficient differs from source")
        require(all(v not in monomial or monomial == (v,) for monomial in row),
                "Pivot occurs nonlinearly or in another monomial")
        definition = polynomial(step["definition"], dimension)
        required_definition = {m: -sign * c for m, c in row.items() if m != (v,)}
        require(definition == required_definition, "Incorrect monic restoration polynomial")
        require(not private.intersection(i for m in definition for i in m), "Private-coordinate dependency")
        definitions[v] = definition
        removed.add(r)
        identity_checks += 1
    order = acyclic_order(definitions)
    reported = certificate["resolution_order"]
    require(len(reported) == len(set(reported)) and set(reported) == set(definitions), "Incomplete resolution order")
    seen = set()
    deps = dependencies(definitions)
    for v in reported:
        require(deps[v] <= seen, "Invalid dependency order")
        seen.add(v)
    free = [v for v in retained if v not in definitions]
    remaining = [r for r in kept_rows if r not in removed]
    require(free == certificate["free_source_coordinates"], "Free-coordinate list mismatch or missing definition")
    require(remaining == certificate["retained_source_rows"], "Retained-row list mismatch")
    partition = certificate["partition"]
    require(isinstance(partition, list) and all(isinstance(g, list) and g for g in partition), "Empty pool partition")
    require(all(integer(i) for g in partition for i in g), "Noninteger block index")
    require(sorted(i for g in partition for i in g) == list(range(5)), "Incomplete or repeated block partition")
    require(partition == profile.get("partition", [[0, 1, 2, 3, 4]]), "Profile/certificate partition mismatch")
    return rows, definitions, order, free, remaining, partition, identity_checks


def validate_graph(circuit, variables):
    require(circuit["schema"] == "integer-polynomial-circuit-v1", "Wrong circuit schema")
    require(circuit["domain"] == "unrestricted integers", "Wrong circuit domain")
    require(circuit["variables"] == variables, "Wrong quantified variables or source map")
    nodes = circuit["nodes"]
    require(bool(nodes), "Empty graph")
    for i, node in enumerate(nodes):
        require(isinstance(node, list) and node, "Malformed node")
        if node[0] in ("const", "var"):
            require(len(node) == 2 and integer(node[1]), "Malformed leaf")
            if node[0] == "var":
                require(0 <= node[1] < len(variables), "Unknown circuit coordinate")
        else:
            require(len(node) == 3 and node[0] in ("+", "-", "*"), "Nonpolynomial operation")
            require(all(integer(j) and 0 <= j < i for j in node[1:]), "Forward, cyclic, or missing gate operand")
    output = circuit["output"]
    require(integer(output) and 0 <= output < len(nodes), "Invalid output")
    require(all(integer(i) and 0 <= i < len(nodes) for i in circuit["residual_outputs"]), "Invalid residual output")
    live = set()
    pending = [output]
    while pending:
        i = pending.pop()
        if i in live:
            continue
        live.add(i)
        if nodes[i][0] in ("+", "-", "*"):
            pending.extend(nodes[i][1:])
    require(live == set(range(len(nodes))), "Dead circuit gate")
    require(set(circuit["residual_outputs"]) <= live, "Residual is not in final output")
    return nodes


def match_expressions(source, interface, circuit, checked):
    rows, definitions, order, free, remaining, partition, _ = checked
    variables = [{**source["variables"][i], "source_index": i} for i in free]
    variables += [{"name": "mixed_pool.z" + str(i), "kind": "unrestricted integer"}
                  for i in range(len(partition))]
    nodes = validate_graph(circuit, variables)
    ex = Expressions()
    actual = []
    for node in nodes:
        if node[0] == "const":
            actual.append(ex.number(node[1]))
        elif node[0] == "var":
            actual.append(ex.variable(node[1]))
        elif node[0] == "+":
            actual.append(ex.addition(actual[node[1]], actual[node[2]]))
        elif node[0] == "-":
            actual.append(ex.difference(actual[node[1]], actual[node[2]]))
        else:
            actual.append(ex.product(actual[node[1]], actual[node[2]]))
    coordinates = {v: ex.variable(i) for i, v in enumerate(free)}
    for v in order:
        coordinates[v] = ex.sparse(definitions[v], coordinates)
    expected = [ex.sparse(rows[r], coordinates) for r in remaining]
    dimension = len(source["variables"])

    def expression(terms):
        return ex.sparse(polynomial(terms, dimension), coordinates)

    reqs = {r["request"]: r for r in interface["requests"]}
    moduli = []
    numerators = []
    for block in interface["blocks"]:
        base = expression(block["base"])
        moduli.append(expression(block["T"]))
        summands_h, summands_s = [], []
        for j in block["requests"]:
            request = reqs[j]
            output, pell_x, pell_y, shifted_x = [expression(request[k]) for k in ("m", "X", "Y", "D")]
            summands_h.append(ex.product(pell_y, ex.difference(output, pell_x)))
            difference = ex.difference(output, shifted_x)
            summands_s.append(ex.difference(ex.product(difference, difference), ex.product(pell_y, pell_y)))
        numerators.append(ex.difference(ex.sum_list(summands_s),
                                       ex.product_list([ex.number(2), base, ex.sum_list(summands_h)])))
    for index, blocks in enumerate(partition):
        terms = [ex.product_list([numerators[j]] + [moduli[h] for h in blocks if h != j])
                 for j in blocks]
        quotient = ex.variable(len(free) + index)
        expected.append(ex.difference(ex.sum_list(terms), ex.product_list([quotient] + [moduli[h] for h in blocks])))
    require(len(expected) == len(circuit["residual_outputs"]), "Wrong residual count")
    for i, (wanted, node) in enumerate(zip(expected, circuit["residual_outputs"])):
        require(wanted == actual[node], "Exact residual-expression mismatch at " + str(i))
    target = ex.sum_list([ex.product(r, r) for r in expected])
    require(target == actual[circuit["output"]], "Exact final sum-of-squares mismatch")
    return len(ex.data)


def scalar_polynomial(p, values, modulus):
    answer = 0
    for monomial, coefficient in p.items():
        term = coefficient
        for i in monomial:
            term = term * values[i] % modulus
        answer = (answer + term) % modulus
    return answer


def evaluate_graph(circuit, point, modulus):
    values = []
    for node in circuit["nodes"]:
        if node[0] == "const":
            value = node[1]
        elif node[0] == "var":
            value = point[node[1]]
        elif node[0] == "+":
            value = values[node[1]] + values[node[2]]
        elif node[0] == "-":
            value = values[node[1]] - values[node[2]]
        else:
            value = values[node[1]] * values[node[2]]
        values.append(value % modulus)
    return values


def modular_checks(source, interface, circuit, checked):
    rows, definitions, order, free, remaining, partition, _ = checked
    dimension = len(source["variables"])
    requests = {r["request"]: r for r in interface["requests"]}
    trials = []
    for modulus in (101, 1009, 1000003):
        for trial in range(4):
            rng = random.Random(23903 + 131 * trial + modulus)
            point = ([0] * len(circuit["variables"]) if trial == 0 else
                     [rng.randrange(-100, 101) for _ in circuit["variables"]])
            values = dict(zip(free, point))
            for v in order:
                values[v] = scalar_polynomial(definitions[v], values, modulus)
            for step in definitions:
                require(values[step] == scalar_polynomial(definitions[step], values, modulus), "Numerical restoration mismatch")
            residuals = [scalar_polynomial(rows[r], values, modulus) for r in remaining]

            def atom(terms):
                return scalar_polynomial(polynomial(terms, dimension), values, modulus)

            all_t, all_e = [], []
            for block in interface["blocks"]:
                h, s = 0, 0
                for j in block["requests"]:
                    r = requests[j]
                    m, x, y, d = (atom(r[k]) for k in ("m", "X", "Y", "D"))
                    h += y * (m - x)
                    s += (m - d) ** 2 - y ** 2
                all_e.append((s - 2 * atom(block["base"]) * h) % modulus)
                all_t.append(atom(block["T"]))
            for i, blocks in enumerate(partition):
                value = 0
                for j in blocks:
                    term = all_e[j]
                    for other in blocks:
                        if other != j:
                            term *= all_t[other]
                    value += term
                term = point[len(free) + i]
                for j in blocks:
                    term *= all_t[j]
                residuals.append((value - term) % modulus)
            actual = evaluate_graph(circuit, point, modulus)
            require([actual[i] for i in circuit["residual_outputs"]] == residuals, "Modular residual cross-check failed")
            expected = sum(r * r for r in residuals) % modulus
            require(actual[circuit["output"]] == expected, "Modular output cross-check failed")
            trials.append({"prime": modulus, "trial": trial, "output": expected})
    return trials


def univariate_add(left, right, sign=1):
    result = [0] * max(len(left), len(right))
    for i, value in enumerate(left):
        result[i] += value
    for i, value in enumerate(right):
        result[i] += sign * value
    while len(result) > 1 and result[-1] == 0:
        result.pop()
    return result


def univariate_multiply(left, right):
    result = [0] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        if a:
            for j, b in enumerate(right):
                if b:
                    result[i + j] += a * b
    while len(result) > 1 and result[-1] == 0:
        result.pop()
    return result


def degree_check(circuit, metrics):
    certificate = metrics["degree_certificate"]
    point = {int(i): v for i, v in certificate["point"].items()}
    require(set(point) <= set(range(len(circuit["variables"]))) and all(integer(v) for v in point.values()),
            "Invalid degree-witness point")
    upper, restrictions = [], []
    for node in circuit["nodes"]:
        if node[0] == "const":
            upper.append(0)
            restrictions.append([node[1]])
        elif node[0] == "var":
            upper.append(1)
            restrictions.append([0, point.get(node[1], 0)])
        else:
            op, a, b = node
            if op == "*":
                upper.append(upper[a] + upper[b])
                restrictions.append(univariate_multiply(restrictions[a], restrictions[b]))
            else:
                upper.append(max(upper[a], upper[b]))
                restrictions.append(univariate_add(restrictions[a], restrictions[b], 1 if op == "+" else -1))
    output = circuit["output"]
    degree = upper[output]
    require(degree == metrics["exact_total_degree"] == certificate["upper_degree"], "Wrong degree bound")
    require(len(restrictions[output]) - 1 == degree and restrictions[output][-1] != 0,
            "Highest homogeneous form not certified nonzero")
    require(restrictions[output][-1] == certificate["leading_value"], "Wrong exact leading value")
    residual_degrees = [upper[i] for i in circuit["residual_outputs"]]
    residual_tops = [restrictions[i][upper[i]] if upper[i] < len(restrictions[i]) else 0
                     for i in circuit["residual_outputs"]]
    require(residual_degrees == certificate["residual_degrees"], "Residual degree-bound mismatch")
    require(residual_tops == certificate["residual_leading_values"], "Residual top-value mismatch")
    return {"degree": degree, "exact_top_coefficient_on_reported_line": restrictions[output][-1],
            "method": "Complete exact univariate substitution x_i=point_i*t plus a syntactic global upper bound"}


def dependence_certificate(circuit):
    modulus = 1000003
    count = len(circuit["variables"])
    outstanding = set(range(count))
    witnesses = []
    for attempt in range(8):
        rng = random.Random(59113 + attempt)
        point = [rng.randrange(1, modulus) for _ in range(count)]
        values = evaluate_graph(circuit, point, modulus)
        adjoints = [0] * len(values)
        adjoints[circuit["output"]] = 1
        derivatives = [0] * count
        for i in reversed(range(len(values))):
            node, adjoint = circuit["nodes"][i], adjoints[i] % modulus
            if node[0] == "var":
                derivatives[node[1]] = (derivatives[node[1]] + adjoint) % modulus
            elif node[0] in ("+", "-", "*"):
                op, a, b = node
                if op == "*":
                    adjoints[a] = (adjoints[a] + adjoint * values[b]) % modulus
                    adjoints[b] = (adjoints[b] + adjoint * values[a]) % modulus
                else:
                    adjoints[a] = (adjoints[a] + adjoint) % modulus
                    adjoints[b] = (adjoints[b] + (adjoint if op == "+" else -adjoint)) % modulus
        covered = sorted(i for i in outstanding if derivatives[i])
        if covered:
            witnesses.append({"prime": modulus, "point": point,
                              "certified_coordinates": covered,
                              "nonzero_derivatives": {str(i): derivatives[i] for i in covered}})
            outstanding.difference_update(covered)
        if not outstanding:
            break
    require(not outstanding, "Could not certify genuine dependence on coordinates " + str(sorted(outstanding)))
    return {"all_inputs_genuinely_used": True, "witnesses": witnesses}


def require_rejection(action, description):
    try:
        action()
    except (Invalid, KeyError, IndexError) as error:
        return {"mutation": description, "rejected": True, "reason": str(error)}
    raise Invalid("Mutation was not rejected: " + description)


def mutation_checks(source, interface, certificate, profile, circuit, checked):
    results = []
    missing = copy.deepcopy(certificate)
    missing["steps"].pop()
    results.append(require_rejection(lambda: verify_certificate(source, interface, missing, profile), "missing definition"))
    nonunit = copy.deepcopy(certificate)
    nonunit["steps"][0]["unit_coefficient"] = 2
    results.append(require_rejection(lambda: verify_certificate(source, interface, nonunit, profile), "nonunit pivot"))
    wrong = copy.deepcopy(certificate)
    wrong["steps"][0]["definition"][0][0] += 1
    results.append(require_rejection(lambda: verify_certificate(source, interface, wrong, profile), "altered restoration coefficient"))
    # A monic two-row fixture x0=x1, x1=x0 is locally valid but has no
    # triangular inverse lift. It must be rejected by the cycle detector.
    cyclic = {0: {(1,): 1}, 1: {(0,): 1}}
    results.append(require_rejection(lambda: acyclic_order(cyclic), "cyclic locally monic definitions"))
    altered = copy.deepcopy(circuit)
    altered["nodes"][altered["output"]][0] = "-"
    results.append(require_rejection(lambda: match_expressions(source, interface, altered, checked), "altered final sum operation"))
    bad_leaf = copy.deepcopy(circuit)
    leaf = next(n for n in bad_leaf["nodes"] if n[0] == "var")
    leaf[1] = (leaf[1] + 1) % len(bad_leaf["variables"])
    results.append(require_rejection(lambda: match_expressions(source, interface, bad_leaf, checked), "altered coordinate leaf"))
    return results


def verify_endpoint(directory, source, interface):
    certificate = load(directory / "projection.json")
    profile = load(directory / "profile.json")
    circuit = load(directory / "circuit.json")
    metrics = load(directory / "METRICS.json")
    require(digest(directory / "circuit.json") == certificate["circuit_sha256"], "Circuit byte hash mismatch")
    checked = verify_certificate(source, interface, certificate, profile)
    expression_count = match_expressions(source, interface, circuit, checked)
    rows, definitions, order, free, remaining, partition, identities = checked
    require(metrics["variables"] == len(circuit["variables"]) == len(free) + len(partition), "Variable-count mismatch")
    require(metrics["residuals"] == len(circuit["residual_outputs"]) == len(remaining) + len(partition), "Residual-count mismatch")
    require(metrics["deleted_monic_coordinates"] == len(definitions), "Elimination-count mismatch")
    require(metrics["retained_source_residuals"] == len(remaining), "Source-residual-count mismatch")
    require(metrics["new_pool_residuals"] == len(partition), "Pool-residual-count mismatch")
    require(metrics["binary_operations"] == sum(n[0] in ("+", "-", "*") for n in circuit["nodes"]), "Operation-count mismatch")
    require(metrics["maximum_literal_integer"] == max(abs(n[1]) for n in circuit["nodes"] if n[0] == "const"), "Literal-height mismatch")
    degree = degree_check(circuit, metrics)
    require(degree["degree"] <= profile.get("degree_bound", degree["degree"]), "Profile degree limit exceeded")
    return {"endpoint": directory.name, "accepted": True,
            "source_sha256": SOURCE_PIN, "circuit_sha256": digest(directory / "circuit.json"),
            "projection_sha256": digest(directory / "projection.json"),
            "metrics_sha256": digest(directory / "METRICS.json"),
            "variables": len(circuit["variables"]), "residuals": len(circuit["residual_outputs"]),
            "binary_operations": metrics["binary_operations"],
            "exact_monic_identities": identities,
            "acyclic_inverse_lift": True,
            "exact_expression_nodes_compared": expression_count,
            "exact_residual_expression_identities": len(circuit["residual_outputs"]),
            "exact_sum_of_squares_identity": True,
            "degree": degree,
            "modular_cross_checks": modular_checks(source, interface, circuit, checked),
            "dependence": dependence_certificate(circuit),
            "mutations": mutation_checks(source, interface, certificate, profile, circuit, checked)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directories", nargs="*", type=Path)
    parser.add_argument("--output", type=Path, default=ROOT / "verification" / "PROJECTION_INDEPENDENT.json")
    args = parser.parse_args()
    require(digest(ROOT / "inputs" / "source216.json") == SOURCE_PIN, "Actual source bytes do not match the fixed pin")
    source = load(ROOT / "inputs" / "source216.json")
    interface = load(ROOT / "inputs" / "interface216.json")
    require(interface["source_sha256"] == SOURCE_PIN, "Interface source pin mismatch")
    directories = args.directories or sorted(p.parent for p in (ROOT / "equations").glob("*/projection.json"))
    require(bool(directories), "No projection endpoints found")
    results = []
    for directory in directories:
        result = verify_endpoint(directory, source, interface)
        results.append(result)
        print(json.dumps({"endpoint": result["endpoint"], "accepted": True,
                          "variables": result["variables"], "degree": result["degree"]["degree"],
                          "monic_identities": result["exact_monic_identities"],
                          "genuine_input_dependence": True}, sort_keys=True), flush=True)
    report = {"schema": "independent-monic-projection-audit-v1", "accepted": True,
              "checker_sha256": digest(Path(__file__)),
              "source_sha256": SOURCE_PIN,
              "interface_sha256": digest(ROOT / "inputs" / "interface216.json"),
              "producer_imported": False,
              "identity_method": "Exact interned expression comparison using only explicit valid integer-ring normalizations",
              "scope": "Finite monic elimination, acyclic restoration, literal circuit, counts, exact degree, and genuine input dependence; inherited unbounded arithmetic and ZFC calibration remain separate mathematical dependencies",
              "endpoints": results}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print("Wrote " + str(args.output), flush=True)


if __name__ == "__main__":
    main()
