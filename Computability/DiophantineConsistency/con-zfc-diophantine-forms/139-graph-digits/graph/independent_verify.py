#!/usr/bin/env python3
"""Independent checker for a block-incidence quartic certificate.

This file imports no producer or inherited verifier.  It checks a direct
certificate from source rows to the final polynomial; it does not need to
trust the optimizer's merge history or its graph-layout choices.  All
required checks use explicit exceptions and remain enabled with python -O.

Usage: python3 independent_verify.py SOURCE_JSON CANDIDATE_DIR [--output FILE]
       [--negative-controls]
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
from collections import Counter, defaultdict
from pathlib import Path


class CertificateError(ValueError):
    """A claimed finite identity or structural condition is false."""


def need(condition, message):
    if not condition:
        raise CertificateError(message)


def isint(value):
    return isinstance(value, int) and not isinstance(value, bool)


def addto(poly, monomial, coefficient):
    if coefficient:
        value = poly.get(monomial, 0) + coefficient
        if value:
            poly[monomial] = value
        else:
            poly.pop(monomial, None)


def addscaled(target, source, scale=1):
    for monomial, coefficient in source.items():
        addto(target, monomial, scale * coefficient)


def multiply(first, second):
    result = {}
    for monomial_a, coefficient_a in first.items():
        for monomial_b, coefficient_b in second.items():
            addto(result, tuple(sorted(monomial_a + monomial_b)),
                  coefficient_a * coefficient_b)
    return result


def parse_terms(terms, count, *, degree=None, unit=False, unique=False):
    need(isinstance(terms, list), "terms must be an array")
    result = {}
    seen = set()
    for term in terms:
        need(isinstance(term, list) and len(term) == 2, "malformed term")
        coefficient, factors = term
        need(isint(coefficient) and coefficient != 0, "bad coefficient")
        need(not unit or abs(coefficient) == 1, "nonunit occurrence")
        need(isinstance(factors, list), "factors must be an array")
        need(all(isint(i) and 0 <= i < count for i in factors),
             "factor outside declared variables")
        need(degree is None or len(factors) <= degree, "degree bound failed")
        key = tuple(sorted(factors))
        need(not unique or (key not in seen and factors == list(key)),
             "polynomial is not a collected canonical coefficient list")
        seen.add(key)
        addto(result, key, coefficient)
    return result


def substitute(poly, values):
    result = {}
    for monomial, coefficient in poly.items():
        term = {(): coefficient}
        for variable in monomial:
            term = multiply(term, values[variable])
        addscaled(result, term)
    return result


def evaluate(poly, point):
    result = 0
    for monomial, coefficient in poly.items():
        term = coefficient
        for variable in monomial:
            term *= point[variable]
        result += term
    return result


def normalize_check(source, normalization):
    need(source.get("domain") == "unrestricted integers",
         "source domain is not unrestricted integers")
    need(source.get("polynomial") == "sum(square(row) for row in residuals)",
         "source equation does not declare a sum of residual squares")
    original_count = len(source["variables"])
    need(normalization["original_variables"] == original_count,
         "source dimension mismatch")
    original_rows = [parse_terms(row["terms"], original_count, degree=2)
                     for row in source["residuals"]]
    variables = normalization["variables"]
    count = len(variables)
    need(count >= original_count, "normalization loses original coordinates")
    meanings = []
    constant_count = 0
    scale_count = 0
    for i, var in enumerate(variables):
        kind = var.get("kind")
        if i < original_count:
            need(kind == "original" and var.get("source_index") == i,
                 "original coordinate is not preserved literally")
            meanings.append({(i,): 1})
        elif kind == "constant":
            value = var.get("value")
            need(isint(value) and value > 1, "invalid literal constant")
            meanings.append({(): value})
            constant_count += 1
        elif kind == "scale":
            coefficient, variable = var.get("coefficient"), var.get("variable")
            need(isint(coefficient) and coefficient > 1,
                 "invalid normalized scale")
            need(isint(variable) and 0 <= variable < original_count,
                 "scale does not refer to an original coordinate")
            meanings.append({(variable,): coefficient})
            scale_count += 1
        else:
            raise CertificateError("unknown normalized coordinate kind")
    need(normalization.get("constant_count") == constant_count,
         "wrong normalized constant count")
    need(normalization.get("scale_count") == scale_count,
         "wrong normalized scale count")

    rows = []
    definitions = set()
    source_indices = set()
    for row in normalization["rows"]:
        poly = parse_terms(row["terms"], count, degree=2, unit=True)
        rows.append(poly)
        pulled = substitute(poly, meanings)
        kind = row.get("kind")
        if kind in ("constant", "scale"):
            # There must be exactly one new highest-index coordinate with
            # coefficient +1, appearing nowhere else in its definition.
            used = [i for monomial in poly for i in monomial]
            need(used, "empty defining row")
            target = max(used)
            need(target >= original_count and target not in definitions,
                 "missing, duplicate, or backward definition")
            need(poly.get((target,)) == 1,
                 "definition is not monic in its new coordinate")
            need(all(target not in monomial or monomial == (target,)
                     for monomial in poly), "nonlinear defining coordinate")
            need(variables[target]["kind"] == kind,
                 "defining-row coordinate kind mismatch")
            if kind == "constant":
                need(row.get("value") == variables[target]["value"],
                     "literal constant annotation mismatch")
            else:
                need(row.get("coefficient") == variables[target]["coefficient"]
                     and row.get("variable") == variables[target]["variable"],
                     "scale annotation mismatch")
            need(not pulled, "claimed normalization definition is false")
            definitions.add(target)
        elif kind == "source":
            index = row.get("source_row")
            need(isint(index) and 0 <= index < len(original_rows)
                 and index not in source_indices,
                 "source-row index missing or repeated")
            need(pulled == original_rows[index],
                 "normalized source row does not equal the source row")
            source_indices.add(index)
        else:
            raise CertificateError("unknown normalized row kind")
    need(definitions == set(range(original_count, count)),
         "not every new normalized coordinate is uniquely defined")
    need(source_indices == set(range(len(original_rows))),
         "not every source equation is retained exactly once")
    return original_rows, rows, meanings


def verify_data(source, polynomial, certificate, *, numeric_controls=True):
    need(polynomial.get("domain") == "unrestricted integers",
         "final domain is not unrestricted integers")
    original_rows, normalized_rows, meanings = normalize_check(
        source, certificate["normalization"])
    variables = polynomial["variables"]
    variable_count = len(variables)
    normalized_count = len(meanings)
    labels = {}
    flow_variables = set()
    for i, variable in enumerate(variables):
        kind = variable.get("kind")
        if kind == "flow":
            flow_variables.add(i)
        elif kind in ("logical_alias", "equality_dummy", "unit_dummy"):
            label = variable.get("normalized_variable")
            need(label is None or (isint(label) and 0 <= label < normalized_count),
                 "invalid alias label")
            need(kind != "equality_dummy" or label is not None,
                 "ordinary equality dummy is a unit coordinate")
            need(kind != "unit_dummy" or label is None,
                 "unit dummy is an ordinary coordinate")
            labels[i] = label
        else:
            raise CertificateError("unknown final coordinate kind")

    # A complete partition, not merely the labels of source factors, is
    # essential: unconstrained aliases could otherwise create false zeros.
    class_members = set()
    class_labels = set()
    cycles = certificate["equality_cycles"]
    for cycle in cycles:
        label, aliases = cycle["normalized_variable"], cycle["aliases"]
        method = cycle.get("method", "cycle")
        need(isint(label) and 0 <= label < normalized_count
             and label not in class_labels, "duplicate logical class")
        need(isinstance(aliases, list), "equality aliases must be an array")
        if method == "quartic_pair":
            need(len(aliases) == 2, "quartic pair must have exactly two aliases")
        else:
            need(method == "cycle" and (len(aliases) == 1 or len(aliases) >= 3),
                 "an equality cycle must have one or at least three vertices")
        need(len(set(aliases)) == len(aliases), "repeated equality-cycle vertex")
        for alias in aliases:
            need(isint(alias) and alias in labels and labels[alias] == label,
                 "alias in the wrong logical class")
            need(alias not in class_members, "overlapping logical classes")
            class_members.add(alias)
        class_labels.add(label)
    need(class_labels == set(range(normalized_count)),
         "a normalized coordinate has no surviving alias")
    units = certificate["unit_path"]
    need(isinstance(units, list) and len(units) >= 2 and len(set(units)) == len(units),
         "unit path has fewer than two distinct vertices")
    for alias in units:
        need(isint(alias) and alias in labels and labels[alias] is None,
             "ordinary coordinate in the unit path")
    need(class_members | set(units) == set(labels)
         and not (class_members & set(units)), "alias partition is incomplete")

    vertices = certificate["vertices"]
    vertex_count = len(vertices)
    hubs = certificate["hub_vertices"]
    row_blocks = certificate["row_blocks"]
    need(len(row_blocks) == len(normalized_rows), "row-block count mismatch")
    blocks = [hubs] + row_blocks
    block_of = {}
    for block_index, block in enumerate(blocks):
        need(isinstance(block, list) and block, "empty vertex block")
        for vertex in block:
            need(isint(vertex) and 0 <= vertex < vertex_count
                 and vertex not in block_of, "invalid or overlapping vertex blocks")
            block_of[vertex] = block_index
            expected_kind = "hub" if block_index == 0 else "row"
            need(vertices[vertex].get("kind") == expected_kind,
                 "vertex kind disagrees with block partition")
            if block_index:
                need(vertices[vertex].get("row") == block_index - 1,
                     "row vertex annotation disagrees with its block")
    need(set(block_of) == set(range(vertex_count)), "vertex partition is incomplete")

    edges = certificate["edges"]
    divergences = [dict() for _ in vertices]
    prescribed_divergences = [dict() for _ in vertices]
    logical_block_sums = [dict() for _ in blocks]
    free_by_block = [[] for _ in blocks]
    flow_used = set()
    edge_monomials = []
    for edge_index, edge in enumerate(edges):
        tail, head = edge.get("tail"), edge.get("head")
        need(isint(tail) and isint(head) and tail in block_of and head in block_of,
             "edge endpoint outside graph")
        coefficient = edge.get("coefficient")
        need(isint(coefficient) and abs(coefficient) == 1, "nonunit edge coefficient")
        factors = edge.get("monomial")
        need(isinstance(factors, list) and all(isint(i) and 0 <= i < variable_count
                                               for i in factors), "bad edge monomial")
        monomial = tuple(sorted(factors))
        edge_monomials.append(monomial)
        addto(divergences[tail], monomial, coefficient)
        addto(divergences[head], monomial, -coefficient)
        if edge.get("kind") == "free":
            need(len(factors) == 1 and factors[0] in flow_variables,
                 "free edge does not carry a declared flow coordinate")
            variable = factors[0]
            need(variable not in flow_used, "free-flow coordinate is reused")
            flow_used.add(variable)
            need(tail != head and block_of[tail] == block_of[head],
                 "free edge is a loop or crosses blocks")
            free_by_block[block_of[tail]].append(edge_index)
        elif edge.get("kind") == "prescribed":
            need(len(factors) <= 2 and all(i in labels for i in factors),
                 "prescribed edge is not an alias product of degree at most two")
            logical = tuple(sorted(labels[i] for i in factors if labels[i] is not None))
            addto(logical_block_sums[block_of[tail]], logical, coefficient)
            addto(logical_block_sums[block_of[head]], logical, -coefficient)
            addto(prescribed_divergences[tail], logical, coefficient)
            addto(prescribed_divergences[head], logical, -coefficient)
        else:
            raise CertificateError("unknown edge kind")
    need(flow_used == flow_variables, "flow-coordinate declaration is incomplete")
    for i, row in enumerate(normalized_rows):
        need(logical_block_sums[i + 1] == row,
             "prescribed edges do not reproduce a normalized source row")
    expected_hub = {}
    for row in normalized_rows:
        addscaled(expected_hub, row, -1)
    need(logical_block_sums[0] == expected_hub,
         "hub balance is not minus the sum of normalized rows")

    # Root every internal tree independently; no global simplicity assumption
    # is used, so parallel prescribed edges are allowed.
    tree_orders = []
    for block_index, block in enumerate(blocks):
        internal = free_by_block[block_index]
        need(len(internal) == len(block) - 1, "wrong internal-tree edge count")
        neighbors = defaultdict(list)
        for edge_index in internal:
            edge = edges[edge_index]
            neighbors[edge["tail"]].append((edge["head"], edge_index))
            neighbors[edge["head"]].append((edge["tail"], edge_index))
        root = block[0]
        parent = {root: None}
        order = [root]
        for vertex in order:
            for other, edge_index in neighbors[vertex]:
                if other not in parent:
                    parent[other] = (vertex, edge_index)
                    order.append(other)
        need(set(parent) == set(block), "internal free edges are not a spanning tree")
        tree_orders.append((root, order, parent))

    # Exact coefficient expansion of twice the energy, including every
    # collision caused by alias reuse and graph adjacency.
    twice_energy = {}
    for divergence in divergences:
        terms = list(divergence.items())
        for i, (monomial_a, coefficient_a) in enumerate(terms):
            addto(twice_energy, tuple(sorted(monomial_a + monomial_a)), coefficient_a ** 2)
            for monomial_b, coefficient_b in terms[i + 1:]:
                addto(twice_energy, tuple(sorted(monomial_a + monomial_b)),
                      2 * coefficient_a * coefficient_b)
    need(all(coefficient % 2 == 0 for coefficient in twice_energy.values()),
         "half-incidence energy has a nonintegral coefficient")
    energy = {monomial: coefficient // 2 for monomial, coefficient in twice_energy.items()}
    # With quartic equality penalties, energy terms can collide with the
    # penalties.  Only the height of their completely collected SUM matters.
    expanded = dict(energy)
    for cycle in cycles:
        aliases = cycle["aliases"]
        if cycle.get("method", "cycle") == "quartic_pair":
            # a^4+b^4-a^3*b-a*b^3 = (a-b)^2*(a^2+a*b+b^2).
            # This is nonnegative over R and vanishes exactly when a=b.
            first, second = aliases
            addto(expanded, (first,) * 4, 1)
            addto(expanded, (second,) * 4, 1)
            addto(expanded, tuple(sorted((first, first, first, second))), -1)
            addto(expanded, tuple(sorted((first, second, second, second))), -1)
        elif len(aliases) >= 3:
            for i, alias in enumerate(aliases):
                addto(expanded, (alias, alias), 1)
                addto(expanded, tuple(sorted((alias, aliases[(i + 1) % len(aliases)]))), -1)
    addto(expanded, (), 1)
    for alias in units:
        addto(expanded, (alias, alias), 1)
    addto(expanded, (units[0],), -1)
    addto(expanded, (units[-1],), -1)
    for first, second in zip(units, units[1:]):
        addto(expanded, tuple(sorted((first, second))), -1)
    literal = parse_terms(polynomial["terms"], variable_count, degree=4,
                          unit=True, unique=True)
    need(expanded == literal, "literal polynomial differs from the complete certified energy")
    need(all(abs(coefficient) == 1 for coefficient in literal.values()),
         "final coefficient height is not one")
    need(literal.get(()) == 1, "final constant is not one")
    need({variable for monomial in literal for variable in monomial}
         == set(range(variable_count)), "a declared final coordinate is unused")
    metrics = {
        "variables": variable_count,
        "source_variables": len(source["variables"]),
        "source_rows": len(original_rows),
        "normalized_variables": normalized_count,
        "normalized_rows": len(normalized_rows),
        "hubs": len(hubs),
        "flow_variables": len(flow_variables),
        "unit_coordinates": len(units),
        "equality_dummies": sum(v["kind"] == "equality_dummy" for v in variables),
        "energy_monomials": len(energy),
        "energy_coefficient_height": max(map(abs, energy.values()), default=0),
        "monomials": len(literal),
        "degree": max(map(len, literal)),
        "individual_degree": max(max(Counter(m).values(), default=0) for m in literal),
        "coefficient_height": max(map(abs, literal.values())),
        "constant": literal.get((), 0),
        "positive_coefficients": sum(c > 0 for c in literal.values()),
        "negative_coefficients": sum(c < 0 for c in literal.values()),
    }
    for key, value in metrics.items():
        if key in polynomial.get("metrics", {}):
            need(polynomial["metrics"][key] == value, "false metric: " + key)
    need(metrics["degree"] == 4, "the released polynomial is not exactly quartic")

    # Construct the canonical lift symbolically in the ORIGINAL variables.
    # Tree leaf elimination proves its divergences are the exact original
    # residuals at block roots and zero elsewhere, even away from zeros.
    lifted = [None] * variable_count
    for alias, label in labels.items():
        lifted[alias] = {(): 1} if label is None else meanings[label]
    pulled_divergences = [substitute(divergence, meanings)
                          for divergence in prescribed_divergences]
    for block_index, (root, order, parent) in enumerate(tree_orders):
        for vertex in reversed(order[1:]):
            other, edge_index = parent[vertex]
            edge = edges[edge_index]
            sign_at_child = edge["coefficient"] * (1 if edge["tail"] == vertex else -1)
            flow = {monomial: -sign_at_child * coefficient
                    for monomial, coefficient in pulled_divergences[vertex].items()}
            lifted[edge["monomial"][0]] = flow
            addscaled(pulled_divergences[other], pulled_divergences[vertex])
            pulled_divergences[vertex] = {}
        expected = substitute(logical_block_sums[block_index], meanings)
        need(pulled_divergences[root] == expected,
             "symbolic canonical flow lift has a false root divergence")
    need(all(value is not None for value in lifted), "canonical lift omits a coordinate")
    roots = {root for root, _, _ in tree_orders}
    need(all(not poly for i, poly in enumerate(pulled_divergences) if i not in roots),
         "a nonroot divergence survived the canonical lift")

    controls = []
    if numeric_controls:
        count = len(source["variables"])
        points = [[0] * count, [(-1 if i % 2 else 1) for i in range(count)],
                  [((i * i + 3 * i + 1) % 7) - 3 for i in range(count)]]
        for case, point in enumerate(points):
            target = [evaluate(poly, point) for poly in lifted]
            residuals = [evaluate(row, point) for row in original_rows]
            doubled_expected = sum(value * value for value in residuals) + sum(residuals) ** 2
            need(doubled_expected % 2 == 0, "off-zero identity is not integral")
            actual = evaluate(literal, target)
            need(2 * actual == doubled_expected, "off-zero energy identity failed")
            controls.append({"case": case, "value_sha256": hashlib.sha256(
                str(actual).encode("ascii")).hexdigest(), "value_bits": actual.bit_length()})
    return {"status": "pass", "metrics": metrics,
            "exact_checks": ["monic triangular normalization", "every source residual restored",
                             "complete alias and unit partitions", "all logical block balances",
                             "unique integral internal tree flows", "full half-energy coefficient expansion",
                             "literal polynomial equality", "height one and degree four",
                             "symbolic canonical lift at every original input"],
            "off_zero_numeric_controls": controls}


def negative_controls(source, polynomial, certificate):
    mutations = []

    def add(name, mutate):
        s, p, c = copy.deepcopy(source), copy.deepcopy(polynomial), copy.deepcopy(certificate)
        mutate(s, p, c)
        try:
            verify_data(s, p, c, numeric_controls=False)
        except (CertificateError, KeyError, TypeError, IndexError) as error:
            mutations.append({"mutation": name, "rejected": True, "reason": str(error)})
        else:
            raise CertificateError("negative control was accepted: " + name)

    def alter_constant(s, p, c):
        term = next(term for term in p["terms"] if not term[1])
        term[0] = -term[0]
    add("final constant changed", alter_constant)

    def alter_source(s, p, c):
        row = next(row for row in c["normalization"]["rows"] if row["kind"] == "source")
        row["terms"][0][0] *= -1
    add("normalized source coefficient reversed", alter_source)

    def alter_edge(s, p, c):
        edge = next(edge for edge in c["edges"] if edge["kind"] == "prescribed")
        edge["coefficient"] *= -1
    add("prescribed incidence reversed", alter_edge)

    def reuse_flow(s, p, c):
        edges = [edge for edge in c["edges"] if edge["kind"] == "free"]
        need(len(edges) >= 2, "negative-control fixture has too few flows")
        edges[1]["monomial"] = edges[0]["monomial"][:]
    add("flow variable reused on another edge", reuse_flow)

    def alter_alias(s, p, c):
        cycle = c["equality_cycles"][0]
        alias = cycle["aliases"][0]
        p["variables"][alias]["normalized_variable"] = None
    add("ordinary alias relabeled as a unit", alter_alias)
    return mutations


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("candidate", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--negative-controls", action="store_true")
    args = parser.parse_args()
    polynomial_path = args.candidate / "polynomial.json"
    certificate_path = args.candidate / "certificate.json"
    source = json.loads(args.source.read_text())
    polynomial = json.loads(polynomial_path.read_text())
    certificate = json.loads(certificate_path.read_text())
    result = verify_data(source, polynomial, certificate)
    if args.negative_controls:
        result["negative_controls"] = negative_controls(source, polynomial, certificate)
    result["input_sha256"] = {"source": digest(args.source),
                              "polynomial": digest(polynomial_path),
                              "certificate": digest(certificate_path)}
    result["checker_sha256"] = digest(Path(__file__))
    result["scope"] = ("Finite exact algebra and graph certificates; the source system's "
                       "Con(ZFC) calibration is inherited, not established by these checks.")
    encoded = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(encoded)
    print(encoded, end="")


if __name__ == "__main__":
    main()
