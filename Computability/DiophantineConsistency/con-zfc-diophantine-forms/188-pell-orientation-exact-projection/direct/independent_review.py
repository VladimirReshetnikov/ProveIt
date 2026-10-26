#!/usr/bin/env python3
"""Independent exact review of the orientation source and polynomial graphs.

Python standard library only. No producer, optimizer, or search code is imported.
The graphs are verified at explicit source-coordinate expression boundaries;
their astronomically large fully expanded polynomials need not be collected.
"""
import argparse
import copy
import hashlib
import json
import math
from pathlib import Path


def need(condition, message):
    if not condition:
        raise ValueError(message)


def add(*polys):
    out = {}
    for p in polys:
        for mon, c in p.items():
            out[mon] = out.get(mon, 0) + c
    return {mon: c for mon, c in out.items() if c}


def scale(c, p):
    return {m: c * a for m, a in p.items() if c * a}


def multiply(a, b):
    out = {}
    for left, ca in a.items():
        for right, cb in b.items():
            key = tuple(sorted(left + right))
            out[key] = out.get(key, 0) + ca * cb
    return {m: c for m, c in out.items() if c}


def constant(c):
    return {(): c} if c else {}


def atom(i):
    return {(i,): 1}


def decode(terms):
    out = {}
    for c, mon in terms:
        need(type(c) is int and all(type(i) is int for i in mon), "noninteger polynomial data")
        key = tuple(sorted(mon))
        out[key] = out.get(key, 0) + c
    return {m: c for m, c in out.items() if c}


def product(items):
    answer = constant(1)
    for p in items:
        answer = multiply(answer, p)
    return answer


def read(path):
    return json.loads(Path(path).read_text())


def check_source(directory):
    parent_bytes = (directory / "parent206.json").read_bytes()
    parent = json.loads(parent_bytes)
    src = read(directory / "source206.json")
    cert = read(directory / "orientation_certificate.json")
    expected_hash = "7da179bedf0e072d01655aeb174516e94809294d67218b3db1c66a817f631e67"
    need(hashlib.sha256(parent_bytes).hexdigest() == expected_hash, "unexpected fixed source parent")
    need(len(parent["variables"]) == 206 and len(parent["residuals"]) == 145, "parent dimensions")
    need(src["variables"] == parent["variables"], "changed source coordinates")
    A = add(constant(1), atom(132))
    indices = [atom(0), add(atom(0), atom(2)), add(atom(8), constant(-1)),
               atom(9), atom(10), atom(11), atom(12), atom(4), atom(13),
               atom(14), atom(1), atom(15), scale(2, atom(16)), atom(93)]
    square_error, triangle_error, linear_error, sum_norms, delta = {}, {}, {}, {}, {}
    for j, k in enumerate(indices):
        d, y, z = 136 + 3*j, 137 + 3*j, 138 + 3*j
        Y = add(atom(y), constant(-1)) if j == 2 else atom(y)
        Z = add(atom(z), constant(1)) if j == 10 else atom(z)
        X = add(atom(d), Z)
        norm = add(multiply(X, X), scale(-1, multiply(Z, Z)), multiply(Y, Y), constant(-1))
        wire = add(Z, scale(-1, multiply(A, Y)))
        need(norm == decode(parent["residuals"][95+2*j]["terms"]), f"norm binding {j}")
        need(wire == decode(parent["residuals"][94+2*j]["terms"]), f"AY binding {j}")
        xm1 = add(X, constant(-1))
        e = add(Y, scale(-1, k))
        square_error = add(square_error, multiply(xm1, xm1), multiply(e, e))
        triangle_error = add(triangle_error, multiply(X, xm1), multiply(e, e))
        linear_error = add(linear_error, scale(-1, xm1), multiply(e, e))
        sum_norms = add(sum_norms, norm)
        delta = add(delta, xm1)
    MQ = multiply(atom(132), atom(193))
    old = add(square_error, scale(-1, sum_norms), scale(-1, MQ))
    triangle = add(triangle_error, scale(-1, sum_norms), scale(-1, MQ))
    linear = add(linear_error, scale(-1, MQ))
    need(old == decode(parent["residuals"][135]["terms"]), "old pooled orientation binding")
    new = decode(src["residuals"][135]["terms"])
    need(new in (triangle, linear), "new source is neither certified orientation form")
    mode = "linear" if new == linear else "triangular"
    need(new.get((142,)) == -1 and all(142 not in m for m in new if m != (142,)), "no unit pivot on root142")
    need(len(src["residuals"]) == len(parent["residuals"]), "source row count changed")
    for i in range(145):
        if i != 135:
            need(src["residuals"][i] == parent["residuals"][i], f"unexpected source change {i}")
    need([i for i, r in enumerate(parent["residuals"])
          if any(193 in m for c, m in r["terms"])] == [135], "hidden orientation quotient use")
    for i in [122, *range(125, 135), 138]:
        need(not any(142 in m or 193 in m for c, m in parent["residuals"][i]["terms"]),
             f"anchor circularity at row {i}")
    pool = read(directory / "factored_pool.json")
    bases = [decode(b["base"]) for b in pool["blocks"]]
    Ts = [decode(b["T"]) for b in pool["blocks"]]
    Es = [decode(b["E"]) for b in pool["blocks"]]
    need(len(bases) == 5 and len(pool["pool_coordinates"]) == 1, "pool arity")
    reconstructed = add(*[product([bases[i], Es[i], *Ts[:i], *Ts[i+1:]]) for i in range(5)],
                        scale(-1, product([atom(pool["pool_coordinates"][0]), *Ts])))
    need(reconstructed == decode(src["residuals"][-1]["terms"]), "factored pool does not equal full source")
    return src, pool, {"mode": mode, "parent_sha256": expected_hash,
                       "norm_and_wire_identities": 28, "unchanged_source_rows": 144,
                       "pooled_polynomial_terms": len(reconstructed)}


def graph_review(directory, graph, source, pool):
    nodes = graph["nodes"]
    source_n = len(source["variables"])
    rows = source["residuals"]
    inputs = graph["source_input_indices"]
    need(inputs == sorted(set(inputs)) and all(0 <= i < source_n for i in inputs), "invalid free coordinates")
    need(len(graph["variables"]) == len(inputs), "input metadata length")
    for i, source_i in enumerate(inputs):
        need(graph["variables"][i] == {"source_index": source_i, **source["variables"][source_i]}, "input metadata")
    source_file = graph.get("source_file", "source206.json")
    need(source_file in ("source206.json", "parent206.json"), "unrecognized source binding")
    need(graph["source_sha256"] == hashlib.sha256((directory / source_file).read_bytes()).hexdigest(), "source hash")
    need(graph["parent_sha256"] == hashlib.sha256((directory / "parent206.json").read_bytes()).hexdigest(), "parent hash")
    for i, nd in enumerate(nodes):
        need(isinstance(nd, list), "bad node")
        op = nd[0]
        if op == "var":
            need(i < len(inputs) and nd == ["var", i], "unexpected variable leaf")
        elif op == "const":
            need(len(nd) == 2 and type(nd[1]) is int, "bad constant")
        else:
            need(op in ("+", "-", "*") and len(nd) == 3, "nonpolynomial operation")
            need(all(type(a) is int and 0 <= a < i for a in nd[1:]), "graph is not topological")
    defs, used = {}, set()
    for entry in graph["source_definitions"]:
        r, v = entry["row"], entry["variable"]
        need(0 <= r < len(rows) and 0 <= v < source_n and v not in defs and r not in used, "repeated or invalid pivot")
        p = decode(rows[r]["terms"])
        c = p.get((v,))
        need(c in (-1, 1) and all(v not in m for m in p if m != (v,)), "nonunit pivot")
        defs[v] = (r, {m: -c*a for m, a in p.items() if m != (v,)})
        used.add(r)
    need(inputs == [i for i in range(source_n) if i not in defs], "free/defined coordinate partition")
    retained = [r for r in range(len(rows)) if r not in used]
    need(graph["retained_source_rows"] == retained, "retained residual partition")
    env = {v: i for i, v in enumerate(inputs)}
    checked_defs, checked_rows, macro_roots = set(), [], {}
    seen_nodes = set()

    def leaf(n):
        return constant(nodes[n][1]) if nodes[n][0] == "const" else atom(n)

    def expression(p):
        answer = {}
        for mon, coefficient in p.items():
            need(all(v in env for v in mon), "definition dependency is not available")
            answer = add(answer, scale(coefficient, product([leaf(env[v]) for v in mon])))
        return answer

    def local(root, boundaries):
        need(type(root) is int and 0 <= root < len(nodes), "invalid root")
        memo = {}
        def descend(i):
            if i in memo:
                return memo[i]
            seen_nodes.add(i)
            nd = nodes[i]
            if nd[0] == "const":
                answer = constant(nd[1])
            elif i in boundaries:
                answer = atom(i)
            else:
                need(nd[0] != "var", "undeclared variable crossed expression boundary")
                left, right = descend(nd[1]), descend(nd[2])
                answer = add(left, right) if nd[0] == "+" else (
                    add(left, scale(-1, right)) if nd[0] == "-" else multiply(left, right))
            memo[i] = answer
            return answer
        return descend(root)

    for block in graph["blocks"]:
        kind, root = block["kind"], block["root"]
        boundaries = set(env.values())
        if kind == "definition":
            v, r = block["source_variable"], block["source_row"]
            need(v in defs and defs[v][0] == r and v not in checked_defs, "unexpected definition block")
            expected = expression(defs[v][1])
            need(local(root, boundaries) == expected, f"definition block mismatch for variable {v}")
            env[v] = root
            checked_defs.add(v)
        elif kind == "residual":
            r = block["source_row"]
            need(r in retained and r != len(rows)-1 and r not in checked_rows, "unexpected residual block")
            need(local(root, boundaries) == expression(decode(rows[r]["terms"])), f"residual block mismatch {r}")
            checked_rows.append(r)
        elif kind == "pool_macro":
            j, field = block["block"], block["field"]
            need(0 <= j < 5 and field in ("base", "T", "E") and (j, field) not in macro_roots, "unexpected pool macro")
            need(local(root, boundaries) == expression(decode(pool["blocks"][j][field])), f"pool macro mismatch {j},{field}")
            macro_roots[j, field] = root
        elif kind == "pool":
            r = block["source_row"]
            need(r == len(rows)-1 and len(macro_roots) == 15 and r not in checked_rows, "pool final block order")
            T = [leaf(macro_roots[i, "T"]) for i in range(5)]
            expected = add(*[product([leaf(macro_roots[i, "base"]), leaf(macro_roots[i, "E"]), *T[:i], *T[i+1:]]) for i in range(5)],
                           scale(-1, product([leaf(env[pool["pool_coordinates"][0]]), *T])))
            need(local(root, boundaries | set(macro_roots.values())) == expected, "five-base pool circuit mismatch")
            checked_rows.append(r)
        else:
            raise ValueError("unknown block kind")
    need(checked_defs == set(defs) and checked_rows == retained, "incomplete block coverage")
    need(graph["restore_source_roots"] == [env[i] for i in range(source_n)], "source restoration roots")
    roots = [b["root"] for b in graph["blocks"] if b["kind"] in ("residual", "pool")]
    need(roots == graph["residual_roots"], "residual root list")
    sos = add(*[multiply(leaf(r), leaf(r)) for r in roots])
    need(local(graph["output"], set(roots)) == sos, "output is not the complete sum of squares")

    # Independently propagated degree bounds and nonzero homogeneous evaluation.
    cert = graph["degree_certificate"]
    modulus = cert["modulus"]
    need(type(modulus) is int and modulus >= 2, "invalid degree-certificate modulus")
    need(len(cert["direction"]) == len(inputs), "degree direction length")
    degrees = {i: 1 for i in inputs}
    leaders = dict(zip(inputs, [x % modulus for x in cert["direction"]]))
    height_bits = {i: 0 for i in inputs}
    def stats(p):
        weights = {m: sum(degrees[v] for v in m) for m in p}
        degree = max(weights.values(), default=0)
        top = sum(c * math.prod(leaders[v] for v in m) for m, c in p.items() if weights[m] == degree) % modulus
        terms = [(abs(c)-1).bit_length() + sum(height_bits[v] for v in m) for m, c in p.items()]
        hb = max(terms, default=0) + (len(terms)-1).bit_length() if terms else 0
        return degree, top, hb
    for b in graph["blocks"]:
        if b["kind"] == "definition":
            v = b["source_variable"]
            degrees[v], leaders[v], height_bits[v] = stats(defs[v][1])
    need(cert["source_degrees"] == [degrees[v] for v in range(source_n)], "source degree certificate")
    need(cert["source_leading_coefficients"] == [leaders[v] for v in range(source_n)], "source leading certificate")
    residual_stats = [stats(decode(rows[r]["terms"])) for r in retained]
    rd = [x[0] for x in residual_stats]
    rt = [x[1] for x in residual_stats]
    need(rd == cert["residual_degrees"] and rt == cert["residual_leading_coefficients"], "residual degree certificate")
    degree = max(rd)
    witness_row = cert["witness_source_row"]
    need(witness_row in retained, "degree witness row absent")
    wi = retained.index(witness_row)
    need(rd[wi] == degree and rt[wi] != 0 and rt[wi] == cert["witness_residue"], "maximum-degree witness failed")

    # Recompute actual derivatives at the supplied modular points.
    occurring = [False] * len(inputs)
    for witness in graph["input_occurrence_certificates"]:
        p, point = witness["modulus"], witness["point"]
        need(type(p) is int and p >= 2 and len(point) == len(inputs), "derivative witness format")
        values, derivs = [], []
        for nd in nodes:
            op = nd[0]
            if op == "const":
                values.append(nd[1] % p); derivs.append([0] * len(inputs))
            elif op == "var":
                values.append(point[nd[1]] % p)
                unit = [0] * len(inputs); unit[nd[1]] = 1; derivs.append(unit)
            else:
                l, r = nd[1:]
                if op == "+":
                    values.append((values[l] + values[r]) % p)
                    derivs.append([(a+b) % p for a, b in zip(derivs[l], derivs[r])])
                elif op == "-":
                    values.append((values[l] - values[r]) % p)
                    derivs.append([(a-b) % p for a, b in zip(derivs[l], derivs[r])])
                else:
                    values.append(values[l] * values[r] % p)
                    derivs.append([(a*values[r] + b*values[l]) % p for a, b in zip(derivs[l], derivs[r])])
        derivative = derivs[graph["output"]]
        need(derivative == witness["derivatives"], "actual-input derivative certificate")
        occurring = [seen or d != 0 for seen, d in zip(occurring, derivative)]
    need(all(occurring), "some input lacks proof of actual occurrence")

    live, stack = set(), [graph["output"]]
    while stack:
        i = stack.pop()
        if i not in live:
            live.add(i)
            if nodes[i][0] in ("+", "-", "*"):
                stack.extend(nodes[i][1:])
    metrics = graph["metrics"]
    actual = {"variables": len(inputs), "residuals": len(roots), "exact_degree": 2*degree,
              "binary_operations": sum(nodes[i][0] in ("+", "-", "*") for i in live),
              "live_nodes": len(live), "stored_nodes": len(nodes),
              "largest_literal": max(abs(nodes[i][1]) for i in live if nodes[i][0] == "const"),
              "coefficient_height_strict_power_of_two": 2*max(s[2] for s in residual_stats)+(len(roots)-1).bit_length()+1}
    need(metrics == actual, "graph metrics differ from independently recomputed values")
    need(live <= seen_nodes, "some live node escaped local polynomial verification")
    return {"status": "PASS", **actual, "exact_definition_blocks": len(defs),
            "exact_residual_blocks": len(roots), "pool_macro_blocks": 15,
            "degree_witness_source_row": witness_row, "degree_witness_residue": rt[wi],
            "all_inputs_have_nonzero_derivative_witness": True}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--directory", type=Path, default=Path(__file__).resolve().parent)
    ap.add_argument("--equation", type=Path)
    ap.add_argument("--receipt", type=Path)
    ap.add_argument("--corruption-controls", action="store_true")
    args = ap.parse_args()
    source, pool, source_receipt = check_source(args.directory)
    paths = [args.equation] if args.equation else sorted((args.directory / "equations").glob("*.json"))
    results = []
    for path in paths:
        obj = read(path)
        source_file = obj.get("source_file", "source206.json")
        need(source_file in ("source206.json", "parent206.json"), "unrecognized source file")
        actual_source = source if source_file == "source206.json" else read(args.directory / source_file)
        result = graph_review(args.directory, obj, actual_source, pool)
        result["source_file"] = source_file
        result["file"] = path.name
        if args.corruption_controls:
            controls = []
            for name in ("output_product", "degree_metadata", "source_hash"):
                bad = copy.deepcopy(obj)
                if name == "output_product":
                    bad["nodes"][bad["output"]][0] = "*"
                elif name == "degree_metadata":
                    bad["metrics"]["exact_degree"] += 2
                else:
                    bad["source_sha256"] = "0" * 64
                try:
                    graph_review(args.directory, bad, actual_source, pool)
                except (ValueError, KeyError, IndexError):
                    controls.append(name)
                else:
                    raise ValueError("corruption not rejected: " + name)
            result["corruptions_rejected"] = controls
        results.append(result)
    receipt = {"status": "PASS", "source": source_receipt, "equations": results,
               "scope": "Exact finite identities, graph specifications, degree, coefficient-norm bounds, and liveness; ordinary unbounded calibration is separate."}
    text = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    if args.receipt:
        args.receipt.write_text(text)
    print(text)


if __name__ == "__main__":
    main()
