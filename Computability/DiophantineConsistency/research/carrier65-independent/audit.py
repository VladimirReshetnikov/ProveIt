#!/usr/bin/env python3
"""Independently audit inert Carrier65 data and both complete retained tuples."""
import argparse
from collections import Counter
from copy import deepcopy
import gzip
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PROOF_SHA = "53ec75050c7f4a00386d9738f8c515f3a816d8e4d94afcebb54b3497d972e749"
GRAPH_SHA = "bf58ed6600eee34d86a802a992e3fd9b999e1835b57a5a83734a40073e1658a7"
INCOMING_PROOF_SHA = "75434688038192dd63381f02c1196727ba8b986fe45accf937967ff29f80fed8"
PARENT = ROOT / "candidates/one-page-low-padding2963/polynomial.json"
PARENT_SHA = "a9a752b912689d1f2418ce1dcc149670a1a3e80843f9ca635131fb8f43693c61"
VARIABLES = ["J", "F", "alpha", "z", "f", "i", "T", "s", "w", "n", "eta", "zeta", "y", "gamma"]
PORTS = ["beta", "K0", "MC", "MF"]
SYMBOLS = VARIABLES + PORTS
ZERO = (0,) * len(SYMBOLS)


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def encoded(value):
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def pinned(path, digest):
    raw = path.read_bytes()
    require(sha(raw) == digest, "Pinned input differs: " + str(path))
    return raw


def add(a, b, sign=1):
    out = dict(a)
    for monomial, value in b.items():
        out[monomial] = out.get(monomial, 0) + sign * value
        if out[monomial] == 0:
            del out[monomial]
    return out


def mul(a, b):
    out = {}
    for ma, ca in a.items():
        for mb, cb in b.items():
            monomial = tuple(x + y for x, y in zip(ma, mb))
            out[monomial] = out.get(monomial, 0) + ca * cb
    return {m: c for m, c in out.items() if c}


def power(a, n):
    out = {ZERO: 1}
    for _ in range(n):
        out = mul(out, a)
    return out


def symbol(name):
    monomial = list(ZERO)
    monomial[SYMBOLS.index(name)] = 1
    return {tuple(monomial): 1}


def degree(a):
    return max((sum(m[:len(VARIABLES)]) for m in a), default=-1)


def leading(a):
    d = degree(a)
    return {m: c for m, c in a.items() if sum(m[:len(VARIABLES)]) == d}


def polynomial_rows(a):
    return [[list(m), c] for m, c in sorted(a.items())]


def check_graph(graph, parent):
    require(graph["witnesses"] == VARIABLES and graph["fixed_numerals"] == PORTS,
            "Exact fourteen variables and four fixed integer ports")
    require(graph["witness_domain"] == "strictly positive integers", "Exact positive domain")
    rows = graph["source"]
    require(len(rows) == 65 and graph["operations"] == 65, "All65 literal binary rows")
    known = set(SYMBOLS)
    by_name = {}
    for row in rows:
        require(isinstance(row, list) and len(row) == 4, "Binary row shape")
        name, op, left, right = row
        require(isinstance(name, str) and name not in known and op in ("+", "-", "*"), "Unique legal binary gate")
        for operand in (left, right):
            require(type(operand) is int or isinstance(operand, str) and operand in known,
                    "Integer-only leaves and topological dependencies")
        known.add(name)
        by_name[name] = row
    require(graph["output"] == "polynomial", "Exact output register")
    counts = dict(sorted(Counter(row[1] for row in rows).items()))
    require(counts == {"*": 37, "+": 16, "-": 12} == graph["operation_counts"], "Exact integer-leaf operation metric")
    live = set()

    def visit(name):
        if type(name) is int or name in live:
            return
        live.add(name)
        if name in by_name:
            visit(by_name[name][2])
            visit(by_name[name][3])

    visit("polynomial")
    require(live == known, "Every row, variable and fixed port is live")
    expected = {row[0]: list(row) for row in parent["source"]
                if row[0] not in {"hE", "index_partial", "Nk", "product2"}}
    expected["product3"] = ["product3", "*", "product1", "Nt"]
    expected.update({"En": ["En", "*", "E", "n"],
                     "tau_partial": ["tau_partial", "+", "En", "k"],
                     "tau": ["tau", "-", "tau_partial", "R"]})
    require(by_name == expected, "Every row is the exact whole-parent carrier transformation")
    require(parent["operations"] == 66 and parent["exact_degree"] == 157
            and parent["witnesses"] == ["J", "F", "alpha", "z", "f", "h", "i", "T", "s", "w", "tau", "eta", "zeta", "y", "gamma"],
            "Exact retained P66 interface")

    full_cache = {name: symbol(name) for name in SYMBOLS}

    def full(name):
        if type(name) is int:
            return {ZERO: name} if name else {}
        if name not in full_cache:
            _, op, left, right = by_name[name]
            a, b = full(left), full(right)
            full_cache[name] = mul(a, b) if op == "*" else add(a, b, 1 if op == "+" else -1)
        return full_cache[name]

    main = full("N1")
    z = add(full("X"), mul(symbol("gamma"), full("H")))
    main_identity = add(add(power(z, 2), mul({ZERO: 2}, mul(full("a"), mul(full("c"), z)))),
                        mul(full("H"), power(full("c"), 2)), -1)
    require(main == main_identity and degree(main) == 18, "Entire main-norm ancestor expansion and cancellation")
    leaders = {name: symbol(name) for name in SYMBOLS}
    cancellations = []
    for name, op, left, right in rows:
        a = {ZERO: left} if type(left) is int else leaders[left]
        b = {ZERO: right} if type(right) is int else leaders[right]
        if op == "*":
            result = mul(a, b)
        else:
            da, db = degree(a), degree(b)
            result = a if da > db else (b if op == "+" else mul({ZERO: -1}, b)) if db > da else add(a, b, 1 if op == "+" else -1)
            if not result:
                cancellations.append(name)
                result = leading(full(name))
        leaders[name] = result
    require(cancellations == ["N1"], "Every leading cancellation accounted for by full expansion")
    q0 = mul(symbol("beta"), symbol("J"))
    k0 = add(symbol("eta"), symbol("zeta"))
    expected_leader = {ZERO: 8}
    for factor, exponent in ((q0, 87), (symbol("gamma"), 1), (symbol("i"), 4), (k0, 13),
                             (symbol("w"), 12), (symbol("s"), 25), (symbol("T"), 2), (symbol("f"), 4)):
        expected_leader = mul(expected_leader, power(factor, exponent))
    expected_leader = mul(expected_leader, add(mul(symbol("w"), add(add(q0, symbol("F"), -1), symbol("alpha"), -1)),
                                             mul(symbol("z"), q0), -1))
    require(leaders["polynomial"] == expected_leader and degree(expected_leader) == 150
            and graph["exact_degree"] == 150, "Complete degree150 leading homogeneous polynomial")
    selected = {"J": 88, "gamma": 1, "i": 4, "eta": 13, "w": 12, "s": 25, "T": 2, "f": 4, "z": 1, "beta": 88}
    monomial = tuple(selected.get(name, 0) for name in SYMBOLS)
    require(expected_leader.get(monomial) == -8, "Nonzero selected coefficient -8*beta^88")
    factors = {name: degree(leaders[name]) for name in ("N0", "N1", "Na", "Nt", "scaled_Ns")}
    require(list(factors.values()) == [22, 18, 62, 2, 46], "Every complete factor degree")
    return {"operations": counts, "live_gates": len(by_name), "live_variables": len(VARIABLES),
            "live_ports": len(PORTS), "factor_degrees": factors, "exact_degree": 150,
            "complete_main_norm_terms": len(main), "main_norm_sha256": sha(encoded(polynomial_rows(main))),
            "complete_leader_terms": len(expected_leader), "leader_sha256": sha(encoded(polynomial_rows(expected_leader))),
            "selected_coefficient": "-8*beta^88", "accounted_cancellations": cancellations}


def port_records(values):
    out = {}
    for name, value in values.items():
        require(type(value) is int and value > 0, "Positive whole integer port")
        raw = value.to_bytes((value.bit_length() + 7) // 8, "big")
        out[name] = {"bits": value.bit_length(), "bytes": len(raw), "sha256": sha(raw)}
    return out


def check_tuple(folder, proof_sha, certificate_sha, length, center, scale):
    path = ROOT / "research" / folder
    pinned(path / "PROOF.md", proof_sha)
    certificate = json.loads(pinned(path / "certificate.json", certificate_sha))
    c_raw = pinned(path / "coefficients.json", certificate["recipe_bindings"]["all3297_coefficients_sha256"])
    c = json.loads(c_raw)
    require(len(c) == 3297 and all(type(x) is int and x >= 0 for x in c), "Complete3297 integer coefficient array")
    power_rho = lambda exponent: 1 << (47 * exponent)
    G = lambda count: sum(power_rho(j) for j in range(count))
    beta = power_rho(length) - 1
    K = power_rho(18) + power_rho(1005) + power_rho(length + 9)
    K += sum(value * power_rho(center - e) for e, value in enumerate(c) if value)
    MC = beta - G(951) - power_rho(960) * G(26) - power_rho(1005)
    native = 4 * G(917) + (scale * (1 << 44) - 2 * scale) * power_rho(center)
    native += power_rho(960) * G(9) + power_rho(987) * G(8) + power_rho(1005)
    values = {"beta": beta, "K": K, "MC": MC, "MF_source": beta + native}
    records = port_records(values)
    require(records == certificate["constant_ports"], "Every complete fixed integer equals the retained certified tuple")
    require(beta >= 31 and K > 0 and 0 < MC < beta < beta + native < 2 * beta, "Actual uniform scalar boxes")
    if length == 2963:
        for name, value in values.items():
            raw = gzip.decompress((PARENT.parent / "coefficients" / (name + ".bin.gz")).read_bytes())
            require(int.from_bytes(raw, "big") == value and len(raw) == records[name]["bytes"], "Full accepted materialized port equality")
    mutated = dict(values)
    mutated["MC"] += power_rho(1005)
    require(port_records(mutated) != certificate["constant_ports"], "Whole marker-deletion port corruption is detected")
    return {"folder": folder, "proof_sha256": proof_sha, "certificate_sha256": certificate_sha,
            "L": length, "d": 47 * length, "clause_center": center, "coefficient_scale": scale,
            "ports": records, "raw_bytes": sum(row["bytes"] for row in records.values()),
            "scalar_boxes": True, "marker_deletion_negative": True,
            "scope": "Reconstruction and scalar interface; canonical P66 soundness/completeness are the pinned ordinary proof, not a finite zero search."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    pinned(HERE / "PROOF.md", PROOF_SHA)
    pinned(HERE / "INCOMING_PROOF.md", INCOMING_PROOF_SHA)
    graph = json.loads(pinned(HERE / "INCOMING_CARRIER65.json", GRAPH_SHA))
    parent = json.loads(pinned(PARENT, PARENT_SHA))
    checked = check_graph(graph, parent)
    negatives = []
    for name in ("tau_sign", "rational_leaf", "omitted_factor", "extra_variable"):
        bad = deepcopy(graph)
        if name == "extra_variable":
            bad["witnesses"].append("unused")
        else:
            gate = {row[0]: row for row in bad["source"]}
            if name == "tau_sign":
                gate["tau"][2], gate["tau"][3] = gate["tau"][3], gate["tau"][2]
            elif name == "rational_leaf":
                gate["four_a"][2] = 4.0
            else:
                gate["product3"][3] = 1
        try:
            check_graph(bad, parent)
        except ValueError as error:
            negatives.append({"name": name, "rejected_by": str(error)})
        else:
            raise ValueError("Corrupt graph was accepted: " + name)
    tuples = [check_tuple("low-padding-independent", "ad952c6f1717a69e6b489e8c7af0bb52ce09414b78cc994b892b6e7f996d06f6",
                          "d165186ba400ebc2074716d2e1a142505b93c6d150b3f1fc44e574e9664ca039", 2963, 1956, 1),
              check_tuple("scaled-clause-independent", "602b9560017f52835d36de8c1969ec8348381c8dae31876cb86905c5de2cdebe",
                          "957faf013a17c2e8e04c03be166d903263d2aadaccac604d31f0791e005776ed", 2953, 1945, 2)]
    data = {"schema": "carrier65_independent_inert_audit_v1", "audit_sha256": sha(Path(__file__).read_bytes()),
            "ordinary_proof_sha256": PROOF_SHA, "incoming_graph_sha256": GRAPH_SHA,
            "incoming_proof_sha256": INCOMING_PROOF_SHA, "parent_graph_sha256": PARENT_SHA,
            "graph": checked, "corruption_controls": negatives, "retained_specializations": tuples,
            "scope": "Data-only exact graph, full homogeneous polynomial and complete tuple audit; no incoming executable code imported or executed, no witness search or formal-kernel replay."}
    raw = encoded(data)
    target = HERE / "CERTIFICATE.json"
    if args.write:
        target.write_bytes(raw)
    else:
        require(target.read_bytes() == raw, "Deterministic whole audit receipt")
    print(json.dumps({"status": "PASS", "operations": 65, "variables": 14, "degree": 150,
                      "main_norm_terms": checked["complete_main_norm_terms"], "leader_terms": checked["complete_leader_terms"],
                      "script_sha256": data["audit_sha256"], "certificate_sha256": sha(raw)}, sort_keys=True))


if __name__ == "__main__":
    main()
