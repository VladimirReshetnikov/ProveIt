#!/usr/bin/env python3
"""Audit the complete sorted2501 integer graph and exact degree-118 replacement."""
import argparse
from collections import Counter
from copy import deepcopy
import gzip
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PROOF_SHA = "b2cb3b703da36bb33e1a3d26851d139a246010f1b2a39491927d6ea43031bd7f"
PARENT = ROOT / "candidates/one-page-sorted-carrier65-2501/polynomial.json"
PARENT_SHA = "06be4bd16a817fe8de0042dad0f3c0f7f93ac310959798a132fb5f18c0ffe035"
CARRIER_PROOF_SHA = "53ec75050c7f4a00386d9738f8c515f3a816d8e4d94afcebb54b3497d972e749"
NATIVE_PROOF_SHA = "d38b5f83ae1b6d342d849e134e1fa341306cb506d68f58fbe74abf9e013cb65d"
NATIVE_CERT_SHA = "372cee7b5e353ee174a9335e117c843b0e847892b038847bcb5df4c6dda8feae"
COEFFICIENTS_SHA = "43f31dd15eb258cca8979aaf39ea8987df9ac573246e50f94bd43769c470dc93"
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


def product(factors, coefficient=1):
    out = {ZERO: coefficient}
    for factor, exponent in factors:
        out = mul(out, power(factor, exponent))
    return out


def expected_graph(parent):
    graph = deepcopy(parent)
    graph.update({
        "arithmetic_proof": "PROOF.md",
        "arithmetic_proof_sha256": PROOF_SHA,
        "exact_degree": 118,
        "name": "sorted2501_scaled_auxiliary66_degree118",
        "operation_counts": {"*": 37, "+": 16, "-": 13},
        "operations": 66,
        "parent_polynomial": "../../candidates/one-page-sorted-carrier65-2501/polynomial.json",
        "parent_polynomial_sha256": PARENT_SHA,
        "proof": "PROOF.md",
        "proof_boundary": "Exact identity of fourteen-positive-coordinate zero sets with complete sorted2501 Carrier65; retained native calibration and discharged Pcso, no new formal-kernel replay.",
    })
    graph["coefficient_binding"]["path"] = "../../candidates/one-page-sorted-carrier65-2501/coefficients/"
    graph["display_scalar_names"]["auxiliary_A"] = "A"
    rows = []
    for row in parent["source"]:
        if row[0] == "scaled_f2":
            continue
        if row[0] == "aux_product":
            rows.extend([["scaled_f2", "*", "Delta", "f2"],
                         ["auxiliary_A", "-", "scaled_f2", "Delta"],
                         ["aux_product", "*", "auxiliary_A", "V2minusY2"]])
        else:
            rows.append(list(row))
    graph["source"] = rows
    return graph


def check_graph(graph, parent):
    require(graph == expected_graph(parent), "Complete literal graph and every metadata/binding field match the exact parent transformation")
    require(parent["operations"] == 65 and parent["exact_degree"] == 150,
            "Exact complete Carrier65 parent")
    require(graph["schema"] == "literal_integer_arithmetic_dag_v1"
            and graph["witnesses"] == VARIABLES and graph["fixed_numerals"] == PORTS
            and graph["witness_domain"] == "strictly positive integers", "Exact polynomial interface")
    rows = graph["source"]
    require(len(rows) == 66 == graph["operations"], "All66 literal binary rows")
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
    counts = dict(sorted(Counter(row[1] for row in rows).items()))
    require(counts == {"*": 37, "+": 16, "-": 13} == graph["operation_counts"], "Exact integer-leaf operation metric")
    require(graph["output"] == "polynomial", "Exact output register")
    live = set()

    def visit(name):
        if type(name) is int or name in live:
            return
        live.add(name)
        if name in by_name:
            visit(by_name[name][2])
            visit(by_name[name][3])

    visit("polynomial")
    require(live == known, "Every gate, positive unknown and fixed port is live")
    old_rows = {row[0]: row for row in parent["source"]}
    changes = {name for name in old_rows if old_rows[name] != by_name[name]}
    require(changes == {"aux_product"} and set(by_name) - set(old_rows) == {"auxiliary_A"},
            "Only one existing coefficient input changes; every old producer survives")
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
    zeta = add(full("X"), mul(symbol("gamma"), full("H")))
    main_identity = add(add(power(zeta, 2), mul({ZERO: 2}, mul(full("a"), mul(full("c"), zeta)))),
                        mul(full("H"), power(full("c"), 2)), -1)
    require(main == main_identity and degree(main) == 18, "Entire main-norm expansion and cancellation")
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
    require(cancellations == ["N1"], "All highest-degree cancellations accounted for by exact full expansion")
    q0 = mul(symbol("beta"), symbol("J"))
    k0 = add(symbol("eta"), symbol("zeta"))
    w, s, f, t, i, gamma = [symbol(name) for name in ("w", "s", "f", "T", "i", "gamma")]
    transport = add(mul(w, add(add(q0, symbol("F"), -1), symbol("alpha"), -1)), mul(symbol("z"), q0), -1)
    expected_factors = {
        "N0": product([(w, 2), (s, 4), (k0, 2), (q0, 14)], -1),
        "N1": product([(gamma, 1), (w, 2), (s, 3), (k0, 1), (q0, 11)], 8),
        "Na": product([(w, 2), (s, 4), (k0, 2), (q0, 14), (f, 6), (t, 2)]),
        "Nt": transport,
        "scaled_Ns": product([(i, 2), (w, 4), (s, 8), (k0, 4), (q0, 28)], -1),
    }
    for name, expected in expected_factors.items():
        require(leaders[name] == expected, "Complete factor leading form: " + name)
    factor_degrees = {name: degree(value) for name, value in expected_factors.items()}
    require(list(factor_degrees.values()) == [22, 18, 30, 2, 46], "All exact factor degrees")
    expected_leader = mul(product([(q0, 67), (gamma, 1), (i, 2), (k0, 9),
                                   (w, 10), (s, 19), (t, 2), (f, 6)], 8), transport)
    require(leaders["polynomial"] == expected_leader and degree(expected_leader) == 118
            and graph["exact_degree"] == 118, "Entire degree118 leading homogeneous polynomial")
    selected = {"J": 68, "gamma": 1, "i": 2, "eta": 9, "w": 10, "s": 19, "T": 2, "f": 6, "z": 1, "beta": 68}
    require(expected_leader.get(tuple(selected.get(name, 0) for name in SYMBOLS)) == -8,
            "Nonzero fixed-beta coefficient -8*beta^68")
    return {
        "operations": counts, "live_gates": 66, "live_variables": 14, "live_ports": 4,
        "factor_degrees": factor_degrees, "exact_degree": 118,
        "complete_main_norm_terms": len(main), "main_norm_sha256": sha(encoded(polynomial_rows(main))),
        "leader_symbols_in_order": SYMBOLS,
        "complete_factor_leaders": {name: polynomial_rows(value) for name, value in expected_factors.items()},
        "complete_leader": polynomial_rows(expected_leader), "complete_leader_terms": len(expected_leader),
        "leader_sha256": sha(encoded(polynomial_rows(expected_leader))),
        "selected_coefficient": "-8*beta^68", "accounted_cancellations": cancellations,
        "all_gate_leaders": {name: {"degree": degree(leaders[name]), "terms": len(leaders[name]),
                                      "sha256": sha(encoded(polynomial_rows(leaders[name])))} for name in by_name},
    }


def check_identities():
    # Fresh independent cut symbols: J,F,alpha,z,f,i,T,s mean Delta,f,S,V,y,P,Q,W.
    delta, f, S, V, y, P, Q, W = [symbol(name) for name in ("J", "F", "alpha", "z", "f", "i", "T", "s")]
    S2, y2 = power(S, 2), power(y, 2)
    difference = add(power(V, 2), y2, -1)
    scaled_f2 = mul(delta, power(f, 2))
    A = add(scaled_f2, delta, -1)
    Z = add(scaled_f2, S2, -1)
    old = add(mul(S2, difference), y2)
    new = add(mul(A, difference), y2)
    require(add(A, S2, -1) == add(Z, delta, -1), "Exact A-S^2=Z-Delta polynomial identity")
    correction = mul(add(Z, delta, -1), difference)
    require(add(new, old, -1) == correction, "Exact auxiliary-factor polynomial identity")
    common = product([(P, 1), (Q, 1), (W, 1), (Z, 1)])
    old_polynomial = add(mul(common, old), delta, -1)
    new_polynomial = add(mul(common, new), delta, -1)
    require(add(new_polynomial, old_polynomial, -1) == mul(common, correction),
            "Exact entire-polynomial difference identity after independent cut expansion")
    wrong_A = add(scaled_f2, delta)
    require(add(add(mul(wrong_A, difference), y2), old, -1) != correction,
            "Wrong-sign auxiliary coefficient fails the identity")
    # Independent Delta,f,i,c symbols verify the divisibility used in the proof.
    delta, f, i, c = [symbol(name) for name in ("J", "F", "alpha", "z")]
    S = product([(i, 1), (delta, 1), (c, 2)])
    Z = add(mul(delta, power(f, 2)), power(S, 2), -1)
    bar = add(power(f, 2), product([(delta, 1), (i, 2), (c, 4)]), -1)
    require(Z == mul(delta, bar), "Exact Z=Delta*Zbar before mathematical cancellation")
    residues = set()
    for a in range(4):
        d = ((a + 2) ** 2 - 1) % 4
        require(d in (0, 3), "Discriminant residue")
        for f in range(4):
            for i in range(4):
                for c in range(4):
                    residue = (f * f - d * i * i * c ** 4) % 4
                    require(residue != 3, "Quotient cannot be negative unit modulo four")
                    residues.add(residue)
    return {"cut_identities": ["A-S^2=Z-Delta", "Unew-U=(Z-Delta)*(V^2-y^2)",
                                "pnew-p=P*Q*W*Z*(Z-Delta)*(V^2-y^2)", "Z=Delta*Zbar"],
            "mod4_cases": 256, "quotient_residues": sorted(residues), "wrong_sign_identity_negative": True,
            "scope": "Exact polynomial identities and finite residue checks. Positive Delta, integer unit-factor reasoning and both zero-set implications are the pinned ordinary proof."}


def port_record(value):
    require(type(value) is int and value > 0, "Positive whole integer port")
    raw = value.to_bytes((value.bit_length() + 7) // 8, "big")
    return {"bits": value.bit_length(), "bytes": len(raw), "sha256": sha(raw)}


def check_ports(graph):
    folder = ROOT / "research/sorted-selector-independent"
    pinned(folder / "PROOF.md", NATIVE_PROOF_SHA)
    cert = json.loads(pinned(folder / "certificate.json", NATIVE_CERT_SHA))
    c = json.loads(pinned(folder / "coefficients.json", COEFFICIENTS_SHA))
    require(len(c) == 3297 and all(type(v) is int and v >= 0 for v in c), "Complete nonnegative integer coefficient array")
    require(cert["recipe_bindings"]["all3297_coefficients_sha256"] == COEFFICIENTS_SHA, "Exact certified full array binding")
    rho_power = lambda exponent: 1 << (47 * exponent)
    G = lambda count: sum(rho_power(j) for j in range(count))
    beta = rho_power(2501) - 1
    K = rho_power(18) + rho_power(1004) + rho_power(2510)
    K += sum(value * rho_power(1493 - e) for e, value in enumerate(c) if value)
    MC = beta - G(951) - rho_power(960) * G(26) - rho_power(1004)
    native = 8 * G(917) - 4 + ((1 << 45) - 4) * rho_power(1493)
    native += rho_power(960) * G(9) + rho_power(987) * G(8) + rho_power(1004)
    values = {"beta": beta, "K": K, "MC": MC, "MF_source": beta + native}
    records = {name: port_record(value) for name, value in values.items()}
    require(records == cert["constant_ports"], "Every reconstructed whole integer equals the final native certificate")
    require(beta >= 31 and K > 0 and 0 < MC < beta < beta + native < 2 * beta, "Actual four-port scalar boxes")
    binding = graph["coefficient_binding"]
    require((HERE / binding["ordinary_proof"]).resolve() == (folder / "PROOF.md").resolve()
            and binding["ordinary_proof_sha256"] == NATIVE_PROOF_SHA
            and (HERE / binding["certificate"]).resolve() == (folder / "certificate.json").resolve()
            and binding["certificate_sha256"] == NATIVE_CERT_SHA, "Actual native proof/certificate paths resolve correctly")
    names = {"beta": "beta", "K0": "K", "MC": "MC", "MF": "MF_source"}
    for graph_name, native_name in names.items():
        entry = binding["ports"][graph_name]
        raw = gzip.decompress(pinned(HERE / binding["path"] / entry["file"], entry["gzip_sha256"]))
        require(int.from_bytes(raw, "big") == values[native_name] and len(raw) == entry["raw_bytes"]
                and sha(raw) == entry["raw_sha256"] and values[native_name].bit_length() == entry["bits"],
                "Full materialized integer-leaf equality: " + graph_name)
    require(sum(entry["bytes"] for entry in records.values()) == binding["raw_bytes"] == 58829, "Entire four-port byte count")
    require(port_record(MC + rho_power(1004)) != records["MC"], "Physical marker omission changes full port")
    coefficient_magnitude = 8 * beta ** 68
    return {"native_proof_sha256": NATIVE_PROOF_SHA, "native_certificate_sha256": NATIVE_CERT_SHA,
            "complete_array_sha256": COEFFICIENTS_SHA, "ports": records, "raw_bytes": 58829,
            "scalar_boxes": True, "marker_omission_negative": True,
            "selected_actual_coefficient": {"sign": -1, "magnitude": port_record(coefficient_magnitude)},
            "scope": "All four complete integers are reconstructed and compared. The native theorem is the retained pinned ordinary proof, not a finite zero search."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="write only the deterministic certificate")
    args = parser.parse_args()
    pinned(HERE / "PROOF.md", PROOF_SHA)
    pinned(ROOT / "research/carrier65-independent/PROOF.md", CARRIER_PROOF_SHA)
    parent = json.loads(pinned(PARENT, PARENT_SHA))
    graph_raw = (HERE / "polynomial.json").read_bytes()
    graph = json.loads(graph_raw)
    require(graph_raw == encoded(expected_graph(parent)), "Exact canonical bytes of the complete derived literal graph")
    checked = check_graph(graph, parent)
    identities = check_identities()
    ports = check_ports(graph)
    negatives = []
    for name in ("wrong_A_sign", "old_auxiliary_input", "rational_leaf", "omitted_factor", "unused_variable", "degree_metadata", "port_metadata"):
        bad = deepcopy(graph)
        rows = {row[0]: row for row in bad["source"]}
        if name == "wrong_A_sign":
            rows["auxiliary_A"][1] = "+"
        elif name == "old_auxiliary_input":
            rows["aux_product"][2] = "normalized_S2"
        elif name == "rational_leaf":
            rows["four_a"][2] = 4.0
        elif name == "omitted_factor":
            rows["product3"][3] = 1
        elif name == "unused_variable":
            bad["witnesses"].append("unused")
        elif name == "degree_metadata":
            bad["exact_degree"] = 117
        else:
            bad["coefficient_binding"]["ports"]["MC"]["bits"] -= 1
        try:
            check_graph(bad, parent)
        except ValueError as error:
            negatives.append({"name": name, "rejected_by": str(error)})
        else:
            raise ValueError("Corrupt complete graph accepted: " + name)
    data = {"schema": "scaled_auxiliary118_sorted2501_audit_v1",
            "audit_sha256": sha(Path(__file__).read_bytes()), "ordinary_proof_sha256": PROOF_SHA,
            "carrier65_proof_sha256": CARRIER_PROOF_SHA, "parent_graph_sha256": PARENT_SHA,
            "complete_graph_sha256": sha(graph_raw), "graph": checked,
            "polynomial_identities": identities, "complete_sorted2501_ports": ports,
            "negative_controls": negatives,
            "scope": "Complete integer-leaf literal graph, exact all-variable leading forms, cut-ring identities, residue cases and whole native ports. No incoming executable is imported or run; no formal-kernel or consistency claim is discharged by this finite audit."}
    raw = encoded(data)
    target = HERE / "CERTIFICATE.json"
    if args.write:
        target.write_bytes(raw)
    else:
        require(target.read_bytes() == raw, "Deterministic certificate byte equality")
    print(json.dumps({"status": "PASS", "operations": 66, "variables": 14, "degree": 118,
                      "raw_ports": 58829, "leader_terms": checked["complete_leader_terms"],
                      "audit_sha256": data["audit_sha256"], "graph_sha256": sha(graph_raw),
                      "certificate_sha256": sha(raw)}, sort_keys=True))


if __name__ == "__main__":
    main()
