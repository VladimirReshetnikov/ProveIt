#!/usr/bin/env python3
"""Audit the final finite data, coefficient binding, and seven circuit packets.

Run from any working directory with Python 3.10+; standard library only.
This checker does not run the emitters. It parses the literal machine separately,
checks authenticated input hashes, reconstructs the operation/liveness/degree
ledgers, and certifies maximum degrees using actual coefficient residues.

Its finite checks do not prove consistency, decide Diophantine solvability, or
replace the ordinary mathematical equivalence proof in the accompanying report.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "data"
PIN = "f0ae4e0991ca44a7bb4e5671d42e33d775e48035"
MACHINE_SHA256 = "fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090"
TRANSITIONS_SHA256 = "880741dcb49494aab7c1f7d7e453764d573f9704882502b5849f1e3a84b81755"
WINDOW_SHA256 = "baa3d2b5296b818b2e6488c1b06fda29e405d9b4cf5dd19a3c38fbdd1ba658d7"
RECIPE_ID = "k215-strict-four-cell-5252-5pow16"
PORTS = ["beta", "K0", "MC", "MF"]
PORT_MAPPING = {
    "beta": "B_base-1", "K0": "DC+B_base*DR",
    "MC": "MC_native", "MF": "MF_native+B_base-1",
}
SCALARS = {
    "k": 5252, "a": 439, "ell": 13, "p": 1075, "m": 7013,
    "dummy_count": 2, "dummy_start": 10520, "M": 11839,
    "anchor_factors": [1, 3, 5, 11], "Emax": 130229, "Hc": 226259,
    "T1": 487157, "T2": 747619, "bmin": 36871, "b": 78125,
    "L": 1953125, "d": 152587890625, "copy_offsets": [8764, 8325, 7886, 7008],
    "bare_shifts": [1317, 226698, 47356, 94712],
    "mu_bit_length": 36856, "mu_population": 2847,
    "clause_mass_bit_length": 22893, "carry_bound_bit_length": 22909,
    "native_support": 7014, "field_targets": 1319, "mod5_unit": 3,
}
POSITIVE = "strictly positive integers"
SIGNED = "unrestricted integers"
# witnesses, domain, operations, multiplications, equations, residual degrees
CASES = {
    "merger12_product.json": (12, POSITIVE, 117, 73, 1, [1529]),
    "merger12_system.json": (12, POSITIVE, 112, 71, 3, [7, 2, 1520]),
    "merger13_product.json": (13, POSITIVE, 91, 53, 1, [319]),
    "merger13_system.json": (13, POSITIVE, 83, 50, 4, [7, 2, 22, 288]),
    "integer26_product.json": (26, SIGNED, 169, 96, 1, [2993]),
    "integer26_system.json": (26, SIGNED, 164, 94, 3, [13, 4, 2976]),
    "retained16_system59.json": (16, POSITIVE, 59, 33, 7, [22, 18, 24, 7, 2, 22, 6]),
}
MODULUS = 1000000007
SCOPE = (
    "Finite input authentication, coefficient-port binding, literal transition "
    "agreement, independent circuit counts/liveness, and maximum-degree "
    "certificates. No claim of a new proof-assistant theorem or a decision "
    "of Con(ZFC); the unbounded equivalence uses the mathematical proofs."
)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read_json(path):
    return json.loads(path.read_text(encoding="utf-8"))


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def relative_file(path):
    """Resolve a manifest path without permitting escape from the bundle."""
    require(isinstance(path, str), "Manifest path is not a string.")
    p = Path(path)
    require(not p.is_absolute(), "Manifest path must be relative: " + path)
    resolved = (ROOT / p).resolve()
    require(resolved.is_relative_to(ROOT), "Manifest path escapes the bundle: " + path)
    require(resolved.is_file(), "Missing bundle file: " + path)
    return resolved


def check_machine():
    require(digest(DATA / "k215.tm") == MACHINE_SHA256, "Literal machine hash mismatch.")
    require(digest(DATA / "k215_transitions.json") == TRANSITIONS_SHA256,
            "Transition export hash mismatch.")
    lines = (DATA / "k215.tm").read_text(encoding="utf-8").splitlines()
    require(lines[0].strip() == "#! start 0", "Literal machine start header changed.")
    rows = []
    for line in lines[1:]:
        if not line.strip():
            continue
        fields = line.split()
        require(len(fields) == 5 and fields[3] in ("L", "R"), "Malformed literal action.")
        state, read, write, nxt = map(int, (fields[0], fields[1], fields[2], fields[4]))
        require(0 <= state < 215 and read in (0, 1) and write in (0, 1)
                and 0 <= nxt <= 215, "Literal action outside the fixed alphabet.")
        rows.append([state, read, write, -1 if fields[3] == "L" else 1, nxt])
    require(len(rows) == 430, "Literal action count is not 430.")
    require({(r[0], r[1]) for r in rows} == {(q, s) for q in range(215) for s in (0, 1)},
            "Literal machine is not deterministic and total on its 430 working pairs.")
    exported = read_json(DATA / "k215_transitions.json")
    require(exported["schema"] == "proveit-k215-independent-transition-export-v1",
            "Transition export schema changed.")
    require(exported["transitions"] == rows, "Literal and exported actions differ.")
    require(exported["transition_fields"] == ["state", "read", "write", "move", "next"],
            "Transition export column convention changed.")
    require(exported["source_sha256"]["tm"] == MACHINE_SHA256, "Export machine binding changed.")
    require(exported["working_states"] == 215 and exported["transition_count"] == 430,
            "Transition export metadata disagrees.")
    for name, value in {"start": 0, "halt": 215, "blank": 0, "head": 0,
                        "tape": "two-way infinite", "move_encoding": {"L": -1, "R": 1}}.items():
        require(exported["convention"][name] == value, "Transition convention: " + name)
    directions = {"L": sum(r[3] == -1 for r in rows), "R": sum(r[3] == 1 for r in rows)}
    terminal = [r for r in rows if r[4] == 215]
    require(directions == exported["direction_counts"] == {"L": 82, "R": 348},
            "Direction count changed.")
    require(terminal == exported["terminal_transitions"] == [[68, 1, 1, 1, 215]],
            "Halting action changed.")
    return {"literal_path": "data/k215.tm", "literal_sha256": MACHINE_SHA256,
            "transition_json_path": "data/k215_transitions.json",
            "transition_json_sha256": TRANSITIONS_SHA256, "compared_rows": 430,
            "working_states": 215, "direction_counts": directions,
            "terminal_transitions": terminal, "literal_export_match": True}


def check_windows():
    require(digest(DATA / "strict_windows.json") == WINDOW_SHA256, "Strict-window hash mismatch.")
    windows = read_json(DATA / "strict_windows.json")
    require(len(windows) == 5252, "Strict-window selector count changed.")
    require(all(isinstance(w, list) and len(w) == 4
                and all(type(x) is int and 0 <= x < 439 for x in w) for w in windows),
            "Malformed strict-window tile.")
    require(len(set(map(tuple, windows))) == 5252, "Repeated strict-window selector.")
    require(windows[0] == [434, 435, 436, 1] and windows[1] == [438, 0, 0, 438],
            "Start or forbidden selector changed.")
    require(windows[2:] == sorted(windows[2:]), "Strict-window order changed.")
    receipt = read_json(DATA / "strict_compiler_checks.json")
    require(receipt["status"] == "PASS" and receipt["window_sha256"] == WINDOW_SHA256
            and receipt["scalars"] == SCALARS, "Strict compiler receipt binding mismatch.")
    return {"path": "data/strict_windows.json", "sha256": WINDOW_SHA256,
            "selectors": 5252, "strict_tiles": 5251, "alphabet_size": 439,
            "unique": True, "prescribed_order": True}


def check_binding():
    path = DATA / "COEFFICIENT_BINDING.json"
    binding = read_json(path)
    require(binding["schema"] == "k215-strict-four-cell-binding-v1", "Coefficient binding schema.")
    require(binding["recipe_id"] == RECIPE_ID and binding["repository_pin"] == PIN,
            "Coefficient recipe or repository pin changed.")
    require(binding["fixed_numerals"] == PORTS and binding["port_mapping"] == PORT_MAPPING,
            "Whole-tuple or shifted-MF coefficient binding changed.")
    require(binding["scalars"] == SCALARS, "Coefficient scalar tuple changed.")
    machine = binding["machine"]
    require(machine["path"] == "data/k215.tm" and machine["sha256"] == MACHINE_SHA256
            and machine["transition_json"] == "data/k215_transitions.json"
            and machine["transition_json_sha256"] == TRANSITIONS_SHA256,
            "Coefficient binding has different machine inputs.")
    require(binding["windows"]["path"] == "data/strict_windows.json"
            and binding["windows"]["sha256"] == WINDOW_SHA256
            and binding["windows"]["count"] == 5252, "Coefficient window binding changed.")
    require(set(binding["circuits"]) == set(CASES), "Coefficient binding circuit set changed.")
    for name in CASES:
        require(binding["circuits"][name] == {"recipe_id": RECIPE_ID, "fixed_numerals": PORTS},
                "Circuit coefficient tuple mismatch: " + name)
    evaluator = binding["evaluator"]
    require(evaluator["path"] == "code/coefficient_recipe.py", "Unexpected coefficient evaluator.")
    require(digest(relative_file(evaluator["path"])) == evaluator["sha256"],
            "Coefficient evaluator hash does not match the binding.")
    # The evaluator is the supplied finite recipe, not a second implementation of it.
    import coefficient_recipe
    require(coefficient_recipe.binding_document() == binding,
            "Coefficient manifest and executable finite recipe disagree.")
    coefficients = coefficient_recipe.coefficients_mod(MODULUS)
    require(list(coefficients) == PORTS and all(type(v) is int and 0 <= v < MODULUS
                                               for v in coefficients.values()),
            "Malformed coefficient residues.")
    require(coefficients["beta"] != 0, "Chosen degree modulus annihilates beta.")
    residues = read_json(DATA / "coefficient_residues.json")
    require(residues["recipe_id"] == RECIPE_ID
            and residues["binding_sha256"] == digest(path), "Residue receipt binding mismatch.")
    recorded = [r for r in residues["fingerprints"] if r["modulus"] == MODULUS]
    require(len(recorded) == 1 and recorded[0]["ports"] == coefficients,
            "Actual coefficient residues disagree with their receipt.")
    return binding, coefficients, {
        "path": "data/COEFFICIENT_BINDING.json", "sha256": digest(path),
        "recipe_id": RECIPE_ID, "fixed_numerals": PORTS, "port_mapping": PORT_MAPPING,
        "evaluator_path": evaluator["path"], "evaluator_sha256": evaluator["sha256"],
        "degree_modulus": MODULUS, "actual_coefficient_residues": coefficients,
        "manifest_matches_executable_recipe": True,
    }


def trim(poly):
    while poly and poly[-1] == 0:
        poly.pop()
    return poly


def add_poly(a, b, sign=1):
    out = list(a) + [0] * max(0, len(b) - len(a))
    for i, value in enumerate(b):
        out[i] = (out[i] + sign * value) % MODULUS
    return trim(out)


def multiply_poly(a, b):
    if not a or not b:
        return []
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] += x * y
    return trim([x % MODULUS for x in out])


def check_circuit(filename, expected, binding, coefficients):
    count, domain, operations, multiplications, equations, residual_degrees = expected
    packet = read_json(DATA / filename)
    witnesses = packet["witnesses"]
    require(len(witnesses) == count and packet["witness_domain"] == domain,
            filename + ": witness count/domain mismatch.")
    require(packet["fixed_numerals"] == PORTS
            and packet["coefficient_binding"] == "COEFFICIENT_BINDING.json",
            filename + ": coefficient binding mismatch.")
    require(binding["circuits"][filename]["fixed_numerals"] == PORTS,
            filename + ": absent complete fixed tuple.")
    inputs = witnesses + PORTS
    require(all(isinstance(x, str) for x in inputs) and len(set(inputs)) == len(inputs),
            filename + ": duplicated or malformed inputs.")
    source = packet["source"]
    known = set(inputs)
    degree = {x: 1 for x in witnesses}
    degree.update({x: 0 for x in PORTS})
    # A concrete linear specialization certifies a lower degree bound. All fixed
    # ports use the actual coefficient tuple modulo MODULUS, not toy constants.
    affine = {name: [2 * j + 3, j + 2] for j, name in enumerate(witnesses)}
    values = dict(affine)
    values.update({name: [value] if value else [] for name, value in coefficients.items()})
    counts = {"+": 0, "-": 0, "*": 0}
    def valid_arg(arg):
        return type(arg) is int or isinstance(arg, str) and arg in known
    def deg(arg):
        return 0 if type(arg) is int else degree[arg]
    def val(arg):
        return ([] if arg % MODULUS == 0 else [arg % MODULUS]) if type(arg) is int else values[arg]
    for row in source:
        require(isinstance(row, list) and len(row) == 4, filename + ": malformed gate.")
        name, op, a, b = row
        require(isinstance(name, str) and name not in known and op in counts,
                filename + ": duplicate or invalid gate.")
        require(valid_arg(a) and valid_arg(b), filename + ": undeclared gate input.")
        degree[name] = deg(a) + deg(b) if op == "*" else max(deg(a), deg(b))
        values[name] = multiply_poly(val(a), val(b)) if op == "*" else add_poly(val(a), val(b), 1 if op == "+" else -1)
        counts[op] += 1
        known.add(name)
    require(len(source) == operations and counts["*"] == multiplications,
            filename + ": operation ledger mismatch.")
    actual_ledger = {"operations": len(source), "multiplications": counts["*"],
                     "additions_subtractions": counts["+"] + counts["-"],
                     "all_gates_live": True, "all_ports_live": True}
    require(packet["ledger"] == actual_ledger, filename + ": advertised ledger mismatch.")
    if "output" in packet:
        require("comparisons" not in packet, filename + ": conflicting output conventions.")
        comparisons = [[packet["output"], 0]]
        require(packet["exact_degree"] == residual_degrees[0], filename + ": claimed product degree.")
    else:
        comparisons = packet["comparisons"]
        require(packet["residual_exact_degrees"] == residual_degrees,
                filename + ": claimed residual degrees.")
    require(len(comparisons) == equations and
            all(isinstance(p, list) and len(p) == 2 and all(valid_arg(x) for x in p)
                for p in comparisons), filename + ": equation ports.")
    live = {x for pair in comparisons for x in pair if isinstance(x, str)}
    for name, op, a, b in reversed(source):
        require(name in live, filename + ": dead gate " + name)
        live.update(x for x in (a, b) if isinstance(x, str))
    require(all(x in live for x in inputs), filename + ": dead input port.")
    if "degree_upper_by_register" in packet:
        require(packet["degree_upper_by_register"] == degree,
                filename + ": register degree-bound ledger mismatch.")
    upper = [max(deg(a), deg(b)) for a, b in comparisons]
    specialized = [add_poly(val(a), val(b), -1) for a, b in comparisons]
    observed = [len(p) - 1 for p in specialized]
    require(observed == residual_degrees, filename + ": degree specialization failed.")
    require(max(upper) == max(observed), filename + ": maximum degree not certified.")
    # S59's main Pell residual has a known cancellation (bound 22, exact 18);
    # this does not affect the certified maximum degree 24. Its exact individual
    # upper bound 18 is supplied by build_retained59.py's symbolic audit.
    canonical_sha = hashlib.sha256(json.dumps(source, separators=(",", ":")).encode()).hexdigest()
    if "source_sha256" in packet:
        require(packet["source_sha256"] == canonical_sha, filename + ": source digest mismatch.")
    return {"path": "data/" + filename, "sha256": digest(DATA / filename),
            "source_sha256": canonical_sha, "recipe_id": RECIPE_ID,
            "witnesses": count, "witness_domain": domain, "equations": equations,
            **actual_ledger, "degree_upper_bounds": upper,
            "specialized_residual_degrees": observed, "exact_maximum_degree": max(observed),
            "maximum_degree_certified": True,
            "degree_certificate": {"modulus": MODULUS,
                "linear_substitution": {x: {"constant": p[0], "slope": p[1]} for x, p in affine.items()},
                "leading_residual_coefficients": [p[-1] for p in specialized],
                "fixed_ports": "Actual residues recorded in coefficient_binding."}}


def check_provenance():
    path = ROOT / "SOURCE_PROVENANCE.json"
    document = read_json(path)
    require(document["schema"] == "proveit-source-provenance-v1"
            and document["repository_commit"] == PIN, "Source provenance schema or pin.")
    entries = document["entries"]
    require(isinstance(entries, list) and len(entries) == 19, "Expected 19 copied provenance artifacts.")
    checked = []
    for item in entries:
        rel = item["bundle_path"]
        observed = digest(relative_file(rel))
        raw = relative_file(rel).read_bytes()
        git_blob = hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()
        require(item["repository_commit"] == PIN, "Copied artifact repository pin: " + rel)
        require(observed == item["bundled_sha256"] == item["source_sha256"]
                and item["byte_identical"] is True, "Copied artifact digest mismatch: " + rel)
        require(len(raw) == item["source_size_bytes"] == item["bundled_size_bytes"]
                and git_blob == item["source_git_blob_sha1"], "Copied artifact Git blob mismatch: " + rel)
        checked.append({"path": rel, "sha256": observed})
    return {"path": "SOURCE_PROVENANCE.json", "sha256": digest(path),
            "verified_copied_files": len(checked), "artifacts": checked}


def main():
    try:
        machine = check_machine()
        windows = check_windows()
        binding, coefficients, binding_receipt = check_binding()
        circuits = [check_circuit(name, case, binding, coefficients) for name, case in CASES.items()]
        provenance = check_provenance()
        report = {"schema": "proveit-con-zfc-synthesis-bundle-checks-v1", "status": "PASS",
                  "repository_pin": PIN, "machine": machine, "windows": windows,
                  "coefficient_binding": binding_receipt, "circuits": circuits,
                  "source_provenance": provenance, "scope": SCOPE}
    except (ValueError, KeyError, TypeError, OSError) as exc:
        report = {"schema": "proveit-con-zfc-synthesis-bundle-checks-v1", "status": "FAIL",
                  "error": str(exc), "scope": SCOPE}
        (DATA / "bundle_checks.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
        raise SystemExit(str(exc))
    (DATA / "bundle_checks.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": "PASS", "literal_transitions_compared": 430,
                      "window_selectors": 5252, "circuits_checked": len(circuits),
                      "copied_provenance_files": provenance["verified_copied_files"],
                      "actual_coefficient_degree_certificates": True,
                      "receipt": "data/bundle_checks.json"}, indent=2))


if __name__ == "__main__":
    main()

