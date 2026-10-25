#!/usr/bin/env python3
"""Build/check the complete start-marker4177 source page and four integer ports."""
import argparse
from collections import Counter
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PARENT = ROOT / "candidates/one-page-zero-weight6007"
CERT = ROOT / "research/start-marker-independent"
VERIFIER_SHA = "569d9da678dea56d1b610b2e1c436686e361b19ec66ad6cd2683c59344441067"
CERTIFICATE_SHA = "b3e1368f3918e8a3371e11aed9746c2369e8770c9aaa2496b4cf797f3b85b8f8"
PARENT_TEX_SHA = "8a1ef160bddb5f0520623546362fc9fe41c749d85dbf4937600aac01a92397d8"
PARENT_DAG_SHA = "cc67c35f522bd22ddc4265209860d681146da62d42cdc207c3266b697c5b42a8"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def record(raw):
    return {"bytes": len(raw), "sha256": digest(raw)}


def encoded(value):
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def page_text():
    raw = (PARENT / "equation.tex").read_bytes()
    require(digest(raw) == PARENT_TEX_SHA, "Pinned complete parent page changed")
    text = raw.decode()
    changes = [
        (r"B=\rho^{6007}", r"B=\rho^{4177}"),
        (r"\Lambda=\rho^{2995}+\rho^{4007}", r"\Lambda=\rho^{2059}+\rho^{3108}"),
        (r"+\rho^{1984}", r"+\rho^{1048}"),
        (r"2^{29}\rho^{5037}-\rho^{5019}", r"2^{29}\rho^{4175}-\rho^{4157}"),
        (r"\rho^{1042}G_{943}(\rho)+\rho^{6017}", r"\rho^{1048}+\rho^{4187}"),
        (r"&+t^{34}(2-t)x^{1984}.", r"&+t^{34}(2-t)x^{1048}."),
    ]
    for before, after in changes:
        require(text.count(before) == 1, "Unexpected complete parent formula multiplicity")
        text = text.replace(before, after)
    return text.encode()


FLAG_TERM = r"&+t^{34}(2-t)x^{1048}"


def psi_coefficients(t, text):
    """Expand the exact printed Psi recipe; an absent physical flag is detectable."""
    require(text.count(r"x^{992}(x^{10}+t^{17})G_8(tx)") == 1
            and text.count(r"t^8x^{943}(x^{30}+t^{17})G_9(tx)") == 1,
            "Exact printed label summands")
    require(text.count(FLAG_TERM) <= 1, "At most one printed flag summand")
    result = [0] * 3297
    for j in range(8):
        result[1002 + j] += t ** j
        result[992 + j] += t ** (17 + j)
    for j in range(9):
        result[973 + j] += t ** (8 + j)
        result[943 + j] += t ** (25 + j)
    if FLAG_TERM in text:
        result[1048] += t ** 34 * (2 - t)
    return result


def printed_coefficients(text, tiles):
    require(text.count(r"+2^{10}\Psi(x,2)") == 1, "Exact weighted Phi argument")
    psi1, psi2 = psi_coefficients(1, text), psi_coefficients(2, text)
    c = [1024 * value for value in psi2]
    for j, (w, n, east, south) in enumerate(tiles):
        c[j] += 1 + 1024 * (1 + w + 256 * n + 131072 * east + 33554432 * south)
    support = set(range(943)) | {e for e, value in enumerate(psi1) if value} | {990, 991}
    return c, support, psi1


def validate_printed(text, tiles, c, support):
    printed_c, printed_support, psi1 = printed_coefficients(text, tiles)
    require(printed_c == c, "All3297 weighted Phi coefficients")
    require(printed_support == support, "Entire physical support, including zero-weight flag")
    return printed_c, psi1


def materialize():
    source_raw = (CERT / "certify.py").read_bytes()
    certificate_raw = (CERT / "certificate.json").read_bytes()
    require(digest(source_raw) == VERIFIER_SHA, "Reviewed finite verifier changed")
    require(digest(certificate_raw) == CERTIFICATE_SHA, "Reviewed finite certificate changed")
    command = [sys.executable, "-B"]
    if sys.flags.optimize:
        command.append("-O" if sys.flags.optimize == 1 else "-OO")
    command.append(str(CERT / "certify.py"))
    completed = subprocess.run(command, check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    require(not completed.stderr, "Finite verifier reported a diagnostic")
    report = json.loads(completed.stdout)
    require(report["status"] == "PASS" and report["certificate_sha256"] == CERTIFICATE_SHA,
            "Finite verifier did not authenticate the expected certificate")
    certificate = json.loads(certificate_raw)
    require(certificate["script_sha256"] == VERIFIER_SHA, "Certificate verifier binding")
    proof_raw = (CERT / "PROOF.md").read_bytes()
    require(digest(proof_raw) == certificate["proof_sha256"], "Whole ordinary proof binding")

    spec = importlib.util.spec_from_file_location("reviewed_start_marker4177", CERT / "certify.py")
    require(spec is not None and spec.loader is not None, "Reviewed verifier module")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    _, seed, actions, tiles, c, support = module.model()
    canonical, _ = module.constants(c, support)
    require(len(seed) == 436 and len(actions) == 430 and len(tiles) == 943,
            "Whole finite language dimensions")

    page = page_text()
    printed_c, psi1 = validate_printed(page.decode(), tiles, c, support)
    require(len(c) == 3297 and c[1048] == 0 and all(c[e] == 0 for e in (990, 991)),
            "Zero-weight physical flag and both dummy coefficients")
    require(all(value == 0 for value in c[1010:]), "Complete weighted zero tail")
    require(all(value in (0, 1) for value in psi1) and sum(psi1) == 35 and psi1[1048] == 1,
            "Unweighted Psi includes the zero-weight physical flag")
    require(len(support) == 980, "Whole physical support size")

    controls = {}
    wrong = printed_c.copy()
    wrong[1048] = 1 << 44
    controls["restored_weighted_flag"] = wrong != c
    wrong = [1024 * value for value in psi1]
    wrong[:943] = printed_c[:943]
    controls["Psi_one_in_weighted_Phi"] = wrong != c
    corrupted = page.decode().replace(FLAG_TERM, "")
    corrupt_c, corrupt_support, _ = printed_coefficients(corrupted, tiles)
    require(corrupt_c == c and corrupt_support == support - {1048},
            "Deleting actual printed flag leaves Phi unchanged but removes physical flag")
    try:
        validate_printed(corrupted, tiles, c, support)
    except ValueError as error:
        controls["actual_TeX_flag_deletion_rejected"] = str(error) == "Entire physical support, including zero-weight flag"
    else:
        controls["actual_TeX_flag_deletion_rejected"] = False
    require(all(controls.values()), "Changed source recipes were not rejected")

    power = lambda e: 1 << (47 * e)
    B, beta = power(4177), power(4177) - 1
    MC = beta + power(1) - (power(1) + 3) * power(990)
    MC -= sum(power(e) for e in range(943))
    MC -= sum(value * power(e) for e, value in enumerate(psi1) if value)
    K = sum(power(e) for e in (20, 30, 1048, 4187))
    K += sum(value * (power(2059 - e) + power(3108 - e))
             for e, value in enumerate(printed_c) if value)
    MF = B + 3 + ((1 << 44) - 2) * (power(2059) + power(3108))
    MF += sum(power(e) for e in range(973, 982))
    MF += sum(power(e) for e in range(1012, 1020)) + power(1048)
    MF += (1 << 29) * power(4175) - power(4157)
    printed = {"beta": beta, "K": K, "MC": MC, "MF_source": MF}
    require(printed == canonical, "All four printed constants equal certify.constants")

    files, ports = {}, {}
    for name, key in (("beta", "beta"), ("K0", "K"), ("MC", "MC"), ("MF", "MF_source")):
        value = printed[key]
        require(value > 0, "Positive fixed integer")
        raw = value.to_bytes((value.bit_length() + 7) // 8, "big")
        expected = certificate["constant_ports"][key]
        require(record(raw) == {"bytes": expected["bytes"], "sha256": expected["sha256"]}
                and value.bit_length() == expected["bits"], "Whole constant mismatch: " + name)
        packed = gzip.compress(raw, mtime=0)
        filename = key + ".bin.gz"
        files["coefficients/" + filename] = packed
        ports[name] = {"file": filename, "bits": value.bit_length(), "raw_bytes": len(raw),
                       "raw_sha256": digest(raw), "gzip_sha256": digest(packed)}
    raw_bytes = sum(port["raw_bytes"] for port in ports.values())
    require(raw_bytes == 98219 == certificate["raw_bytes"], "Whole coherent byte count")

    parent_raw = (PARENT / "polynomial.json").read_bytes()
    require(digest(parent_raw) == PARENT_DAG_SHA, "Pinned complete66-gate parent changed")
    polynomial = json.loads(parent_raw)
    rows = polynomial["source"]
    counts = dict(Counter(row[1] for row in rows))
    require(len(rows) == 66 and counts == {"*": 38, "+": 15, "-": 13}, "Exact operation ledger")
    require(polynomial["witnesses"] == ["J", "F", "alpha", "z", "f", "h", "i", "T", "s", "w",
                                        "tau", "eta", "zeta", "y", "gamma"]
            and polynomial["fixed_numerals"] == ["beta", "K0", "MC", "MF"], "All15+4 input leaves")
    known = set(polynomial["witnesses"]) | set(polynomial["fixed_numerals"])
    dependencies = {}
    for name, op, left, right in rows:
        require(name not in known and op in {"+", "-", "*"}, "Unique typed wire")
        require(all(type(x) is int or x in known for x in (left, right)), "Backward wire reference")
        dependencies[name] = {x for x in (left, right) if isinstance(x, str)}
        known.add(name)
    live, pending = set(), [polynomial["output"]]
    while pending:
        name = pending.pop()
        if name not in live:
            live.add(name)
            pending.extend(dependencies.get(name, ()))
    require(live == known, "Every operation and every input must be live")
    polynomial["name"] = "start_marker4177_p66_degree157"
    polynomial["proof"] = "README.md"
    polynomial["proof_boundary"] = "Complete Start-marker native/P66 ordinary proof plus discharged Pcs; retained K215/refutation calibration, no new formal-kernel replay."
    polynomial["coefficient_binding"] = {
        "schema": "start_marker4177_materialized_v1", "path": "coefficients/",
        "ports": ports, "raw_bytes": raw_bytes,
        "certificate": "../../research/start-marker-independent/certificate.json",
        "certificate_sha256": CERTIFICATE_SHA,
        "ordinary_proof": "../../research/start-marker-independent/PROOF.md",
        "ordinary_proof_sha256": certificate["proof_sha256"],
    }
    files["polynomial.json"] = encoded(polynomial)
    files["equation.tex"] = page_text()
    files["BUILD_AUDIT.json"] = encoded({
        "schema": "start_marker4177_printed_recipe_audit_v1",
        "all3297_Phi_coefficients_equal": True, "nonzero_Phi_coefficients": 977,
        "Psi_one_support_positions": 35, "physical_support_positions": 980,
        "flag_coefficient": {"1048": 0}, "physical_flag_present": True,
        "zero_tail": [1010, 3296], "negative_controls": controls,
        "all_four_printed_integers_equal_canonical": True, "raw_bytes": raw_bytes,
        "operations": 66, "operation_counts": counts, "all15_variables_and4_ports_live": True,
        "exact_degree": 157, "degree_basis": "Identical full free-port66 DAG; retained nonzero leading coefficient8*beta^92.",
        "certificate_sha256": CERTIFICATE_SHA, "verifier_sha256": VERIFIER_SHA,
        "ordinary_proof_sha256": certificate["proof_sha256"],
        "parent_page_sha256": PARENT_TEX_SHA, "parent_polynomial_sha256": PARENT_DAG_SHA,
        "scope": "Complete source-page reconstruction and whole constants; no PDF, native compiler or formal-kernel execution.",
    })
    return files


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build", action="store_true", help="Write generated source and integer ports")
    args = parser.parse_args()
    files = materialize()
    closure = dict(files)
    closure["README.md"] = (HERE / "README.md").read_bytes()
    closure["build.py"] = Path(__file__).read_bytes()
    files["SOURCE_MANIFEST.json"] = encoded({
        "schema": "start_marker4177_source_bundle_v1",
        "files": {name: record(raw) for name, raw in sorted(closure.items())},
        "finite_certificate": "research/start-marker-independent/certificate.json",
        "finite_certificate_sha256": CERTIFICATE_SHA,
        "ordinary_proof": "research/start-marker-independent/PROOF.md",
        "ordinary_proof_sha256": json.loads((CERT / "certificate.json").read_bytes())["proof_sha256"],
        "scope": "Complete deterministic source/ports bundle. PDF and visual receipts belong to a separate rendering manifest.",
    })
    for relative, raw in files.items():
        target = HERE / relative
        if args.build:
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(raw)
        else:
            require(target.read_bytes() == raw, "Generated artifact differs: " + relative)
    print(json.dumps({"status": "PASS", "files": {name: digest(raw) for name, raw in files.items()},
                      "integer_leaf_operations": 66, "raw_constant_bytes": 98219,
                      "all3297_Phi_coefficients": True, "all980_support_positions": True}, sort_keys=True))


if __name__ == "__main__":
    main()
