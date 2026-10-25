#!/usr/bin/env python3
"""Build/check the complete one-anchor7309 source page and four integer ports."""
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
PARENT = ROOT / "candidates/one-page-two-anchor7691"
CERT = ROOT / "research/one-anchor-independent"
VERIFIER_SHA = "9e48fa6e071e279c271d4facc87aec2a7026369a2ab3b3056a68e33c41ae479d"
CERTIFICATE_SHA = "f1d772729d85b1138205d8ab37297dcf79bfffd1338525fb59c22495adf325fd"
PARENT_TEX_SHA = "45a9aa06b18b936199d267e503c0371555417b9404d3fa34b747dc3655f9e9f9"
PARENT_DAG_SHA = "08162db9ea87f5fe05917106838ce1710fc388e0f1a374f622e980a893e41aff"


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
        (r"B=\rho^{7691}", r"B=\rho^{7309}"),
        (r"\Lambda=\rho^{4393}+\rho^{5495}", r"\Lambda=\rho^{4161}+\rho^{5228}"),
        (r"+\rho^{2195}", r"+\rho^{2079}"),
        (r"2^{26}\rho^{6726}-\rho^{6708}", r"2^{25}\rho^{6343}-\rho^{6325}"),
        (r"+\rho^{1100}+\rho^{7733}", r"+\rho^{1137}G_{943}(\rho)+\rho^{7351}"),
        (r"&+t^{34}x^{1095}(1+tx^{1100}).", r"&+t^{34}(2t-1)x^{2079}."),
    ]
    for before, after in changes:
        require(text.count(before) == 1, "Unexpected complete parent formula multiplicity")
        text = text.replace(before, after)
    return text.encode()


def psi_coefficients(t):
    """Literal expansion of the printed three summands, including zero tail."""
    result = [0] * 3297
    for j in range(8):
        result[1023 + j] += t ** j
        result[1003 + j] += t ** (17 + j)
    for j in range(9):
        result[1013 + j] += t ** (8 + j)
        result[983 + j] += t ** (25 + j)
    result[2079] += t ** 34 * (2 * t - 1)
    return result


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

    spec = importlib.util.spec_from_file_location("reviewed_one_anchor7309", CERT / "certify.py")
    require(spec is not None and spec.loader is not None, "Reviewed verifier module")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    _, seed, actions, tiles, c, support = module.model()
    canonical, _ = module.constants(c, support)
    require(len(seed) == 436 and len(actions) == 430 and len(tiles) == 943,
            "Whole finite language dimensions")

    psi1, psi2 = psi_coefficients(1), psi_coefficients(2)
    printed_c = [1024 * value for value in psi2]
    for j, (w, n, east, south) in enumerate(tiles):
        printed_c[j] += 1 + 1024 * (1 + w + 256 * n + 131072 * east + 33554432 * south)
    require(len(c) == 3297 and printed_c == c, "All3297 weighted Phi coefficients")
    require(c[2079] == 3 * (1 << 44) and all(c[e] == 0 for e in (1095, 2195, 3296)),
            "One weight-three anchor, no predecessor anchors")
    require(all(value == 0 for value in c[2080:]), "Complete retained zero coefficient tail")
    require(all(value in (0, 1) for value in psi1) and sum(psi1) == 35,
            "Unweighted Psi is the35-position control indicator")
    printed_support = set(range(943)) | {e for e, value in enumerate(psi1) if value} | {1063, 1064}
    require(printed_support == support and len(support) == 980, "Entire printed support")

    # Three simple semantic corruptions must fail the complete comparison.
    controls = {}
    wrong = printed_c.copy()
    wrong[2079] = 1 << 44
    controls["unweighted_single_anchor"] = wrong != c
    wrong = printed_c.copy()
    wrong[1095] = 1 << 44
    controls["restored_lower_anchor"] = wrong != c
    wrong = [1024 * value for value in psi1]
    wrong[:943] = printed_c[:943]
    controls["Psi_one_in_weighted_Phi"] = wrong != c
    require(all(controls.values()), "Changed coefficient recipes were not rejected")

    power = lambda e: 1 << (47 * e)
    B, beta = power(7309), power(7309) - 1
    MC = beta + power(1) - (power(1) + 3) * power(1063)
    MC -= sum(power(e) for e in range(943))
    MC -= sum(value * power(e) for e, value in enumerate(psi1) if value)
    K = sum(power(e) for e in (30, 62, 7351))
    K += sum(power(e) for e in range(1137, 2080))
    K += sum(value * (power(4161 - e) + power(5228 - e))
             for e, value in enumerate(printed_c) if value)
    MF = B + 3 + ((1 << 46) - 2) * (power(4161) + power(5228))
    MF += sum(power(e) for e in range(1013, 1022))
    MF += sum(power(e) for e in range(1065, 1073)) + power(2079)
    MF += (1 << 25) * power(6343) - power(6325)
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
    require(raw_bytes == 172011 == certificate["raw_bytes"], "Whole coherent byte count")

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
    polynomial["name"] = "one_weighted_anchor7309_p66_degree157"
    polynomial["proof"] = "README.md"
    polynomial["proof_boundary"] = "Complete one-anchor native/P66 ordinary proof plus discharged Pc1; retained K215/refutation calibration, no new formal-kernel replay."
    polynomial["coefficient_binding"] = {
        "schema": "one_anchor7309_materialized_v1", "path": "coefficients/",
        "ports": ports, "raw_bytes": raw_bytes,
        "certificate": "../../research/one-anchor-independent/certificate.json",
        "certificate_sha256": CERTIFICATE_SHA,
        "ordinary_proof": "../../research/one-anchor-independent/PROOF.md",
        "ordinary_proof_sha256": certificate["proof_sha256"],
    }
    files["polynomial.json"] = encoded(polynomial)
    files["equation.tex"] = page_text()
    files["BUILD_AUDIT.json"] = encoded({
        "schema": "one_anchor7309_printed_recipe_audit_v1",
        "all3297_Phi_coefficients_equal": True, "nonzero_Phi_coefficients": 978,
        "Psi_one_support_positions": 35, "physical_support_positions": 980,
        "anchor_coefficients": {"1095": 0, "2079": 3 * (1 << 44), "2195": 0, "3296": 0},
        "zero_tail": [2080, 3296], "negative_controls": controls,
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
        "schema": "one_anchor7309_source_bundle_v1",
        "files": {name: record(raw) for name, raw in sorted(closure.items())},
        "finite_certificate": "research/one-anchor-independent/certificate.json",
        "finite_certificate_sha256": CERTIFICATE_SHA,
        "ordinary_proof": "research/one-anchor-independent/PROOF.md",
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
                      "integer_leaf_operations": 66, "raw_constant_bytes": 172011,
                      "all3297_Phi_coefficients": True, "all980_support_positions": True}, sort_keys=True))


if __name__ == "__main__":
    main()
