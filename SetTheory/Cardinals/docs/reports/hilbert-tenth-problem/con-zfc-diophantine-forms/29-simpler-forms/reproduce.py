#!/usr/bin/env python3
"""Regenerate the supplied circuits and check their finite diagnostics.

Run with Python 3.10 or later, using only its standard library:
    python -B reproduce.py
    python -B reproduce.py --materialize-coefficients

The optional flag rebuilds the compact943 compiler data and writes the raw
coefficient files. The default verifies the supplied gzip files and the exact
integers they contain, without writing the raw files. Both modes regenerate
the three construction families and save logs and a JSON receipt.

These are reproducibility, arithmetic, circuit, and data checks. They do not
prove Con(ZFC), search for solutions, or constitute a proof-assistant check of
the mathematical equivalences or their imported compiler/Pell dependencies.
"""

import argparse
import ast
from collections import Counter
from datetime import datetime, timezone
import gzip
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time
import traceback


ROOT = Path(__file__).resolve().parent
VERIFY = ROOT / "verification"
LOGS = VERIFY / "logs"
SCOPE = (
    "Regenerated circuit and polynomial artifacts, checked their advertised "
    "counts and degree certificates, ran the generators' finite algebra and "
    "transcription diagnostics, and verified complete compact943 coefficient "
    "bytes. This is not an end-to-end proof-assistant certificate, a solution "
    "search, or a proof of Con(ZFC). The ordinary mathematical equivalence "
    "proofs and their imported compiler/Pell dependencies require separate review."
)


def require(condition, message):
    """Keep the driver's checks active even if it was invoked with -O."""
    if not condition:
        raise RuntimeError(message)


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def read_json(relative):
    return json.loads((ROOT / relative).read_text(encoding="utf-8"))


def utc_now():
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def local_path(relative):
    """Manifest paths are portable paths inside this extracted archive."""
    path = (ROOT / relative).resolve()
    require(path.is_relative_to(ROOT), "Path escapes the archive: " + relative)
    return path


def run_generator(relative, receipt):
    script = local_path(relative)
    require(script.is_file(), "Missing generator: " + relative)
    log_relative = "verification/logs/" + relative.replace("/", "__") + ".log"
    row = {
        "script": relative,
        "script_sha256": sha256(script.read_bytes()),
        "arguments": ["-B", relative],
        "working_directory": str(script.parent.relative_to(ROOT)),
        "log": log_relative,
    }
    receipt["steps"].append(row)
    print("Running " + relative, flush=True)
    env = os.environ.copy()
    env.pop("PYTHONOPTIMIZE", None)
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    started = time.monotonic()
    try:
        with (ROOT / log_relative).open("w", encoding="utf-8") as log:
            log.write("Command: python -B " + relative + "\n")
            log.write("Working directory: " + row["working_directory"] + "\n\n")
            log.flush()
            result = subprocess.run(
                [sys.executable, "-B", str(script)],
                cwd=script.parent,
                env=env,
                stdout=log,
                stderr=subprocess.STDOUT,
                check=False,
                timeout=1800,
            )
        row["returncode"] = result.returncode
        require(result.returncode == 0, relative + " failed; see " + log_relative)
    finally:
        row["elapsed_seconds"] = round(time.monotonic() - started, 3)


def verify_coefficients():
    manifest = read_json("COEFFICIENT_BINDING.json")
    require(manifest["variant"] == "wang943-compact-5pow10", "Wrong coefficient variant")
    require(manifest["base"]["d"] == 5**10, "Wrong compact943 exponent")
    records = manifest["files"]
    require({r["name"] for r in records} == {"beta", "MC", "MF_source", "K"}
            and len(records) == 4, "The complete four-port tuple is required")
    values, checked = {}, []
    for row in records:
        name = row["name"]
        compressed_path = local_path(row.get("supplied_path", row["path"] + ".gz"))
        raw_path = local_path(row["path"])
        compressed = compressed_path.read_bytes()
        require(len(compressed) == row["gzip_bytes"], name + ": gzip length mismatch")
        require(sha256(compressed) == row["gzip_sha256"], name + ": gzip hash mismatch")
        raw = gzip.decompress(compressed)
        require(len(raw) == row["bytes"], name + ": raw length mismatch")
        require(sha256(raw) == row["sha256"], name + ": raw hash mismatch")
        require(bool(raw) and raw[-1] != 0, name + ": nonminimal integer encoding")
        value = int.from_bytes(raw, "little", signed=False)
        require(value.bit_length() == row["bit_length"], name + ": bit length mismatch")
        require(value.bit_count() == row["population"], name + ": population mismatch")
        if raw_path.exists():
            require(raw_path.read_bytes() == raw, name + ": raw file differs from gzip")
        values[name] = value
        checked.append({
            "name": name,
            "supplied_path": str(compressed_path.relative_to(ROOT)),
            "gzip_bytes": len(compressed),
            "gzip_sha256": sha256(compressed),
            "bytes": len(raw),
            "sha256": sha256(raw),
            "bit_length": value.bit_length(),
            "population": value.bit_count(),
            "existing_raw_file_verified": raw_path.exists(),
        })
    d = manifest["base"]["d"]
    beta, mc, mf, k = (values[n] for n in ("beta", "MC", "MF_source", "K"))
    base, native = 1 << d, mf - beta
    require(beta == base - 1, "beta is not 2^(5^10)-1")
    require(0 < mc < beta and mc % 4 == 2, "MC parity contract failed")
    require(0 < native < beta and native % 8 == 4, "Shifted MF contract failed")
    require(mc.bit_count() == manifest["contract"]["MC_population"], "MC population contract failed")
    require(native.bit_count() == manifest["contract"]["MF_native_population"], "MF population contract failed")
    require(mc.bit_count() + native.bit_count() == d, "Complementary population contract failed")
    dr, dc = k >> d, k & beta
    require(dr == 1 << (625 * 5497), "Compiler high-port identity failed")
    require(0 < dc < base, "Compiler low-port range failed")
    require((2 * dc - dr) % 5 == manifest["contract"]["mod5_unit"] == 4,
            "Compiler modulo-five unit contract failed")
    require(sum(r["bytes"] for r in checked) == manifest["total_uncompressed_bytes"],
            "Total coefficient byte length mismatch")
    require(sum(r["gzip_bytes"] for r in checked) == manifest["total_gzip_bytes"],
            "Total compressed coefficient byte length mismatch")
    return {
        "status": "PASS",
        "manifest": "COEFFICIENT_BINDING.json",
        "manifest_sha256": sha256((ROOT / "COEFFICIENT_BINDING.json").read_bytes()),
        "variant": manifest["variant"],
        "files": checked,
        "integer_contract_checks": "PASS",
        "scope": "The complete compact943 tuple used by norm12 and low_degree. "
                 "The signed17 family retains its separate original T4 recipe; "
                 "its generator authenticates its source files and checks modular evaluations.",
    }


def norm_metrics(relative, count, multiplies, degree, comparison_degrees=None):
    body = read_json(relative)
    witnesses, fixed = body["witnesses"], body["fixed_numerals"]
    require(len(witnesses) == len(set(witnesses)) == 12, relative + ": witness count")
    require(body["domain"] == "strictly positive integers", relative + ": domain")
    degrees = {name: 1 for name in witnesses}
    degrees.update({name: 0 for name in fixed})
    counts = Counter()
    for name, op, left, right in body["source"]:
        require(name not in degrees and op in ("+", "-", "*"), relative + ": invalid gate")
        dl = 0 if isinstance(left, int) else degrees[left]
        dr = 0 if isinstance(right, int) else degrees[right]
        degrees[name] = dl + dr if op == "*" else max(dl, dr)
        counts[op] += 1
    require(len(body["source"]) == count and counts["*"] == multiplies,
            relative + ": operation count")
    ledger = body["ledger"]
    require(ledger["operations"] == count and ledger["multiplications"] == multiplies
            and ledger["additions_subtractions"] == count - multiplies,
            relative + ": inconsistent ledger")
    require(ledger["all_gates_live"] and ledger["all_ports_live"], relative + ": liveness ledger")
    if comparison_degrees is None:
        require(body["exact_degree"] == degrees[body["output"]] == degree,
                relative + ": degree mismatch")
        syntactic = degree
    else:
        syntactic = [max(0 if isinstance(x, int) else degrees[x] for x in pair)
                     for pair in body["comparisons"]]
        require(syntactic == body["residual_exact_degrees"] == comparison_degrees,
                relative + ": residual degree mismatch")
    return {"artifact": relative, "variables": 12, "operations": count,
            "multiplications": multiplies, "additions_subtractions": count - multiplies,
            "declared_exact_degree": degree, "recomputed_syntactic_degree_bound": syntactic}


def verify_norm12():
    rows = [
        norm_metrics("norm12/shifted_norm12_product.json", 116, 73, 1097),
        norm_metrics("norm12/shifted_norm12_system110.json", 110, 71, 1088, [7, 2, 1088]),
        norm_metrics("norm12/shifted_norm12_sos118.json", 118, 74, 2176),
    ]
    checks = read_json("norm12/SHIFTED_NORM12_CHECKS.json")
    require(checks["exact_signed_norm_fixtures"] == checks["coordinate_shift_fixtures"] == 48,
            "Norm12 fixture counts differ")
    require(len(checks["leading_form_checks"]) == 3, "Norm12 leading-form checks missing")
    for row in checks["leading_form_checks"]:
        require(row["norm"][0] == 1088 and row["product"][0] == 1097
                and row["norm"][1] != 0 and row["product"][1] != 0,
                "Norm12 leading-form diagnostic failed")
    return {"status": "PASS", "forms": rows,
            "generator_receipt": "norm12/SHIFTED_NORM12_CHECKS.json",
            "degree_scope": "Syntactic upper bounds recomputed here; exact leading forms "
                            "are justified in the mathematical proof and checked by generator fixtures."}


def verify_signed17():
    body = read_json("signed17/generated/signed17.json")
    checks = read_json("signed17/generated/signed17_checks.json")
    variables = body["variables"]
    require(len(variables) == len(set(variables)) == 17, "Signed17 variable count")
    require(body["domain"] == "unrestricted integers", "Signed17 domain")
    degrees, counts, variable_leaves = [], Counter(), []
    for node in body["nodes"]:
        kind = node["kind"]
        if kind == "variable":
            variable_leaves.append(node["name"])
            degree = 1
        elif kind in ("literal", "fixed"):
            degree = 0
        else:
            require(kind in ("add", "sub", "mul"), "Signed17 invalid operation")
            left, right = node["left"], node["right"]
            require(0 <= left < len(degrees) and 0 <= right < len(degrees), "Signed17 invalid DAG")
            degree = degrees[left] + degrees[right] if kind == "mul" else max(degrees[left], degrees[right])
            counts[kind] += 1
        degrees.append(degree)
    expected_counts = {"add": 672, "sub": 26, "mul": 19909}
    expected_degree = 424296 * 5**33 + 53824
    require(variable_leaves == variables, "Signed17 variable leaf list")
    require(dict(counts) == body["operation_counts"] == checks["operations"] == expected_counts,
            "Signed17 operation count")
    require(sum(counts.values()) == checks["total_operations"] == 20607,
            "Signed17 total operation count")
    require(degrees[body["output"]] == body["exact_degree"] == expected_degree,
            "Signed17 degree mismatch")
    certificate = checks["degree_certificate"]
    require(certificate["degree"] == expected_degree
            and certificate["diagonal_leading_coefficient"] % certificate["diagonal_leading_coefficient_modulus"] != 0
            and certificate["leading_coefficient_independent_of_fixed_ports"],
            "Signed17 exact-degree certificate failed")
    for key, value in {"status": "PASS", "variables": 17, "authenticated_source_files": 19,
                       "actual_instance_modular_comparisons": 24, "norm_identity_checks": 150,
                       "intersective_moduli_checked": 1200, "consecutive_square_gap_checks": 10098}.items():
        require(checks[key] == value, "Signed17 diagnostic mismatch: " + key)
    return {"status": "PASS", "variables": 17, "operations": dict(counts),
            "total_operations": sum(counts.values()), "declared_exact_degree": expected_degree,
            "recomputed_syntactic_degree_bound": degrees[body["output"]],
            "generator_receipt": "signed17/generated/signed17_checks.json",
            "coefficient_scope": "Original T4 finite coefficient recipe, not compact943.",
            "degree_scope": "Upper bound recomputed here; the generator certifies its "
                            "nonzero diagonal leading coefficient independently of fixed ports."}


def expression_degree(expression, variables, fixed):
    """Recompute a polynomial's structural degree without evaluating code."""
    def visit(node):
        if isinstance(node, ast.Constant) and type(node.value) is int:
            return 0
        if isinstance(node, ast.Name):
            require(node.id in variables or node.id in fixed, "Unknown polynomial symbol: " + node.id)
            return int(node.id in variables)
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.UAdd, ast.USub)):
            return visit(node.operand)
        if isinstance(node, ast.BinOp):
            if isinstance(node.op, (ast.Add, ast.Sub)):
                return max(visit(node.left), visit(node.right))
            if isinstance(node.op, ast.Mult):
                return visit(node.left) + visit(node.right)
            if isinstance(node.op, ast.Pow):
                require(isinstance(node.right, ast.Constant) and type(node.right.value) is int
                        and node.right.value >= 0, "Nonpolynomial exponent")
                return visit(node.left) * node.right.value
        raise RuntimeError("Unexpected syntax in a polynomial residual")
    return visit(ast.parse(expression, mode="eval").body)


def verify_low_degree():
    checks = read_json("low_degree/generated/ODD_SCALE_LIFTS_CHECKS.json")
    require(checks["no_semantic_claim_from_testing"] is True, "Low-degree diagnostic scope missing")
    manifest = read_json("COEFFICIENT_BINDING.json")
    by_name = {r["name"]: r for r in manifest["files"]}
    results = {r["name"]: r for r in checks["results"]}
    rows = []
    for count, equations, degree, terms in [(51, 30, 4, 342), (42, 21, 6, 467), (36, 15, 8, 845)]:
        name = "integer{}_degree{}_odd_scale".format(count, degree)
        relative = "low_degree/generated/" + name + ".json"
        body, row = read_json(relative), results[name]
        variables, fixed = set(body["variables"]), set(body["fixed_numerals"])
        require(len(variables) == len(body["variables"]) == body["variable_count"] == count,
                name + ": variable count")
        require(body["domain"] == "unrestricted integers", name + ": domain")
        require(len(body["residuals"]) == body["equation_count"] == equations, name + ": equation count")
        degrees = [expression_degree(p, variables, fixed) for p in body["residuals"]]
        require(degrees == body["residual_degrees"] == row["residual_degrees"], name + ": residual degrees")
        require(2 * max(degrees) == body["exact_degree"] == row["exact_degree"] == degree,
                name + ": sum-of-squares degree")
        require(body["expanded_symbolic_terms"] == row["expanded_symbolic_terms"] == terms,
                name + ": symbolic term count")
        require(row["identity_checks"] == equations and row["signed_transcription_trials"] == 32,
                name + ": diagnostic counts")
        require(body["exact_degree_certificate"] == row["exact_degree_certificate"], name + ": degree certificate")
        binding = body["coefficient_binding"]
        require(binding["tuple_id"] == manifest["variant"], name + ": coefficient variant")
        require(set(binding["numeric_coefficients"]) == set(by_name), name + ": incomplete tuple")
        for port, item in binding["numeric_coefficients"].items():
            require(item["sha256"] == by_name[port]["sha256"]
                    and item["gzip_sha256"] == by_name[port]["gzip_sha256"],
                    name + ": inconsistent coefficient identity")
            require(sha256(local_path(str(Path(relative).parent / item["gzip_file"])).read_bytes())
                    == item["gzip_sha256"], name + ": referenced coefficient file mismatch")
        rows.append({"artifact": relative, "variables": count, "equations": equations,
                     "maximum_residual_degree": max(degrees), "declared_exact_degree": degree,
                     "expanded_symbolic_terms": terms,
                     "exact_degree_certificate": body["exact_degree_certificate"]})
    return {"status": "PASS", "forms": rows,
            "generator_receipt": "low_degree/generated/ODD_SCALE_LIFTS_CHECKS.json",
            "degree_scope": "Structural residual degrees recomputed here; the generator "
                            "expands the sum of squares and checks the displayed nonzero coefficients."}


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--materialize-coefficients", action="store_true",
                        help="rebuild compact943 compiler data and raw .bin files before verification")
    args = parser.parse_args()
    VERIFY.mkdir(exist_ok=True)
    LOGS.mkdir(exist_ok=True)
    started = time.monotonic()
    receipt = {"schema": "proveit-conzfc-reproduction-v1", "status": "RUNNING",
               "started_utc": utc_now(), "python": sys.version,
               "materialize_coefficients": args.materialize_coefficients,
               "scope": SCOPE, "steps": []}
    try:
        require(sys.version_info >= (3, 10), "Python 3.10 or later is required")
        if args.materialize_coefficients:
            for script in ("coefficients/build_wang943.py", "coefficients/build_wang943_compact.py",
                           "coefficients/materialize_wang943_compact.py"):
                run_generator(script, receipt)
        receipt["coefficients"] = verify_coefficients()
        for script in ("norm12/build_shifted_norm12.py", "signed17/build_signed17.py",
                       "low_degree/build_odd_scale_lifts.py"):
            run_generator(script, receipt)
        receipt["norm12"] = verify_norm12()
        receipt["signed17"] = verify_signed17()
        receipt["low_degree"] = verify_low_degree()
        receipt["generated_receipt_sha256"] = {
            path: sha256((ROOT / path).read_bytes()) for path in (
                "norm12/SHIFTED_NORM12_CHECKS.json", "signed17/generated/signed17_checks.json",
                "low_degree/generated/ODD_SCALE_LIFTS_CHECKS.json")
        }
        receipt["status"] = "PASS"
    except Exception as error:
        receipt["status"] = "FAIL"
        receipt["error"] = str(error)
        (LOGS / "driver_error.log").write_text(traceback.format_exc(), encoding="utf-8")
        receipt["error_log"] = "verification/logs/driver_error.log"
    finally:
        receipt["completed_utc"] = utc_now()
        receipt["elapsed_seconds"] = round(time.monotonic() - started, 3)
        (VERIFY / "REPRODUCTION.json").write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
    print(receipt["status"] + ": verification/REPRODUCTION.json", flush=True)
    if receipt["status"] != "PASS":
        print(receipt["error"], file=sys.stderr)
        return 1
    print("All finite checks passed. See the receipt for scope and separate coefficient bindings.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
