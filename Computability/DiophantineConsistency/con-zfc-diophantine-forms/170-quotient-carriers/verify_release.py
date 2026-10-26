#!/usr/bin/env python3
"""Read-only release audit, using Python's standard library from any directory.

Run ``python3 -B verify_release.py`` or ``python3 -B -O verify_release.py``.
An optional --receipt PATH writes the complete diagnostics outside this package.
All subprocess logs and upstream rebuilds use temporary directories. No producer
module is imported, no --write option is passed, and no network is used.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent
ALIASES = (
    ("P217", "pooled217_height5184", 217, 154, 19112, 5184),
    ("P220_lowheight", "pooled220_height2736", 220, 157, 8847, 2336),
    ("P220_sparse", "pooled220_height7968", 220, 157, 7858, 6272),
)

# Each checker is executed as a separate process. Set json=False for a checker
# whose successful diagnostic output is plain text rather than a JSON value.
COMPONENTS = (
    {"id": "fixed_carrier_formulas", "script": "compact/verify_fixed_carriers.py", "args": (), "json": True},
    {"id": "fixed_coefficient_reconstruction", "script": "compact/rebuild_fixed_coefficients.py", "args": (), "json": True},
    {"id": "direct_equation_compositions", "script": "direct/verify_compositions.py", "args": (), "json": True},
    {"id": "normalized_ordinate_91", "script": "additional/ordinate_normalization/verify_normalized91.py", "args": (), "json": True},
    {"id": "integer_domain_lift", "script": "code/check_integer_lift.py", "args": (), "json": True},
    {"id": "printed_principal_residuals", "script": "code/render_residuals.py", "args": ("--check",), "json": True},
)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha256(path):
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def read_json(path):
    return json.loads(path.read_text(encoding="utf-8"))


def manifest_check():
    """Check every exact named file, without silently extending manifest scope."""
    manifest = ROOT / "MANIFEST.sha256"
    if not manifest.exists():
        return {"status": "NOT_PRESENT", "scope": "No top-level manifest supplied."}
    entries = {}
    total_bytes = 0
    for number, line in enumerate(manifest.read_text(encoding="utf-8").splitlines(), 1):
        if not line or line.startswith("#"):
            continue
        require(len(line) >= 67 and re.fullmatch(r"[0-9A-Fa-f]{64}", line[:64])
                and line[64:66] in ("  ", " *"),
                f"Malformed MANIFEST.sha256 line {number}")
        name = line[66:]
        relative = Path(name)
        require(name and not relative.is_absolute() and ".." not in relative.parts,
                f"Unsafe manifest path at line {number}: {name!r}")
        target = (ROOT / relative).resolve()
        require(target.is_relative_to(ROOT) and target != manifest.resolve(),
                f"Manifest path leaves package or lists itself: {name!r}")
        require(target not in entries, f"Duplicate manifest path: {name!r}")
        require(target.is_file(), f"Manifest file is missing: {name}")
        expected = line[:64].lower()
        require(sha256(target) == expected, f"Manifest digest mismatch: {name}")
        entries[target] = expected
        total_bytes += target.stat().st_size
    require(entries, "The supplied top-level manifest has no file entries")
    return {"status": "PASS", "sha256": sha256(manifest),
            "named_files": len(entries), "named_bytes": total_bytes,
            "scope": "Every exact named file; unlisted files are not represented as covered."}


def polynomial(terms, dimension, maximum_degree):
    require(isinstance(terms, list), "A sparse term list must be an array")
    result = {}
    for entry in terms:
        require(isinstance(entry, list) and len(entry) == 2, "Malformed sparse term")
        coefficient, indices = entry
        require(type(coefficient) is int and coefficient != 0, "Noninteger or zero sparse coefficient")
        require(isinstance(indices, list) and len(indices) <= maximum_degree,
                "Invalid sparse degree")
        require(all(type(i) is int and 0 <= i < dimension for i in indices),
                "Invalid coordinate index")
        monomial = tuple(indices)
        require(tuple(sorted(monomial)) == monomial and monomial not in result,
                "Unsorted or duplicate sparse monomial")
        result[monomial] = coefficient
    return result


def alias_check(alias, source, n, rows_expected, terms_expected, height_expected):
    public = ROOT / "equations" / alias
    original = ROOT / "direct" / source
    hashes = {}
    for name in ("equation.json", "expanded_polynomial.json", "metrics.json"):
        require((public / name).read_bytes() == (original / name).read_bytes(),
                f"Public alias {alias}/{name} differs from direct/{source}/{name}")
        hashes[name] = sha256(public / name)
    equation = read_json(public / "equation.json")
    require(equation.get("domain") == "unrestricted integers", f"Changed domain: {alias}")
    require(len(equation["variables"]) == n, f"Changed dimension: {alias}")
    require(len(equation["residuals"]) == rows_expected, f"Changed residual count: {alias}")
    residuals = [polynomial(row["terms"], n, 2) for row in equation["residuals"]]
    require(all(residuals), f"Empty quadratic residual in {alias}")
    expansion = {}
    for residual in residuals:
        entries = list(residual.items())
        for j, (first, a) in enumerate(entries):
            for k in range(j, len(entries)):
                second, b = entries[k]
                monomial = tuple(sorted(first + second))
                coefficient = a * b * (1 if j == k else 2)
                expansion[monomial] = expansion.get(monomial, 0) + coefficient
    expansion = {monomial: c for monomial, c in expansion.items() if c}
    supplied = read_json(public / "expanded_polynomial.json")
    require(supplied.get("variables") == n, f"Expanded dimension mismatch: {alias}")
    require(polynomial(supplied["terms"], n, 4) == expansion,
            f"Public quartic coefficient mismatch: {alias}")
    used = {i for monomial in expansion for i in monomial}
    require(used == set(range(n)), f"Unused declared coordinate: {alias}")
    metrics = {
        "variables": n, "rows": rows_expected,
        "residual_terms": sum(len(row) for row in residuals),
        "row_height": max(abs(c) for row in residuals for c in row.values()),
        "degree": max(map(len, expansion)), "monomials": len(expansion),
        "height": max(map(abs, expansion.values())),
    }
    require(metrics == read_json(public / "metrics.json"), f"Public metric mismatch: {alias}")
    require((metrics["degree"], metrics["monomials"], metrics["height"])
            == (4, terms_expected, height_expected), f"Selected profile changed: {alias}")
    return {"status": "PASS", "alias": f"equations/{alias}",
            "source": f"direct/{source}", "sha256": hashes, "metrics": metrics,
            "live_coordinates": len(used)}


def component_check(component, temporary, report):
    identifier = component["id"]
    script = ROOT / component["script"]
    require(script.is_file(), f"Missing component checker: {component['script']}")
    flags = ["-B"] + (["-O"] if sys.flags.optimize else [])
    command = [sys.executable, *flags, str(script), *component.get("args", ())]
    environment = os.environ.copy()
    environment["PYTHONDONTWRITEBYTECODE"] = "1"
    stdout_path = temporary / (identifier + ".stdout")
    stderr_path = temporary / (identifier + ".stderr")
    started = time.monotonic()
    with stdout_path.open("wb") as stdout, stderr_path.open("wb") as stderr:
        process = subprocess.run(command, cwd=ROOT, env=environment,
                                 stdout=stdout, stderr=stderr, check=False)
    elapsed = round(time.monotonic() - started, 3)
    stdout_bytes = stdout_path.read_bytes()
    stderr_bytes = stderr_path.read_bytes()
    stdout_text = stdout_bytes.decode("utf-8", errors="replace")
    stderr_text = stderr_bytes.decode("utf-8", errors="replace")
    record = {"status": "FAIL" if process.returncode else "PASS",
              "script": component["script"], "arguments": list(component.get("args", ())),
              "optimized_python": bool(sys.flags.optimize), "seconds": elapsed,
              "exit_code": process.returncode,
              "stdout_sha256": hashlib.sha256(stdout_bytes).hexdigest(),
              "stderr_sha256": hashlib.sha256(stderr_bytes).hexdigest(),
              "stdout_bytes": len(stdout_bytes), "stderr_bytes": len(stderr_bytes)}
    report["components"][identifier] = record
    if stderr_text:
        record["stderr"] = stderr_text
    if process.returncode:
        record["stdout"] = stdout_text
        print((stderr_text or stdout_text)[-12000:], file=sys.stderr, end="\n")
        raise ValueError(f"Component {identifier} exited with code {process.returncode}")
    if component.get("json", True):
        try:
            diagnostic = json.loads(stdout_text)
        except json.JSONDecodeError as error:
            record.update(status="FAIL", stdout=stdout_text)
            raise ValueError(f"Component {identifier} did not return its expected JSON diagnostic") from error
        record["diagnostic"] = diagnostic
        if isinstance(diagnostic, dict):
            for field in ("status", "result"):
                if field in diagnostic:
                    if str(diagnostic[field]).lower() not in ("pass", "passed", "ok"):
                        record["status"] = "FAIL"
                        raise ValueError(f"Component {identifier} reports {field}={diagnostic[field]!r}")
    else:
        record["diagnostic"] = stdout_text
    print(f"PASS {identifier} ({elapsed:.3f}s)", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--receipt", type=Path,
                        help="Write complete JSON diagnostics outside the release directory")
    args = parser.parse_args()
    receipt = args.receipt.resolve() if args.receipt else None
    if receipt is not None and receipt.is_relative_to(ROOT):
        parser.error("--receipt must point outside the release directory; verification keeps the package unchanged")
    report = {"schema": "conzfc_release_verification_v1", "status": "RUNNING",
              "python": sys.version.split()[0], "optimized_python": bool(sys.flags.optimize),
              "components": {}, "scope": "Finite artifact, coefficient, source and map verification. The unbounded consistency equivalences are the separately supplied ordinary proofs; no consistency decision or new proof-assistant build is performed."}
    result = 1
    try:
        report["manifest"] = manifest_check()
        if report["manifest"]["status"] == "PASS":
            print(f"PASS manifest ({report['manifest']['named_files']} named files)", flush=True)
        else:
            print("Manifest not present; component and source checks still run.", flush=True)
        report["direct_aliases"] = []
        for specification in ALIASES:
            checked = alias_check(*specification)
            report["direct_aliases"].append(checked)
            print(f"PASS direct alias {specification[0]}", flush=True)
        with tempfile.TemporaryDirectory(prefix="conzfc-release-audit-") as temporary:
            for component in COMPONENTS:
                component_check(component, Path(temporary), report)
        require(manifest_check() == report["manifest"],
                "The top-level manifest or one of its named files changed during verification")
        report["status"] = "PASS"
        result = 0
        print(f"PASS release: {len(ALIASES)} public direct profiles and {len(COMPONENTS)} component checks.", flush=True)
    except (OSError, ValueError, KeyError, TypeError) as error:
        report["status"] = "FAIL"
        report["error"] = {"type": type(error).__name__, "message": str(error)}
        print(f"FAIL release: {error}", file=sys.stderr, flush=True)
    if receipt is not None:
        try:
            receipt.parent.mkdir(parents=True, exist_ok=True)
            receipt.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
            print(f"Receipt: {receipt}", flush=True)
        except OSError as error:
            print(f"FAIL receipt: {error}", file=sys.stderr, flush=True)
            return 1
    return result


if __name__ == "__main__":
    raise SystemExit(main())
