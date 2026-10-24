#!/usr/bin/env python3
"""Full finite replay of the separate literal-beta-majorant quartics.

This checker expands the actual residual squares independently and calls
the separately pinned arithmetic/affine and power-certificate auditors.
The unbounded CRT/majorant proof is in PROOF.md.
"""
from collections import defaultdict
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import zipfile

from majorant_audit import audit as majorant_audit

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def equation_check(directory):
    eq = json.loads((directory/"equation.json").read_text())
    polynomial = json.loads((directory/"expanded_polynomial.json").read_text())
    need(eq["domain"] == polynomial["domain"] == "nonnegative integers", "domain")
    n = len(eq["variables"])
    need(len({v["name"] for v in eq["variables"]}) == n, "distinct variables")
    result = defaultdict(int)
    used = set()
    for row in eq["residuals"]:
        need(len({tuple(m) for c, m in row["terms"]}) == len(row["terms"]), "row uniqueness")
        for c, m in row["terms"]:
            need(type(c) is int and c and len(m) <= 2 and m == sorted(m)
                 and all(type(i) is int and 0 <= i < n for i in m), "quadratic term")
            used.update(m)
        for c, m in row["terms"]:
            for d, p in row["terms"]:
                result[tuple(sorted(m+p))] += c*d
    expected = {m: c for m, c in result.items() if c}
    actual = {tuple(m): c for c, m in polynomial["terms"]}
    need(expected == actual and len(actual) == len(polynomial["terms"]), "whole quartic expansion")
    need(used == set(range(n)) and max(map(len, actual)) == 4, "liveness and exact degree")
    metrics = eq["metrics"]
    need(metrics["variables"] == n and metrics["quadratic_rows"] == len(eq["residuals"])
         and metrics["expanded_monomials"] == len(actual)
         and metrics["max_abs_expanded_coefficient"] == max(map(abs, actual.values())), "metrics")
    return dict(metrics=metrics,
                equation_sha256=sha256((directory/"equation.json").read_bytes()).hexdigest(),
                polynomial_sha256=sha256((directory/"expanded_polynomial.json").read_bytes()).hexdigest())


def source_check():
    pins = json.loads((HERE/"SOURCE_PINS.json").read_text())
    archive = REPO/pins["archive"]
    need(sha256(archive.read_bytes()).hexdigest() == pins["archive_sha256"], "original whole ZIP")
    with zipfile.ZipFile(archive) as z:
        for name, item in pins["files"].items():
            old = z.read(item["original_member"])
            new = (HERE/"source"/name).read_bytes()
            need(sha256(old).hexdigest() == item["original_sha256"]
                 and sha256(new).hexdigest() == item["candidate_sha256"], "source pins")
            if name == "build_equation.py":
                replacements = [
                    (b"    V = b.add(m, U)\n", b"    V = U  # Independent private-coordinate bound; prime-supported CRT lift.\n"),
                    (b"    H = b.sum([ep, fp, t, V, ONE])\n", b"    H = b.sum([ep, fp])  # Literal beta-row majorant; endpoint forces H>=t.\n"),
                ]
                wanted = old
                for before, after in replacements:
                    need(wanted.count(before) == 1, "one occurrence of each source patch")
                    wanted = wanted.replace(before, after)
                need(new == wanted, "exactly two original source changes")
            else:
                need(old == new, "unchanged source/arithmetic/auditor")
    parent = pins["prime_lift_proof"]
    need(sha256((HERE/parent["path"]).read_bytes()).hexdigest() == parent["sha256"], "prime-lift proof")
    return dict(status="PASS", archive_sha256=pins["archive_sha256"],
                original_source_files=len(pins["files"]), patched_source_lines=2)


def main():
    sources = source_check()
    flags = ["-O"] if sys.flags.optimize else []
    upstream = {}
    with tempfile.TemporaryDirectory(prefix="proveit-beta-majorant-audit-") as tmp:
        for variant in ["affine", "retained"]:
            output = Path(tmp)/(variant+".json")
            command = [sys.executable, "-B", *flags, str(HERE/"source/check_equation.py"),
                       "--directory", str(HERE/"source"), "--equation-directory", str(HERE/variant),
                       "--output", str(output)]
            p = subprocess.run(command, text=True, capture_output=True)
            need(p.returncode == 0, "complete arithmetic/affine audit: "+p.stderr)
            upstream[variant] = json.loads(output.read_text())
        output = Path(tmp)/"power.json"
        p = subprocess.run([sys.executable, "-B", *flags, str(HERE/"source/audit_power_graph.py"),
                            "--output", str(output)], text=True, capture_output=True)
        need(p.returncode == 0, "exact positive-power graph audit: "+p.stderr)
        power = json.loads(output.read_text())
    result = dict(status="PASS", optimized=not __debug__, sources=sources,
                  literal_majorant=majorant_audit(HERE),
                  variants={name: equation_check(HERE/name) for name in ["affine", "retained"]},
                  independent_upstream_audits=upstream, exact_power_graph_audit=power,
                  scope="Full literal quartics, source identities, exact majorant gate path, arithmetic and positive-power audits. Ordinary proof in PROOF.md; no Lean/internal-ZFC derivation.")
    target = HERE/("CHECK_OPTIMIZED.json" if sys.flags.optimize else "CHECK.json")
    target.write_text(json.dumps(result, indent=2, sort_keys=True)+"\n")
    print("PASS exact source patches, beta-majorant gate path, full quartics and all arithmetic/affine/power audits")


if __name__ == "__main__":
    main()
