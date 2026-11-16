#!/usr/bin/env python3
"""Rebuild the source manifest and packet catalog from the pinned checkout.

Usage: python3 rebuild_provenance.py /absolute/path/to/ProveIt
Only files beside this script are written. No source checkout files are changed.
"""
from pathlib import Path
import csv
import hashlib
import json
import re
import subprocess
import sys

COMMIT = "42c64ff3a9f56f2a9edc1525e75ece3b720c7f77"
REPOSITORY = "https://github.com/VladimirReshetnikov/ProveIt"
BASE = "Logic/PrimitiveRecursiveArithmetic/"
PROOFS = BASE + "docs/proofs/"
CORE = BASE + "ConciseIPRA/Lean/ConciseIPRA/"

# A selected-source list, not a list of every file in a catalogued packet.
SELECTED = [
    ("LICENSE", "license", "License of the pinned repository; preserved with the adapted kernel."),
    ("lean-toolchain", "toolchain_pin", "Repository toolchain pin; not an assertion that the full repository was rebuilt."),
    (BASE + "ConciseIPRA/README.md", "foundation_scope", "Descriptions of the native calculus and Lean formalization."),
    (CORE + "Syntax.lean", "adapted_kernel_source", "Scoped syntax, formulas, substitution and quantifier-free predicate."),
    (CORE + "Deduction.lean", "adapted_kernel_source", "Intuitionistic proof constructors and structural proof operations."),
    (CORE + "PR.lean", "adapted_kernel_source", "Primitive recursive symbols, arithmetic axioms and quantifier-free induction."),
    (CORE + "NativeBiInterpretation.lean", "foundation_api", "Existing ordinary/native theory transport API; not a semantic reflection principle."),
    (PROOFS + "README.md", "collection_index", "Source of the 46-row catalog and the index's explicit verification disclaimer."),
    (PROOFS + "algebra/puiseux_ipra/puiseux_ipra.tex", "selected_proof_and_scope", "Exact-algebraic Puiseux construction and its representation scope."),
    (PROOFS + "algebra/puiseux_ipra/convergence.tex", "selected_proof_section", "Finite weighted norms, exact simple-root recurrence and coefficient stabilization."),
    (PROOFS + "algebra/puiseux_ipra/evidence/scope_obstruction.md", "obstruction_argument", "Reported obstruction to uniform exact Puiseux output for arbitrary Cauchy coefficients."),
    (PROOFS + "analysis/calculus_ipra/README.md", "reported_scope_and_status", "Fixed evaluator schemas, supplied moduli and stated formalization status."),
    (PROOFS + "analysis/gamma_ipra/README.md", "reported_scope_and_status", "Fixed certified PR names, explicit resources and incomplete analytic formalization."),
    (PROOFS + "analytic-number-theory/zeta_ipra_proof_package/README.md", "reported_scope_and_status", "Fixed PR approximation programs and stated native/object formalization limits."),
    (PROOFS + "analytic-number-theory/zeta_zeros_ipra_2026-11-15/sections/status.tex", "reported_scope_and_status", "Explicit distinction among the human argument, finite executable evidence, and uninstantiated Lean/object-theory obligations."),
    (PROOFS + "analytic-number-theory/pnt_li_ipra_2026-11-15/tex/foundations.tex", "selected_foundational_proof_section", "Fixed arithmetic evaluators, finite precision budgets, guarded inverses, and the ordinary/native proof-transport boundary."),
    (PROOFS + "geometry/euler_rodrigues_ipra/README.md", "reported_scope_and_status", "Already supplied exact-gap/approximate-axis alternatives and exact-axis obstruction."),
    (PROOFS + "topology/dimension_invariance_ipra/README.md", "reported_scope_and_status", "Finite rational theorem and its representation/formalization boundaries."),
    (PROOFS + "diophantine-number-theory/faltings_ipra/README.md", "reported_scope_and_status", "Height/list versus cardinality distinction and explicit unresolved general target."),
    (PROOFS + "diophantine-number-theory/siegel_ipra/README.txt", "reported_scope_and_status", "Existing square Runge case and general-target limitations."),
    (PROOFS + "diophantine-number-theory/siegel_ipra/paper/01_scope.tex", "reported_scope_and_status", "Positive height/list versus cardinality targets, affine-model dependence, and the explicit limitations of the source report."),
    (PROOFS + "diophantine-number-theory/siegel_ipra/paper/03_runge.tex", "selected_proof_section", "Square certificate, completion constructor, and rational-denominator warning."),
    (PROOFS + "diophantine-number-theory/siegel_ipra/paper/05_general_route.tex", "selected_proof_section", "Conditional finite-cover/cardinality route and remaining geometric/approximation obligations."),
    (PROOFS + "diophantine-number-theory/mordell_weil_ipra/README.txt", "reported_scope_and_status", "Existing constructive descent and missing rational quotient representatives."),
    (PROOFS + "diophantine-number-theory/mordell_weil_ipra/paper/02_descent.tex", "selected_proof_section", "Already developed contraction descent, finite words, bounds and quantifier-free invariants."),
    (PROOFS + "diophantine-number-theory/diophantine_ipra_2026-11-15/README.txt", "reported_scope_and_status", "Roth cutoff, cardinality, finite-obstruction and formalization distinctions."),
    (PROOFS + "diophantine-number-theory/diophantine_ipra_2026-11-15/paper/02_roth.tex", "selected_proof_section", "Liouville/quadratic results, finite-window observation and missing general cutoff."),
    (PROOFS + "analytic-number-theory/prime_distribution_ipra/README.txt", "reported_scope_and_status", "Declared partial resolution of the five prime-distribution targets."),
    (PROOFS + "analytic-number-theory/prime_distribution_ipra/paper/sections/01_scope.tex", "reported_scope_and_status", "Exact status of the five targets, effective-parameter obligations, and limits on repository reuse."),
    (PROOFS + "analytic-number-theory/prime_distribution_ipra/paper/sections/06_chebotarev.tex", "selected_proof_section", "Finite algebra interface and conditional passage from effective estimates to density."),
    (PROOFS + "analytic-number-theory/prime_distribution_ipra/paper/sections/07_sw_bv.tex", "selected_proof_section", "Exact uniform targets, finite reductions and missing parameter estimates."),
]


def git(repo, *args):
    return subprocess.check_output(["git", "-C", str(repo), *args], text=True).strip()


def build(repo):
    repo = repo.resolve(strict=True)
    if git(repo, "rev-parse", "HEAD") != COMMIT:
        raise SystemExit("The supplied checkout HEAD is not the required pinned commit.")
    destination = Path(__file__).resolve().parent
    index_path = repo / PROOFS / "README.md"
    rows = []
    domain = None
    for line in index_path.read_text(encoding="utf-8").splitlines():
        if line.startswith("### "):
            domain = line[4:].strip()
        if not line.startswith("| [`"):
            continue
        cells = [cell.strip() for cell in line.strip().strip("|").split("|")]
        if len(cells) != 6 or not cells[-2].isdigit() or not cells[-1].isdigit():
            continue
        match = re.fullmatch(r"\[`([^`]+)`\]\(([^)]+)\)", cells[0])
        if not match:
            raise ValueError("Unexpected packet-link syntax: " + cells[0])
        packet_name, relative = match.groups()
        relative = relative.rstrip("/")
        actual_count = sum(p.is_file() for p in (index_path.parent / relative).rglob("*"))
        advertised_count = int(cells[4])
        if actual_count != advertised_count:
            raise ValueError(f"Placed-file count differs for {relative}: {actual_count} != {advertised_count}")
        rows.append({
            "packet_number": len(rows) + 1,
            "domain": domain,
            "packet_name": packet_name,
            "repository_relative_path": PROOFS + relative,
            "relative_to_proofs": relative,
            "descriptive_label_from_index": cells[3],
            "arrival_from_index": cells[1],
            "archive_wrapper_from_index": cells[2].strip("`"),
            "index_placed_files": advertised_count,
            "actual_placed_files": actual_count,
            "omitted_archive_members_reported_by_index": int(cells[5]),
            "entry_basis": "repository_index",
            "full_packet_audit": "not_claimed",
            "source_url": REPOSITORY + "/tree/" + COMMIT + "/" + PROOFS + relative,
        })
    if len(rows) != 46:
        raise ValueError(f"Expected exactly 46 packet rows, found {len(rows)}")
    with (destination / "packet_catalog.csv").open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)

    sources = []
    for relative, role, use in SELECTED:
        path = repo / relative
        data = path.read_bytes()
        actual_blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        expected_blob = git(repo, "rev-parse", COMMIT + ":" + relative)
        if actual_blob != expected_blob:
            raise ValueError("Local file does not match pinned Git blob: " + relative)
        sources.append({
            "repository_relative_path": relative,
            "local_absolute_path": str(path),
            "source_url": REPOSITORY + "/blob/" + COMMIT + "/" + relative,
            "sha256": hashlib.sha256(data).hexdigest(),
            "git_blob_sha1": actual_blob,
            "size_bytes": len(data),
            "line_count": len(data.splitlines()),
            "matches_pinned_commit": True,
            "review_role": role,
            "use_in_report": use,
            "correctness_certification": "not_implied_by_manifest_inclusion",
        })
    metadata = {
        "schema_version": 1,
        "repository_url": REPOSITORY,
        "pinned_commit": COMMIT,
        "commit_url": REPOSITORY + "/commit/" + COMMIT,
        "source_checkout_absolute_path": str(repo),
        "commit_author_time": git(repo, "show", "-s", "--format=%aI", COMMIT),
        "commit_committer_time": git(repo, "show", "-s", "--format=%cI", COMMIT),
        "scope": "Selected consulted sources and a separate index-derived packet catalog; no full repository or full packet audit is claimed.",
        "catalog": {
            "file": "packet_catalog.csv",
            "index_source": PROOFS + "README.md",
            "packet_count": len(rows),
            "placed_files_reported_by_index": sum(r["index_placed_files"] for r in rows),
            "actual_placed_files_counted": sum(r["actual_placed_files"] for r in rows),
            "omitted_archive_members_reported_by_index": sum(r["omitted_archive_members_reported_by_index"] for r in rows),
            "all_46_placed_file_counts_match_index": True,
            "omitted_archive_members_independently_recovered": False,
            "packet_descriptions": "Copied from the index, which reports packet claims without verification.",
        },
        "selected_source_file_count": len(sources),
        "hash_method": "SHA-256 of exact local file bytes; Git blob SHA-1 of 'blob <byte-length>\\0' followed by those bytes, compared with the pinned commit.",
        "sources": sources,
    }
    (destination / "source_manifest.json").write_text(json.dumps(metadata, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps({"catalog_rows": len(rows), "placed_files": metadata["catalog"]["actual_placed_files_counted"],
                      "omitted_members_reported": metadata["catalog"]["omitted_archive_members_reported_by_index"],
                      "selected_source_files": len(sources), "all_source_hashes_match": True}, indent=2))


if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit("Usage: python3 rebuild_provenance.py /absolute/path/to/ProveIt")
    build(Path(sys.argv[1]))
