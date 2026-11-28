#!/usr/bin/env python3
"""Reproduce source metrics and manifests without importing or compiling Lean.

Usage:
  python scripts/source_audit.py /path/to/ProveIt --output /path/to/audit

The import graph is a syntactic module graph, not a proof-term dependency graph.
No result of this script establishes theorem validity or an axiom audit.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import json
import re
import subprocess
from pathlib import Path

PIN = "9050b04000647d588d0c78d945180abcd3b0bcf7"
BASE = Path("Analysis/GeneralizedRiemannHypothesis")
GRH = BASE / "Lean/grh"
TARGETS = [
    "New/Determinant/Chain/Moduli.lean",
    "New/Determinant/Chain/ChainNorms.lean",
    "New/Determinant/Chain/TriangleNorms.lean",
    "New/Determinant/Chain/NormOfChain.lean",
    "New/Determinant/AuxiliaryForms/Turns.lean",
    "New/Determinant/AuxiliaryForms/DiagonalTurns.lean",
    "New/Determinant/AuxiliaryForms/SpanningForms.lean",
    "New/Determinant/Twist/LongForms.lean",
]
BRANCH_HELPERS = [
    "extendedTensor", "leadingMinorAlong",
    "newRowOrder_symm_of_val_eq_succAbove",
    "leadingMinorAlong_newRowOrder_zero", "leadingMinorAlong_newRowOrder_top",
    "prod_det_blockScalar_branchRows", "extendedTensor_dotProduct",
    "weylEval_dotProduct_weylGram_mulVec_weylEval",
    "det_mul_dotProduct_mulVec_eq_extendedTensor", "span_weylEval_eq_top",
    "star_extendedTensor", "re_dotProduct_mulVec_le_of_forall_dotProduct_eq",
]


def git(repo: Path, *args: str) -> str:
    return subprocess.check_output(
        ["git", "-C", str(repo), *args], text=True
    ).strip()


def blob(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def record(repo: Path, path: Path) -> dict:
    data = path.read_bytes()
    return {
        "path": path.relative_to(repo).as_posix(),
        "bytes": len(data),
        "sha256": hashlib.sha256(data).hexdigest(),
        "git_blob_sha1": blob(data),
    }


def write_tsv(path: Path, rows: list[dict]) -> None:
    with path.open("w", newline="", encoding="utf-8") as out:
        writer = csv.DictWriter(out, fieldnames=list(rows[0]), delimiter="\t")
        writer.writeheader()
        writer.writerows(rows)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("repository", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    repo = args.repository.resolve()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    commit = git(repo, "rev-parse", "HEAD")
    source = repo / GRH / "src"
    files = sorted(source.rglob("*.lean"))
    texts = {p: p.read_text(encoding="utf-8") for p in files}
    modules = {p.relative_to(source).with_suffix("").as_posix().replace("/", "."): p
               for p in files}
    graph = {
        module: [dep for line in re.findall(r"(?m)^import\s+([^\n]+)", texts[path])
                 for dep in line.split() if dep in modules]
        for module, path in modules.items()
    }
    reached: set[str] = set()
    pending = ["Main"]
    while pending:
        current = pending.pop()
        if current in reached or current not in graph:
            continue
        reached.add(current)
        pending.extend(graph[current])
    branch = source / "Lib/GLn/Branching/NormBound.lean"
    references = {}
    for name in BRANCH_HELPERS:
        pattern = re.compile(r"(?<![\w'])" + re.escape(name) + r"(?![\w'])")
        references[name] = [
            p.relative_to(source).as_posix()
            for p, content in texts.items()
            if p != branch and pattern.search(content)
        ]
    proposals = repo / BASE / "docs/proposals"
    directories = sorted(p.name for p in proposals.iterdir() if p.is_dir())
    summary = {
        "commit": commit,
        "expected_commit": PIN,
        "matches_expected_commit": commit == PIN,
        "lean_subtree": git(repo, "rev-parse", f"HEAD:{GRH.as_posix()}"),
        "source_files": len(files),
        "physical_lines": sum(len(s.splitlines()) for s in texts.values()),
        "main_syntactic_import_closure_files": len(reached),
        "main_syntactic_import_closure_lines": sum(
            len(texts[modules[m]].splitlines()) for m in reached),
        "affected_modules": {p: len(texts[source / p].splitlines()) for p in TARGETS},
        "affected_modules_physical_lines": sum(
            len(texts[source / p].splitlines()) for p in TARGETS),
        "proposal_bundles": directories,
        "branching_helper_external_text_references": references,
        "scope": "Syntactic metrics and text references; no theorem-validity claim.",
    }
    (out / "source_metrics.json").write_text(
        json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    (out / "import_graph.json").write_text(
        json.dumps(graph, indent=2) + "\n", encoding="utf-8")
    write_tsv(out / "source_manifest.tsv", [record(repo, p) for p in files])
    provenance_paths = [
        repo / GRH / "README.md", repo / GRH / "lean-toolchain",
        repo / GRH / "lake-manifest.json",
        repo / BASE / "docs/guide/theta_lifts_and_dirichlet_zeros.tex",
        repo / BASE / "docs/guide/README.md",
    ]
    write_tsv(out / "context_manifest.tsv",
              [record(repo, p) for p in provenance_paths if p.is_file()])
    print(json.dumps({k: summary[k] for k in [
        "commit", "lean_subtree", "source_files", "physical_lines",
        "main_syntactic_import_closure_files",
        "affected_modules_physical_lines"]}, indent=2))


if __name__ == "__main__":
    main()
