#!/usr/bin/env python3
"""Offline source-integrity audit; NOT Lean compilation or theorem checking.

Run from any directory. All guards raise explicit errors, including with python -O.
The finite recurrence model is only a boundary sanity check, not a Lean proof.
"""
from __future__ import annotations

import argparse
import ast
import difflib
import hashlib
import json
from pathlib import Path
import shutil
import sys

PIN = "7ba7d102822df1eff376cbca913727d9d588ab4e"
SOURCE = "Computability/DiophantineConsistency/Lean/DiophantineConsistency/NativeOuterSeedConstruction.lean"
HELPER = "Computability/HilbertTenthProblem/Lean/Diophantine/Common/PellMod.lean"
SOURCE_HASH = "fd437b7d7d64c3371f4d0f2bc234d9e620526b0b1b3c4558ab6fbb47d6573159"
SOURCE_BLOB = "c02b1abb2c0b9c9c75b63ddd618c5ff678f0911b"
CANDIDATE_HASH = "201491d6c852eb0d5debf5ed3f852e4a640efe3dae636acd7c77ced3d7edaec5"
HELPER_HASH = "1ba5f0223a6099751c06e37079e717e463cd40cf8ec092ac95647383c7ffb623"
HELPER_BLOB = "0e669cfca380d4318038d814f1485ea70f410afe"
OLD = """  have hKr : r+1 < K := by
    have hp : 2*P-1 ≤ K := by
      calc
        2*P-1 = (2*P-1)^1 := (pow_one _).symm
        _ ≤ (2*P-1)^r := Nat.pow_le_pow_right (by omega) (by omega)
        _ ≤ K := pow_le_ψ_succ hP r
    have hXY : X ≤ Q := by
      dsimp [Q]
      exact Nat.le_mul_of_pos_right _ (pow_pos hY _)
    have hXP : 2*X+1 ≤ P := by dsimp [P]; omega
    omega
"""
NEW = "  have hKr : r+1 < K := lt_yn_of_two_le hP (by omega)\n"
CHAIN = [
    "DiophantineConsistency.NativeOuterSeedConstruction",
    "DiophantineConsistency.NativeHalfBinomial",
    "DiophantineConsistency.NativePellScaleBounds",
    "DiophantineConsistency.NativeBinaryScale",
    "DiophantineConsistency.NativePellPower",
    "DiophantineConsistency.NativePellFirstIndex",
    "DiophantineConsistency.NativePellBootstrap",
    "DiophantineConsistency.NativePellStepDown",
    "DiophantineConsistency.SignedPellResidue",
    "Diophantine.Common.PellInt",
    "Diophantine.Common.PellMod",
]


class AuditError(RuntimeError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AuditError(message)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def blob(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def read(root: Path, path: str) -> bytes:
    full = root / path
    require(full.is_file(), f"missing file: {path}")
    return full.read_bytes()


def audit(root: Path) -> dict:
    source = read(root, "sources/" + SOURCE)
    require(sha256(source) == SOURCE_HASH, "source sha256 mismatch")
    require(blob(source) == SOURCE_BLOB, "source Git blob mismatch")
    candidate = read(root, "research/outer_seed/NativeOuterSeedConstruction.lean")
    require(sha256(candidate) == CANDIDATE_HASH, "candidate sha256 mismatch")
    helper = read(root, "dependencies/" + HELPER)
    require(sha256(helper) == HELPER_HASH, "helper sha256 mismatch")
    require(blob(helper) == HELPER_BLOB, "helper Git blob mismatch")
    src, dst, dep = (x.decode("utf-8") for x in (source, candidate, helper))
    require(src.count(OLD) == 1, "old fragment must occur exactly once")
    require(src.replace(OLD, NEW, 1) == dst, "candidate changes more than the reviewed local proof")
    require(dst.count(NEW) == 1, "new fragment must occur exactly once")
    require(len(src.splitlines()) == 279, "unexpected source line count")
    require(len(dst.splitlines()) == 269, "unexpected candidate line count")
    require(len(OLD.splitlines()) == 11 and len(NEW.splitlines()) == 1, "fragment count mismatch")
    expected_patch = "".join(difflib.unified_diff(
        src.splitlines(keepends=True), dst.splitlines(keepends=True),
        fromfile="a/" + SOURCE, tofile="b/" + SOURCE))
    require(read(root, "research/outer_seed/candidate.patch").decode() == expected_patch,
            "patch is not exactly the independently reconstructed diff")

    metrics = json.loads(read(root, "research/outer_seed/METRICS.json"))
    expected_metrics = {
        "source_pin": PIN, "source_path": SOURCE, "source_sha256": SOURCE_HASH,
        "source_git_blob": SOURCE_BLOB, "new_sha256": CANDIDATE_HASH,
        "old_fragment": OLD, "new_fragment": NEW,
        "old_fragment_lines": 11, "new_fragment_lines": 1,
        "old_module_lines": 279, "new_module_lines": 269,
    }
    for key, value in expected_metrics.items():
        require(metrics.get(key) == value, f"metrics mismatch: {key}")

    # Textual guard facts are not substitutes for elaboration of the tactic term.
    for text in [
        "open Diophantine Pell Jones1982 Jones1980",
        "σ 2 r = 3*u+1 ∧ 4 ≤ r ∧ 3*u+1 < R",
        "  obtain ⟨hσ,hr,hsize⟩ := population_sizes hu hR hpop",
        "  have hP : 1 < P := by dsimp [P]; omega",
        "  let K := yn hP (r+1)",
        "  have hRX : R < X := Nat.lt_two_pow_self",
    ]:
        require(text in src and text in dst, f"missing unchanged guard/context: {text}")
    require("variable {a : ℕ} (a1 : 1 < a)" in dep, "helper natural base guard missing")
    require("theorem lt_yn_of_two_le {n : ℕ} (hn : 2 ≤ n) : n < yn a1 n := by" in dep,
            "helper signature mismatch")
    require("namespace Diophantine" in dep, "helper namespace missing")
    require("import Diophantine.Common.Pell\n" in dep, "helper lower import mismatch")
    require("DiophantineConsistency" not in dep, "unexpected helper dependency on consumer layer")
    require(all(word not in NEW for word in ["sorry", "admit", "axiom", "unsafe"]),
            "unexpected new proof escape")

    entries = {}
    modules = {}
    for filename in ["provenance/source_manifest.json", "provenance/dependency_manifest.json"]:
        manifest = json.loads(read(root, filename))
        require(manifest["commit"] == PIN, f"manifest pin mismatch: {filename}")
        for entry in manifest["sources"]:
            entries[entry["local_path"]] = entry
            path = entry["path"]
            if "/Lean/" in path and path.endswith(".lean"):
                name = path.split("/Lean/", 1)[1][:-5].replace("/", ".")
                require(name not in modules, f"ambiguous repository module: {name}")
                modules[name] = entry
    import_evidence = []
    for index, module in enumerate(CHAIN):
        require(module in modules, f"missing import-path module: {module}")
        entry = modules[module]
        data = read(root, entry["local_path"])
        require(sha256(data) == entry["sha256"], f"import module sha256 mismatch: {module}")
        require(blob(data) == entry["sha"], f"import module Git blob mismatch: {module}")
        require(len(data) == entry["size"], f"import module size mismatch: {module}")
        if index + 1 < len(CHAIN):
            require("import " + CHAIN[index + 1] in data.decode().splitlines(),
                    f"import-path edge missing: {module} -> {CHAIN[index + 1]}")
        import_evidence.append({"module": module, "path": entry["local_path"],
                                "sha256": sha256(data), "git_blob": blob(data)})

    # The human novelty assessment reads these exact full prior reports; this
    # hash check does not purport to decide semantic novelty by string matching.
    prior = json.loads(read(root, "baseline_audit/NEAREST_PRIOR_BINDINGS.json"))
    require(prior["source_pin"] == PIN, "nearest-prior binding pin mismatch")
    nearest = []
    for entry in prior["sources"]:
        if "pell_" not in entry["path"]:
            continue
        data = read(root, entry["path"])
        require(sha256(data) == entry["sha256"], f"prior sha256 mismatch: {entry['path']}")
        require(blob(data) == entry["git_blob_sha1"], f"prior Git blob mismatch: {entry['path']}")
        require(len(data) == entry["bytes"], f"prior size mismatch: {entry['path']}")
        nearest.append({"path": entry["path"], "sha256": sha256(data),
                        "decisive_lines": entry["decisive_lines"]})
    require(len(nearest) == 3, "expected three exact nearest Pell prior reports")

    # Boundary sanity only. a=0 or a=1 is intentionally outside the lemma domain.
    positive_checks = 0
    excluded_index_checks = 0
    for a in range(2, 13):
        x, y = 1, 0
        for n in range(25):
            if n < 2:
                require(not n < y, f"n={n} should demonstrate the missing strictness guard")
                excluded_index_checks += 1
            else:
                require(n < y, f"finite recurrence model failed at a={a}, n={n}")
                positive_checks += 1
            x, y = a*x + (a*a-1)*y, x + a*y

    return {
        "status": "PASS_SOURCE_INTEGRITY_AND_FINITE_MODEL_ONLY",
        "source_pin": PIN,
        "python_optimization_level": sys.flags.optimize,
        "source_sha256": SOURCE_HASH,
        "candidate_sha256": CANDIDATE_HASH,
        "source_git_blob": SOURCE_BLOB,
        "helper_git_blob": HELPER_BLOB,
        "proof_fragment_lines": {"old": 11, "new": 1, "removed": 10},
        "module_lines": {"old": 279, "new": 269},
        "exact_single_local_replacement": True,
        "public_source_outside_fragment_unchanged": True,
        "existing_import_path": import_evidence,
        "nearest_prior_reports": nearest,
        "finite_model": {"positive_checks": positive_checks,
                         "excluded_index_checks": excluded_index_checks,
                         "scope": "Natural Pell recurrence, 2 <= a <= 12, 0 <= n <= 24; not proof"},
        "toolchain_observation": {name: shutil.which(name) for name in ["lean", "lake", "elan"]},
        "lean_compilation": "NOT RUN",
        "full_transitive_dependency_or_axiom_check": "NOT RUN",
        "novelty": "Human semantic review in LEMMA_REUSE_REVIEW.md; not machine-certified",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent)
    args = parser.parse_args()
    require(not any(isinstance(node, ast.Assert) for node in ast.walk(ast.parse(Path(__file__).read_text()))),
            "audit script must not rely on Python assert")
    print(json.dumps(audit(args.root.resolve()), indent=2, ensure_ascii=False))


if __name__ == "__main__":
    try:
        main()
    except (AuditError, KeyError, ValueError, OSError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        sys.exit(1)
