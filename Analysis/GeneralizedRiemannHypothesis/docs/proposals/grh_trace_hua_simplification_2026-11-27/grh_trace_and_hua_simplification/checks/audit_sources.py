#!/usr/bin/env python3
"""Reproduce the pinned source counts and the proposed replacement boundaries.

This is a static source inventory, not a Lean dependency export or proof check.
Usage: python3 checks/audit_sources.py /path/to/ProveIt --output results/source_audit.json
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path

PIN = "f2d6ab6c4b70ea73b2deac9e33ad966bc92ea36f"
GRH = Path("Analysis/GeneralizedRiemannHypothesis")
TARGETS = [
    "Statements.lean",
    "Main.lean",
    "New/Main.lean",
    "New/Reduction/MainInequality.lean",
    "Lib/Adelic/TraceFormula/LineDeterminant.lean",
    "Lib/Adelic/TraceFormula/LevelCut.lean",
    "Lib/Adelic/TraceFormula/CuspidalComparison.lean",
    "New/Spanning/Multiplicities/EqualMultiplicities.lean",
    "New/Spanning/RemainingTerms/OneRealPlace.lean",
    "New/Spanning/RemainingTerms/SchurOrbit.lean",
    "Lib/General/Analysis/HolomorphicIntegrals.lean",
    "Lib/General/LinearAlgebra/HermitianMatrices.lean",
    "Lib/General/LinearAlgebra/MinorProducts.lean",
]
RANGES = {
    "New/Spanning/RemainingTerms/OneRealPlace.lean": [
        [241, 282], [360, 426], [449, 707], [795, 1008]
    ],
    "Lib/General/LinearAlgebra/HermitianMatrices.lean": [[71, 99]],
}


def digest(path: Path) -> dict:
    data = path.read_bytes()
    text = data.decode("utf-8")
    return {
        "bytes": len(data),
        "physical_lines": len(text.splitlines()),
        "nonblank_lines_including_comments": sum(bool(x.strip()) for x in text.splitlines()),
        "sha256": hashlib.sha256(data).hexdigest(),
        "git_blob_sha1": hashlib.sha1(
            b"blob " + str(len(data)).encode() + b"\0" + data
        ).hexdigest(),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("repo", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    repo = args.repo.resolve()
    head = subprocess.check_output(
        ["git", "-C", str(repo), "rev-parse", "HEAD"], text=True
    ).strip()
    if head != PIN:
        raise SystemExit(f"Expected pinned commit {PIN}; observed {head}")
    root = repo / GRH / "Lean/grh/src"
    modules = {
        ".".join(p.relative_to(root).with_suffix("").parts): p
        for p in sorted(root.rglob("*.lean"))
    }
    imports = {
        name: [
            item
            for line in path.read_text().splitlines()
            if line.startswith("import ")
            for item in line.removeprefix("import ").split()
            if item in modules
        ]
        for name, path in modules.items()
    }
    reachable, todo = set(), ["Main"]
    while todo:
        name = todo.pop()
        if name not in reachable:
            reachable.add(name)
            todo.extend(imports[name])
    target_info = {}
    for relative in TARGETS:
        path = root / relative
        item = digest(path)
        item["source_url"] = (
            f"https://github.com/VladimirReshetnikov/ProveIt/blob/{PIN}/"
            f"{GRH.as_posix()}/Lean/grh/src/{relative}"
        )
        target_info[relative] = item
    declarations = []
    for relative, ranges in RANGES.items():
        lines = (root / relative).read_text().splitlines()
        for lo, hi in ranges:
            names = []
            for number in range(lo, hi + 1):
                match = re.match(
                    r"\s*(?:private\s+)?(?:noncomputable\s+)?"
                    r"(?:lemma|theorem|def|structure|abbrev)\s+([^\s(:{]+)",
                    lines[number - 1],
                )
                if match:
                    names.append({"line": number, "name": match.group(1)})
            declarations.append({
                "file": relative, "first_line": lo, "last_line": hi,
                "physical_lines": hi - lo + 1, "declarations": names,
            })
    text = {p.relative_to(root).as_posix(): p.read_text() for p in modules.values()}
    usages = {}
    for token in [
        "IsTriangularBasis",
        "IsNegativeBasis",
        "exists_lowerTriangular_conjTranspose_mul_mul_eq_one",
        "charpoly_eq_of_trace_pow_eq",
        "exists_majorant_volumeRatio_inv_pow",
    ]:
        usages[token] = [
            {"file": p, "line": j, "text": line.strip()}
            for p, source in text.items()
            for j, line in enumerate(source.splitlines(), start=1)
            if token in line
        ]
    proposals = repo / GRH / "docs/proposals"
    report = {
        "status": "PASS",
        "commit": head,
        "scope": "Static imports and text occurrences; not declaration-level kernel dependencies",
        "all_modules": len(modules),
        "all_physical_lines": sum(len(p.read_text().splitlines()) for p in modules.values()),
        "Main_import_reachable_modules": len(reachable),
        "unreachable_modules": sorted(set(modules) - reachable),
        "proposal_directories": sorted(p.name for p in proposals.iterdir() if p.is_dir()),
        "proposal_directory_count": sum(p.is_dir() for p in proposals.iterdir()),
        "target_files": target_info,
        "bordered_Hua_affected_regions": declarations,
        "bordered_Hua_gross_affected_lines": sum(x["physical_lines"] for x in declarations),
        "size_warning": "Affected ranges contain retained contracts and replaced proofs; this is NOT a net deletion count",
        "identifier_occurrences": usages,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps({
        key: report[key] for key in [
            "status", "commit", "all_modules", "all_physical_lines",
            "Main_import_reachable_modules", "proposal_directory_count",
            "bordered_Hua_gross_affected_lines",
        ]
    }, indent=2))


if __name__ == "__main__":
    main()
