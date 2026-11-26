#!/usr/bin/env python3
"""Static, reproducible source audit; this does not run a Lean kernel.

Usage: python3 source_audit.py /path/to/grh-lean output.json
The checkout must be at the exact revision used in the report.
"""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

PIN = "72fead102f663d5c7a407964a13dc0cf9d977207"
TARGETS = {
    "grh/src/Statements.lean": ["DirichletLNonvanishingRightOfHalf"],
    "grh/src/Main.lean": ["riemannHypothesis", "LFunction_eq_zero_re"],
    "grh/src/New/Reduction/MainInequality.lean": ["star_inequality"],
    "grh/src/New/Reduction/Lattices/TwistedLattice.lean": ["covolume_add_index_nonneg"],
    "grh/src/New/Congruences/Selmer/RootsOfUnity.lean": ["exists_rootsOfUnity_ellVal_eval_le_add"],
    "grh/src/New/Congruences/Selmer/GeneralTheorem.lean": ["exists_rootsOfUnity_ellVal_eval_le", "exists_anticyclotomic_twist"],
    "grh/src/Lib/GaloisRep/Main/SelmerModules.lean": ["shaLocalSet", "shaOdd"],
    "grh/src/Lib/Cyclotomic/OddSha.lean": ["exists_length_shaOdd_le"],
}

def main() -> None:
    repo = Path(sys.argv[1]).resolve()
    dest = Path(sys.argv[2]) if len(sys.argv) > 2 else None
    commit = subprocess.check_output(["git", "-C", str(repo), "rev-parse", "HEAD"], text=True).strip()
    if commit != PIN:
        raise SystemExit(f"Wrong revision: expected {PIN}, got {commit}")
    src = repo / "grh/src"
    modules = {".".join(p.relative_to(src).with_suffix("").parts): p for p in src.rglob("*.lean")}
    edges = {}
    for module, path in modules.items():
        imports = re.findall(r"^import\s+(.+)$", path.read_text(), re.M)
        edges[module] = [name for line in imports for name in line.split() if name in modules]
    def closure(module: str) -> list[str]:
        seen, todo = set(), [module]
        while todo:
            name = todo.pop()
            if name in seen:
                continue
            seen.add(name)
            todo.extend(edges.get(name, []))
        return sorted(seen)
    result = {
        "repository": "https://github.com/lsernau/grh-lean",
        "commit": commit,
        "toolchain": (repo / "grh/lean-toolchain").read_text().strip(),
        "verification_kind": "static source inspection and import graph only",
        "full_lean_build_performed": False,
        "files": [],
        "local_import_closures": {},
    }
    for path, names in TARGETS.items():
        data = (repo / path).read_bytes()
        lines = data.decode().splitlines()
        locations = {}
        for name in names:
            pattern = re.compile(r"^\s*(?:(?:private|protected|noncomputable)\s+)?(?:theorem|lemma|def|abbrev|structure)\s+(?:[\w.]*\.)?" + re.escape(name) + r"(?:\s|[({:]|$)")
            hits = [i for i, line in enumerate(lines, 1) if pattern.search(line)]
            if not hits:
                raise RuntimeError(f"Declaration not located: {path}: {name}")
            locations[name] = hits
        result["files"].append({"path": path, "sha256": hashlib.sha256(data).hexdigest(), "size_bytes": len(data), "declarations": locations})
    for name in ["New.Congruences.Selmer.RootsOfUnity", "New.Congruences.Selmer.GeneralTheorem", "Lib.Cyclotomic.OddSha"]:
        local = closure(name)
        result["local_import_closures"][name] = {
            "count_including_self": len(local),
            "contains_Main_or_New_Main": "Main" in local or "New.Main" in local,
            "contains_GRH_endpoint_reduction": "New.Reduction.OneSidedBound" in local,
            "modules": local,
        }
    payload = json.dumps(result, indent=2, ensure_ascii=False) + "\n"
    if dest:
        dest.write_text(payload)
    print(json.dumps({"commit": commit, "audited_files": len(result["files"]), "closures": {k: {j: v for j, v in d.items() if j != "modules"} for k, d in result["local_import_closures"].items()}}, indent=2))

if __name__ == "__main__":
    main()
