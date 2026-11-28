#!/usr/bin/env python3
"""Inventory the supplied source locations and all proposal packets at a fixed revision."""
import argparse
import hashlib
import json
import subprocess
from collections import Counter
from pathlib import PurePosixPath

REV = "f2d6ab6c4b70ea73b2deac9e33ad966bc92ea36f"
BASE = "Analysis/GeneralizedRiemannHypothesis"
PKG = BASE + "/Lean/grh"
PROPOSALS = BASE + "/docs/proposals"
TARGETS = {
    "New/Derivatives/Vacuum/ShortVectors.lean": [
        "lemma finiteImage_mem_iff", "lemma exists_isTightFrame_coprime",
        "def HasUnitLinearForm", "lemma exists_isTightFrame_of_coprime",
        "theorem exists_short_isTightFrame_coprime", "theorem exists_isTightFrame :"],
    "New/Derivatives/Vacuum/StandardDataProducts.lean": ["P.exists_isTightFrame_coprime s"],
    "New/Derivatives/Sharpness/BoundAttained.lean": [" := D.exists_isTightFrame"],
    "New/UpperBound/Kernels/JetConjugatesAndBounds.lean": [
        ":= exists_eq_intCast_of_mem_quadInt_of_conj_eq"],
    "New/Spanning/MainTerm/Frequencies.lean": ["theorem sum_height_inv_cube_le"],
    "New/Spanning/MainTerm/GlobalSieve.lean": ["grw [← mul_sum, sum_height_inv_cube_le]"],
    "New/Appendix/DiscreteSeries/MinorSecondOrder.lean": [
        "def crossTrace ", "def crossTraceSum ", "theorem exists_det_one_add_proj_mul_eq_exp"],
    "New/Appendix/DiscreteSeries/OneMinor.lean": ["    exists_det_one_add_proj_mul_eq_exp hQ"],
    "New/Derivatives/Field/PrimeDecomposition.lean": ["lemma relDifferentGen_eq_prod_sub"],
}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("repo", help="ProveIt git checkout containing the audited commit")
    args = parser.parse_args()
    def git(*parts):
        return subprocess.check_output(["git", "-C", args.repo, *parts])
    assert git("rev-parse", REV).decode().strip() == REV
    tree = git("ls-tree", "-r", REV, PROPOSALS).decode().splitlines()
    packets = {}
    for line in tree:
        metadata, path = line.split("\t", 1)
        path = PurePosixPath(path).relative_to(PROPOSALS)
        sha = metadata.split()[-1]
        record = packets.setdefault(path.parts[0], {"files": 0, "tex": []})
        record["files"] += 1
        if path.suffix == ".tex":
            record["tex"].append({"path": str(path), "git_blob": sha})
    target_map = {}
    for file, anchors in TARGETS.items():
        contents = git("show", REV + ":" + PKG + "/src/" + file)
        lines = contents.decode().splitlines()
        starts = {}
        for anchor in anchors:
            hits = [i for i, text in enumerate(lines, 1) if anchor in text]
            assert hits, (file, anchor)
            starts[anchor.strip()] = hits
        target_map[file] = {"lines": len(lines), "sha256": hashlib.sha256(contents).hexdigest(),
                            "anchors": starts}
    result = {"commit": REV, "proposal_tree": git("rev-parse", REV + ":" + PROPOSALS).decode().strip(),
              "proposal_directories": len(packets), "proposal_tex_files": sum(len(p["tex"]) for p in packets.values()),
              "proposal_inventory": packets, "source_targets": target_map}
    print(json.dumps(result, indent=2, ensure_ascii=False))

if __name__ == "__main__":
    main()
