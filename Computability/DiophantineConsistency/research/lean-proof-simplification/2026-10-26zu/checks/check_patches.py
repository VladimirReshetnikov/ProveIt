#!/usr/bin/env python3
"""Check each patch against its supplied baseline, then compare exact output.

All changes occur in automatically removed temporary directories. This script
does not modify a checkout, require network access, or compile Lean.
"""
from pathlib import Path
import json
import shutil
import subprocess
import tempfile

PACKET = Path(__file__).resolve().parents[1]
PREFIX = Path("Computability/DiophantineConsistency/Lean/DiophantineConsistency")
CASES = [
    (
        "shape",
        "shape/shape-metadata.patch",
        [("shape/ExpressionSize.original.lean", PREFIX / "ExpressionSize.lean")],
        [("shape/ExpressionSize.lean", PREFIX / "ExpressionSize.lean")],
    ),
    (
        "growth",
        "growth/full-exponent-growth.patch",
        [("growth/CurrentPackingRank2011.baseline.lean", PREFIX / "CurrentPackingRank2011.lean")],
        [("growth/CurrentPackingRank2011.lean", PREFIX / "CurrentPackingRank2011.lean")],
    ),
    (
        "windows_after_packet_y",
        "windows/ordered-windows.patch",
        [("windows/prior_baseline/" + str(PREFIX / "ObjectPairingInjective.lean"),
          PREFIX / "ObjectPairingInjective.lean")],
        [("windows/lean/DiophantineConsistency/ObjectPairingInjective.lean",
          PREFIX / "ObjectPairingInjective.lean"),
         ("windows/lean/DiophantineConsistency/OrderedWindow.lean",
          PREFIX / "OrderedWindow.lean")],
    ),
]


def main():
    results = []
    for name, patch, inputs, outputs in CASES:
        with tempfile.TemporaryDirectory(prefix="proveit-patch-") as directory:
            root = Path(directory)
            for source, target in inputs:
                dest = root / target
                dest.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(PACKET / source, dest)
            patch_path = str(PACKET / patch)
            subprocess.run(["git", "apply", "--check", patch_path], cwd=root, check=True)
            subprocess.run(["git", "apply", patch_path], cwd=root, check=True)
            for expected, target in outputs:
                if (root / target).read_bytes() != (PACKET / expected).read_bytes():
                    raise SystemExit(f"Candidate mismatch: {name}: {target}")
            results.append({"proposal": name, "applicable": True,
                            "output_matches_candidate": True})
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
