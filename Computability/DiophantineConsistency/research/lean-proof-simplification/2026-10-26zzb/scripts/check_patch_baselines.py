#!/usr/bin/env python3
"""Check both supplied patches without touching a user's repository."""
from pathlib import Path
import tempfile, subprocess, hashlib, json
bundle = Path(__file__).resolve().parents[1]
checks = [
    ("CurrentKernelResidues2011.lean", "current-kernel-horner.patch", "f16f792f4449e423bfa6165f81a6b6e3d8c872531b4e428aaf0bebafd178a659"),
    ("EnumeratorSemantics.lean", "tag-only-option.patch", "4d9cc3b56f5a5d7a07bc443fbe0eee2a2201f2e8cd5ddbb0cfd3f7ce1b30b11d"),
]
results = []
for name, patch, expected in checks:
    baseline = (bundle / "baselines" / name).read_bytes()
    assert hashlib.sha256(baseline).hexdigest() == expected, name
    with tempfile.TemporaryDirectory(prefix="proveit-patch-check-") as temporary:
        root = Path(temporary)
        target = root / "Computability/DiophantineConsistency/Lean/DiophantineConsistency" / name
        target.parent.mkdir(parents=True)
        target.write_bytes(baseline)
        patch_path = bundle / "patches" / patch
        subprocess.run(["git", "apply", "--check", str(patch_path)], cwd=root, check=True)
        subprocess.run(["git", "apply", str(patch_path)], cwd=root, check=True)
        actual = target.read_bytes()
        proposed = (bundle / "proposed/DiophantineConsistency" / name).read_bytes()
        assert actual == proposed, name
        results.append({"patch": patch, "baseline_sha256": expected,
                        "proposed_sha256": hashlib.sha256(actual).hexdigest(),
                        "patch_applies": True, "matches_supplied_proposed_file": True})
print(json.dumps(results, indent=2))
