"""Offline whole-source measurements and deterministic certificate replay.

This script is outside the trusted boundary of every delivered checker.
Run from any directory. Generated replays go to a temporary directory.
"""
import hashlib
import importlib.util
import json
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def main():
    manifest = ROOT / "MANIFEST.sha256.json"
    if manifest.exists():
        for name, expected in json.loads(manifest.read_text()).items():
            actual = hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
            if actual != expected:
                raise ValueError("Payload hash mismatch: " + name)

    spec = importlib.util.spec_from_file_location("source_measure", ROOT / "reference/source_measure.py")
    measure = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(measure)
    names = [
        "reference/published_tokens.py", "reference/published_structure.py",
        "reference/published_bytes.py", "code/compact.py",
        "code/explicit_failure.py", "reference/matched_legacy_tokens.py",
        "reference/matched_legacy_structure.py", "code/readable.py",
    ]
    measurements = {name: measure.metrics(ROOT / name) for name in names}
    expected = {
        "reference/published_tokens.py": (292, 336, 865),
        "reference/published_structure.py": (296, 330, 882),
        "reference/published_bytes.py": (298, 349, 762),
        "code/compact.py": (287, 328, 749),
        "code/explicit_failure.py": (289, 330, 739),
        "reference/matched_legacy_tokens.py": (289, 329, 876),
        "reference/matched_legacy_structure.py": (293, 323, 893),
    }
    for name, profile in expected.items():
        actual = tuple(measurements[name][field] for field in
                       ("normalized_tokens", "ast_nodes", "normalized_bytes"))
        if actual != profile:
            raise ValueError(("Measurement changed (Python version may differ)", name, actual, profile))

    with tempfile.TemporaryDirectory(prefix="ipra-endpoints-") as directory:
        temp = Path(directory)
        replay = temp / "replay.json"
        focused = temp / "focused.json"
        commands = [
            [sys.executable, str(ROOT / "tests/replay.py"),
             "--baseline", str(ROOT / "reference/published_bytes.py"),
             "--candidate", "compact", str(ROOT / "code/compact.py"),
             "--candidate", "explicit_failure", str(ROOT / "code/explicit_failure.py"),
             "--legacy-control", "matched_tokens", str(ROOT / "reference/matched_legacy_tokens.py"),
             "--legacy-control", "matched_structure", str(ROOT / "reference/matched_legacy_structure.py"),
             "--mutation-rounds", "4", "--cases", str(ROOT / "tests/inherited_cases.json"),
             "--output", str(replay)],
            [sys.executable, str(ROOT / "tests/focused.py"),
             "--candidate", str(ROOT / "code/compact.py"),
             "--candidate", str(ROOT / "code/explicit_failure.py"),
             "--output", str(focused)],
        ]
        for command in commands:
            subprocess.run(command, check=True, cwd=temp, capture_output=True, text=True)
        result = {
            "status": "PASS", "python": sys.version,
            "measurements": measurements,
            "replay": json.loads(replay.read_text()),
            "focused": json.loads(focused.read_text()),
            "limits": "Finite executable evidence; not a proof-assistant verification or an absolute minimum.",
        }
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
