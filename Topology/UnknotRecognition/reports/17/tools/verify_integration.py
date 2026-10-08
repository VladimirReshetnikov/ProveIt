"""Apply the included patch to a disposable reference copy and compare bytes."""
import json
from pathlib import Path
import shutil
import subprocess
import tempfile


def files(root):
    return {p.relative_to(root): p.read_bytes() for p in root.rglob("*")
            if p.is_file() and "__pycache__" not in p.parts and p.suffix != ".pyc"}


def main():
    root = Path(__file__).resolve().parents[1]
    with tempfile.TemporaryDirectory(prefix="proveit-patch-") as directory:
        target = Path(directory)
        shutil.copytree(root / "reference/Topology", target / "Topology")
        subprocess.run(["git", "init", "-q", str(target)], check=True)
        patch = root / "integration/changes.patch"
        subprocess.run(["git", "apply", "--check", str(patch)], cwd=target, check=True)
        subprocess.run(["git", "apply", str(patch)], cwd=target, check=True)
        actual = files(target / "Topology/UnknotRecognition/fast")
        expected = files(root / "fast")
        if actual != expected:
            differences = sorted(str(p) for p in actual.keys() | expected.keys()
                                 if actual.get(p) != expected.get(p))
            raise SystemExit("Patched tree differs: " + ", ".join(differences))
    print(json.dumps({"status": "PASS", "compared_files": len(expected),
                      "scope": "Patch applies to pinned reference; output equals delivered fast tree"},
                     indent=2))


if __name__ == "__main__":
    main()
