#!/usr/bin/env python3
"""Rebuild all new equation stages in an isolated directory and compare bytes."""
from pathlib import Path
import argparse
import importlib.util
import json
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent

def require(condition, message):
    if not condition:
        raise ValueError(message)

def read(path):
    return json.loads(path.read_bytes())

def write(path, value, pretty=False):
    path.parent.mkdir(parents=True, exist_ok=True)
    options = {"indent": 2} if pretty else {"separators": (",", ":")}
    path.write_bytes((json.dumps(value, sort_keys=True, **options) + "\n").encode())

def rebuild(destination):
    composition = destination / "composition"
    shutil.copytree(ROOT / "composition", composition,
                    ignore=shutil.ignore_patterns("composed", "__pycache__", "*.pyc"))
    result = subprocess.run([sys.executable, "-B", str(composition / "build_composition.py")],
                            cwd=destination, text=True, capture_output=True)
    require(result.returncode == 0, result.stdout + result.stderr)
    checked = []
    for stage in ["strict238", "basis235", "pooled223", "differences223"]:
        for expected in sorted((ROOT / "composition/composed" / stage).glob("*.json")):
            actual = composition / "composed" / stage / expected.name
            require(actual.read_bytes() == expected.read_bytes(),
                    "rebuild mismatch: " + stage + "/" + expected.name)
            checked.append("composition/composed/" + stage + "/" + expected.name)
    spec = importlib.util.spec_from_file_location("certificate_replay", ROOT / "algebra/audit_algebra.py")
    algebra = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(algebra)
    source = composition / "composed/differences223/equation.json"
    parent = read(source)
    projected = algebra.verify_radicals(parent, read(ROOT / "algebra/radical_certificate.json"))
    balanced = algebra.row_transform(projected, read(ROOT / "algebra/row_certificate218.json"))
    centered = algebra.coordinate_transform(projected, read(ROOT / "algebra/centering_certificate.json"))
    first = algebra.affine_transform(centered, read(ROOT / "algebra/affine_certificate217.json"))
    second = algebra.affine_transform(first, read(ROOT / "algebra/affine_certificate216.json"))
    fewest = algebra.row_transform(second, read(ROOT / "algebra/row_certificate216.json"))
    objects = {"parent223.json": parent, "projected218.json": projected,
               "equation218.json": balanced, "centered218.json": centered,
               "affine217.json": first, "affine216.json": second, "equation216.json": fewest}
    for n, equation in [(218, balanced), (216, fewest)]:
        expansion = algebra.square_sum(equation)
        metadata = read(ROOT / "algebra" / f"expanded{n}.json")
        metadata["terms"] = algebra.terms(expansion)
        objects[f"expanded{n}.json"] = metadata
        objects[f"metrics{n}.json"] = algebra.metrics(equation, expansion)
    for filename, value in objects.items():
        path = destination / "algebra" / filename
        write(path, value, filename in {"affine217.json", "affine216.json"})
        require(path.read_bytes() == (ROOT / "algebra" / filename).read_bytes(),
                "algebra replay mismatch: " + filename)
        checked.append("algebra/" + filename)
    return {"status": "passed", "composition_files_rebuilt": 16,
            "algebra_files_replayed": len(objects), "byte_exact_files": checked,
            "scope": "New composition rebuilt from pinned source242; algebra reconstructed "
                     "from frozen projection and row certificates. No discovery search or formal-kernel rebuild."}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="New directory to retain rebuilt artifacts")
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()
    if args.output:
        args.output.mkdir(parents=True, exist_ok=False)
        result = rebuild(args.output.resolve())
    else:
        with tempfile.TemporaryDirectory(prefix="conzfc-rebuild-") as tmp:
            result = rebuild(Path(tmp))
    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.receipt:
        args.receipt.write_text(text)
    print(text, end="")

if __name__ == "__main__":
    main()
