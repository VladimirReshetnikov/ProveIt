#!/usr/bin/env python3
"""Maintainer utility: prepare a candidate SHA256 input manifest under output/.

This is not a mathematical test. Review the candidate, then explicitly copy it
to SHA256SUMS when preparing a release. Runtime outputs are never hashed.
"""
import argparse
import hashlib
from pathlib import Path


def main():
    root=Path(__file__).resolve().parent
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path,default=root/"output"/"SHA256SUMS.candidate")
    args=parser.parse_args()
    target=args.output.resolve()
    if target == root or (root in target.parents and target.relative_to(root).parts[0] != "output"):
        parser.error("An in-package generated manifest must be beneath output/")
    lines=[]
    for path in sorted(root.rglob("*")):
        relative=path.relative_to(root)
        if relative.parts[0] == "output" or "__pycache__" in relative.parts or relative.as_posix() == "SHA256SUMS":
            continue
        if path.is_symlink():
            raise ValueError(f"Refusing symlink input {relative}")
        if path.is_dir():
            continue
        lines.append(hashlib.sha256(path.read_bytes()).hexdigest()+"  "+relative.as_posix())
    target.parent.mkdir(parents=True,exist_ok=True)
    target.write_text("\n".join(lines)+"\n")
    print(f"Candidate manifest: {target} ({len(lines)} inputs)")


if __name__ == "__main__":
    main()
