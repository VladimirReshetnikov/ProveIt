#!/usr/bin/env python3
"""Check source pins for FullZFC253.v and print its reproducible build commands.

This is a source/provenance audit, not a Coq type checker.  It never labels an
uncompiled wrapper as kernel verified.  Python 3 standard library only.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import shlex

HERE = Path(__file__).resolve().parent
ROOT_PATHS = (
    ("Undecidability", "ZF/stdzf_r3/vendor/undecidability/theories"),
    ("BusyCoq", "ZF/stdzf_r3/vendor/busycoq"),
    ("ZF", "ZF/stdzf/coq"),
    ("RegCon", "ZF/stdzf_r3/regcon"),
    ("ZFC", "ZF/stdzf_r3/zfc"),
    ("M254", "ZF/m254/coq/tm"),
    ("M254P", "ZF/m254/coq/prog"),
    ("M254L", "ZF/m254/coq/logic"),
    ("M254S", "ZF/m254/coq/settheory"),
    ("M253", "ZF/m253/coq/tm"),
    ("M253E", "ZF/m253/coq/e2e"),
)


def strip_comments(text: str) -> str:
    result, depth, pos = [], 0, 0
    while pos < len(text):
        if text.startswith("(*", pos):
            depth += 1
            pos += 2
        elif text.startswith("*)", pos) and depth:
            depth -= 1
            pos += 2
        else:
            if not depth:
                result.append(text[pos])
            pos += 1
    if depth:
        raise ValueError("unclosed Coq comment")
    return "".join(result)


def check(path: Path, expected: str) -> None:
    actual = hashlib.sha256(path.read_bytes()).hexdigest()
    if actual != expected:
        raise ValueError(f"source hash mismatch: {path}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", type=Path, required=True,
                        help="checkout of the pinned public busy-beaver PR20 source")
    parser.add_argument("--command", action="store_true", help="print build commands after audit")
    parser.add_argument("--coqc", default="coqc")
    parser.add_argument("--coqchk", default="coqchk")
    args = parser.parse_args()
    upstream = args.upstream.resolve()
    manifest = json.loads((HERE / "upstream_source_manifest.json").read_text())
    for entry in manifest["upstream_coq_sources"]:
        check(upstream / entry["path"], entry["sha256"])
    for entry in manifest["upstream_artifacts"]:
        check(upstream / entry["path"], entry["sha256"])
    wrapper = HERE / manifest["wrapper"]["path"]
    check(wrapper, manifest["wrapper"]["sha256"])
    source = strip_comments(wrapper.read_text())
    if re.search(r"\b(?:Admitted|admit|Axiom|Parameter)\b|\bUnset\s+(?:Guard|Positivity|Universe)\s+Checking\b", source):
        raise ValueError("wrapper contains a proof escape")
    probes = re.findall(r"\bPrint\s+Assumptions\s+([\w.]+)\s*\.", source)
    if set(probes) != {"zf253_halts_iff_full_ZFC_refutable", "zf253_nonhalts_iff_full_ZFC_consistent"}:
        raise ValueError("expected exactly the two endpoint assumption probes")
    print(f"SOURCE PASS: {len(manifest['upstream_coq_sources'])} pinned upstream Coq sources; "
          f"{len(manifest['upstream_artifacts'])} pinned provenance/build artifacts; wrapper and two probes match")
    print("KERNEL NOT RUN: this script verifies bytes and source conditions only")
    if args.command:
        qflags = [part for prefix, relative in ROOT_PATHS
                  for part in ("-Q", str(upstream / relative), prefix)]
        qflags += ["-Q", str(HERE), "AuditZFC253"]
        commands = [
            ["python3", "-I", "-B", str(upstream / "ZF/m253/check.py"), "--coqc", args.coqc],
            [args.coqc, "-q", *qflags, str(wrapper)],
            [args.coqchk, *qflags, "AuditZFC253.FullZFC253"],
        ]
        print("# Run with matching Coq/coqchk 8.20.1. The first command rebuilds upstream.")
        for command in commands:
            print(shlex.join(command))


if __name__ == "__main__":
    main()
