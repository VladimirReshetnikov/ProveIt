#!/usr/bin/env python3
"""Reproduce the source-window and lexical-interface audit, without edits.

Requires a clean checkout of the pinned ProveIt source tree. Name matches
include comments and are not an elaborated Lean dependency graph.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

DECLARATION = re.compile(
    r"^(?:private\s+)?(?:noncomputable\s+)?(?:def|abbrev|lemma|theorem|structure)\s+(\S+)"
)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkout", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    package = Path(__file__).resolve().parents[1]
    expected = json.loads((package / "audit/source_audit.json").read_text())
    repo = args.checkout.resolve()
    source = repo / expected["source_root"]
    actual = subprocess.check_output(
        ["git", "-C", str(repo), "rev-parse", "HEAD"], text=True).strip()
    if actual != expected["commit"]:
        raise SystemExit(f"Checkout has {actual}; expected {expected['commit']}")
    subprocess.run(["git", "-C", str(repo), "diff", "--quiet", expected["commit"],
                    "--", expected["source_root"]], check=True)
    # Use the tracked file inventory so unrelated untracked files are excluded.
    names = subprocess.check_output(
        ["git", "-C", str(repo), "ls-files", "-z", "--", expected["source_root"]])
    paths = sorted(repo / n.decode() for n in names.split(b"\0")
                   if n and n.endswith(b".lean"))
    texts = {str(p.relative_to(source)): p.read_text(encoding="utf-8") for p in paths}

    def regions(items):
        output = []
        for item in items:
            path = item["path"]
            raw = (source / path).read_bytes()
            lines = raw.decode("utf-8").splitlines()
            spans = []
            for span in item["regions"]:
                a, b = span["start"], span["end"]
                declarations = []
                for n in range(a, b+1):
                    match = DECLARATION.match(lines[n-1])
                    if match:
                        declarations.append({"line": n, "name": match.group(1)})
                spans.append({"start": a, "end": b, "physical_lines": b-a+1,
                              "declarations": declarations})
            output.append({
                "path": path, "physical_lines": len(lines),
                "sha256": hashlib.sha256(raw).hexdigest(),
                "git_blob_sha1": hashlib.sha1(
                    b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest(),
                "regions": spans,
                "total_affected_lines": sum(s["physical_lines"] for s in spans),
            })
        return output

    hits = {}
    for term in expected["lexical_occurrences"]:
        matches = []
        for path, text in texts.items():
            selected = [n for n, line in enumerate(text.splitlines(), 1) if term in line]
            if selected:
                matches.append({"path": path, "lines": selected})
        hits[term] = matches
    result = {
        "commit": actual, "source_root": expected["source_root"],
        "lean_files_examined": len(paths), "audit_kind": expected["audit_kind"],
        "primary": regions(expected["primary"]),
        "contingent_helpers": regions(expected["contingent_helpers"]),
        "lexical_occurrences": hits,
    }
    result["primary_gross_lines"] = sum(x["total_affected_lines"] for x in result["primary"])
    result["contingent_gross_lines"] = sum(x["total_affected_lines"]
                                           for x in result["contingent_helpers"])
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": "PASS" if result == expected else "DIFFERS",
                      "matches_packaged_audit": result == expected,
                      "lean_files_examined": len(paths),
                      "primary_gross_lines": result["primary_gross_lines"],
                      "contingent_gross_lines": result["contingent_gross_lines"]}, indent=2))
    if result != expected:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
