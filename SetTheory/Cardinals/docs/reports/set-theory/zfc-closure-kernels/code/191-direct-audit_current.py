#!/usr/bin/env python3
"""Reproduce the source-only K215 baseline and shared-core interface audit.

This checks source identities and declaration text, not Lean proof terms.
Usage: python3 audit_current.py /path/to/ProveIt --output audit.json
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tomllib

PIN = "57541fe0cfe3af62b4cb58747d8d1d7c16b338d5"
BRANCH = "49e99c5b7cc6c2e164331961de28bad3904361fd"
ZFC = "Computability/BusyBeaver/Lean/BusyBeaver/ZFC/"
PHASE = "Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/phase12/"
BRANCH_BLOBS = {
    "DominatedImplication": "20f4d47f261bf767c684f2295fa34012ec077b25",
    "Lukasiewicz": "982c0d2c5038f1595205a40e0098b2fa13a01896",
}


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_blob(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def stats(data: bytes) -> dict:
    return {"bytes": len(data), "lines": data.count(b"\n"), "sha256": sha256(data), "git_blob": git_blob(data)}


def uncomment(s: str) -> str:
    """Remove nested Lean block comments and line comments for source auditing."""
    out = []
    i = depth = 0
    while i < len(s):
        if s.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and s.startswith("-/", i):
            depth -= 1
            i += 2
        elif not depth and s.startswith("--", i):
            j = s.find("\n", i)
            i = len(s) if j < 0 else j
        else:
            if not depth or s[i] == "\n":
                out.append(s[i])
            i += 1
    return "".join(out)


def public_headers(s: str) -> dict:
    """Textual signatures only; Lean elaboration is a separate acceptance gate."""
    s = uncomment(s)
    found = {}
    for m in re.finditer(r"^(structure|def|theorem|abbrev|class)\s+(\w+)\b", s, re.M):
        tail = s[m.start():]
        stop = re.search(r":=|\bwhere\b", tail)
        if stop:
            found[m.group(2)] = " ".join(tail[:stop.start()].split())
    return found


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("repo", type=Path)
    ap.add_argument("--branch-dir", type=Path, default=Path(__file__).parent / "branch49")
    ap.add_argument("--output", type=Path, default=Path("audit.json"))
    args = ap.parse_args()
    repo = args.repo.resolve()
    head = subprocess.check_output(["git", "-C", str(repo), "rev-parse", "HEAD"], text=True).strip()
    paths = subprocess.check_output(["git", "-C", str(repo), "ls-tree", "-r", "--name-only", "HEAD"], text=True).splitlines()
    libs = tomllib.loads((repo / "lakefile.toml").read_text()).get("lean_lib", [])
    roots = [x["srcDir"] for x in libs if "srcDir" in x]
    modules = {}
    for p in paths:
        if p.endswith(".lean"):
            for root in roots:
                if p.startswith(root + "/"):
                    modules[p[len(root) + 1:-5].replace("/", ".")] = p
    imports = {}
    selected = set()
    external = set()
    pending = ["BusyBeaver.ZFC.KEndpoint215"]
    while pending:
        m = pending.pop()
        if m in selected or m in external:
            continue
        if m not in modules:
            external.add(m)
            continue
        selected.add(m)
        s = uncomment((repo / modules[m]).read_text())
        deps = []
        for line in re.findall(r"^\s*(?:public\s+)?import\s+([^\n]+)", s, re.M):
            deps.extend(line.split())
        imports[m] = deps
        pending.extend(deps)
    prior = json.loads((repo / PHASE / "integration/current-review.json").read_text())
    source_rows = []
    for m, row in prior["sources"].items():
        rel = row["current"].split("/Proofs/", 1)[1]
        b = (repo / rel).read_bytes()
        source_rows.append({"module": m, "path": rel, "expected_sha256": row["sha256"], "actual_sha256": sha256(b), "matches": sha256(b) == row["sha256"]})
    changes = []
    changed_modules = set()
    for name, expected_blob in BRANCH_BLOBS.items():
        old = (repo / ZFC / (name + ".lean")).read_bytes()
        new = (args.branch_dir / (name + ".lean")).read_bytes()
        oh, nh = public_headers(old.decode()), public_headers(new.decode())
        changes.append({"name": name, "old": stats(old), "new": stats(new), "expected_branch_blob": expected_blob, "branch_blob_matches": git_blob(new) == expected_blob, "public_header_checks": {n: {"present": n in nh, "same_text": nh.get(n) == h, "old": h, "new": nh.get(n)} for n, h in oh.items()}, "new_public_headers": sorted(set(nh) - set(oh))})
        changed_modules.add("BusyBeaver.ZFC." + name)
    direct = sorted(m for m, ds in imports.items() if changed_modules.intersection(ds))
    affected = changed_modules.copy()
    while True:
        nxt = affected | {m for m, ds in imports.items() if affected.intersection(ds)}
        if nxt == affected:
            break
        affected = nxt
    pairs = {which: {unit: sum(x[which][unit] for x in changes) for unit in ("bytes", "lines")} for which in ("old", "new")}
    pairs["reduction"] = {unit: pairs["old"][unit] - pairs["new"][unit] for unit in ("bytes", "lines")}
    s0 = (repo / ZFC / "Lukasiewicz.lean").read_text()
    s1 = (args.branch_dir / "Lukasiewicz.lean").read_text()
    marker = "namespace SetTheory.BusyBeaver.ZFC.Tarski\n"
    data = {
        "scope": "Source identities, import closure and textual public declarations only; no fresh Lean compilation or object/log validation.",
        "head": head, "expected_head": PIN, "head_matches": head == PIN,
        "branch_proposal_commit": BRANCH,
        "phase12_source_identity": {"recorded_sources": len(source_rows), "matching_sources": sum(r["matches"] for r in source_rows), "mismatches": [r for r in source_rows if not r["matches"]]},
        "endpoint": {"project_modules": len(selected), "busybeaver_modules": sum(m.startswith("BusyBeaver.") for m in selected), "selected_source_bytes": sum((repo / modules[m]).stat().st_size for m in selected), "external_imports": sorted(external)},
        "shared_core": {"pair_metrics": pairs, "changes": changes, "tarski_namespace_suffix_byte_identical": s0[s0.index(marker):] == s1[s1.index(marker):], "direct_importing_endpoint_modules": direct, "transitively_affected_endpoint_modules": sorted(affected), "prospective_endpoint_bytes_with_same_closure": sum((repo / modules[m]).stat().st_size for m in selected) - pairs["reduction"]["bytes"]},
        "source_hashes": source_rows,
        "endpoint_modules": [{"module": m, "path": modules[m], "imports": imports[m]} for m in sorted(selected)],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(data, indent=2) + "\n")
    print(json.dumps({k: data[k] for k in ("scope", "head_matches", "phase12_source_identity", "endpoint")}, indent=2))
    print(json.dumps({"shared_pair": pairs, "direct_clients": direct, "affected_module_count": len(affected), "tarski_suffix_identical": data["shared_core"]["tarski_namespace_suffix_byte_identical"]}, indent=2))
    if not data["head_matches"] or any(not r["matches"] for r in source_rows):
        raise SystemExit("Baseline identity audit failed")
    if any(not c["branch_blob_matches"] or any(not h["same_text"] for h in c["public_header_checks"].values()) for c in changes):
        raise SystemExit("Proposed shared-core source/API text audit failed")


if __name__ == "__main__":
    main()
