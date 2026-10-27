#!/usr/bin/env python3
"""Record hashes from the two pinned local checkouts; never downloads files."""
import argparse
import csv
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
PROVEIT_PIN = "a7ae5ab55f9627f5af7bf77443b3c34ef8ef1be4"
PROVEIT_FOLLOWUP = "7de9d09fecd17de776d712835ecb2011205c531d"
ANTHROPIC_PIN = "1a6eee293b9e00cb432eef6018a21f523623a9af"

def git(repo, *args):
    return subprocess.check_output(["git", "-C", str(repo), *args])

def snapshot(repo, name, pin, prefixes):
    head = git(repo, "rev-parse", "HEAD").decode().strip()
    if head != pin:
        raise RuntimeError(f"Unexpected checkout for {name}: {head}")
    records = []
    tracked = git(repo, "ls-files", "--stage", "-z", "--", *prefixes)
    for entry in tracked.decode().split("\0"):
        if not entry:
            continue
        meta, relative = entry.split("\t", 1)
        _, blob, stage = meta.split()
        if stage != "0":
            raise RuntimeError(f"Unmerged source: {relative}")
        path = repo / relative
        if not path.is_file():
            raise RuntimeError(f"Source not materialized: {path}")
        data = path.read_bytes()
        if git(repo, "hash-object", "--", relative).decode().strip() != blob:
            raise RuntimeError(f"Modified tracked source: {relative}")
        records.append({"path": relative, "git_blob": blob, "size_bytes": len(data),
                        "sha256": hashlib.sha256(data).hexdigest(),
                        "url": f"https://github.com/{name}/blob/{pin}/{relative}"})
    return {"repository": name, "commit": pin, "files": records,
            "hash_coverage_is_not_line_by_line_review": True}

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--proveit", type=Path, required=True)
    parser.add_argument("--anthropic", type=Path, required=True)
    args = parser.parse_args()
    out = ROOT / "provenance"
    out.mkdir(exist_ok=True)
    p = snapshot(args.proveit.resolve(), "VladimirReshetnikov/ProveIt", PROVEIT_PIN,
                 ["Computability/SubexponentialSAT", "docs/incoming", "lib/openai-math/preprints"])
    a = snapshot(args.anthropic.resolve(), "anthropics/formal-math", ANTHROPIC_PIN, ["eth"])
    diff = git(args.proveit, "diff", PROVEIT_PIN, PROVEIT_FOLLOWUP, "--",
               "Computability/SubexponentialSAT", "docs/incoming")
    (out / "final_documentation_update.patch").write_bytes(diff)
    readme_path = "Computability/SubexponentialSAT/README.md"
    followup_data = git(args.proveit, "show", f"{PROVEIT_FOLLOWUP}:{readme_path}")
    followup = {"commit": PROVEIT_FOLLOWUP, "path": readme_path,
                "change": "Documentation only: links the supplied Anthropic formalization",
                "git_blob": git(args.proveit, "rev-parse", f"{PROVEIT_FOLLOWUP}:{readme_path}").decode().strip(),
                "sha256": hashlib.sha256(followup_data).hexdigest(),
                "size_bytes": len(followup_data),
                "url": f"https://github.com/VladimirReshetnikov/ProveIt/blob/{PROVEIT_FOLLOWUP}/{readme_path}"}
    manifest = {"recorded_at_utc": datetime.now(timezone.utc).isoformat(),
                "inspection_scope": "All 29 packet summaries/status declarations; detailed source interfaces and leading proofs used in the comparison; supplied Anthropic theorem, proof entry, algorithm and source status. No full Lean build.",
                "snapshots": [p, a], "final_documentation_followup": followup}
    (out / "source_manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    commits = git(args.proveit, "log", "-35", "--format=%H%x09%aI%x09%s", PROVEIT_FOLLOWUP,
                  "--", "Computability/SubexponentialSAT", "docs/incoming")
    (out / "reviewed_commits.txt").write_bytes(commits)
    rows = re.findall(r"\\path\{([^}]+)\}&(.+?)\\\\", (ROOT / "sections/review.tex").read_text())
    if len(rows) != 29:
        raise RuntimeError(f"Unexpected packet count: {len(rows)}")
    with (out / "packet_inventory.csv").open("w", newline="") as handle:
        writer = csv.writer(handle)
        writer.writerow(["packet", "summary_latex", "source_url"])
        for packet, summary in rows:
            writer.writerow([packet, summary, f"https://github.com/VladimirReshetnikov/ProveIt/tree/{PROVEIT_PIN}/Computability/SubexponentialSAT/Research/{packet}"])
    print(f"Recorded {len(p['files'])} ProveIt and {len(a['files'])} Anthropic source hashes; 29 packets.")

if __name__ == "__main__":
    main()
