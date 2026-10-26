#!/usr/bin/env python3
"""Check pinned file identities, six statement headers, metrics and patch applicability.

Read-only: this script does not apply any patch. These are textual checks,
not Lean elaboration or proofs that imported assumptions remain unchanged.
"""
import argparse
import difflib
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
PIN = "89226e3921bce3e8949fadd12d3efb6914c7630c"
REFRESH = "663fb267f6142ca4c0ea5bcd2d4f607f9a4b0eda"
SUBDIR = Path("Computability/DiophantineConsistency/Lean/DiophantineConsistency")
TARGETS = {
    "CurrentSelectorTail2011.lean": ["tail_position_iff", "selectorTail_succ"],
    "CurrentControllerData2011.lean": ["two_order_47", "two_order_2011"],
    "CurrentTileColors2011.lean": ["facts_horizontal_colors", "facts_temporal_colors"],
}
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--repo", required=True, type=Path)
parser.add_argument("--output", type=Path, default=ROOT / "evidence" / "candidate_metrics.json")
args = parser.parse_args()

def header(text, name):
    match = re.search(r"(?m)^(?:private )?theorem " + re.escape(name) + r"\b", text)
    if match is None:
        raise ValueError("Missing theorem " + name)
    end = text.index(":=", match.start())
    return text[match.start():end].rstrip()

rows = []
for filename, names in TARGETS.items():
    rel = SUBDIR / filename
    original = subprocess.check_output(["git", "show", PIN + ":" + rel.as_posix()], cwd=args.repo)
    candidate = (ROOT / "candidates" / filename).read_bytes()
    old, new = original.decode(), candidate.decode()
    assert (args.repo / rel).read_bytes() == original, "Working file changed: " + filename
    headers = {name: header(old, name) == header(new, name) for name in names}
    assert all(headers.values()), "Statement header changed: " + filename
    diff = list(difflib.unified_diff(old.splitlines(), new.splitlines()))
    deleted = sum(line.startswith("-") and not line.startswith("---") for line in diff)
    added = sum(line.startswith("+") and not line.startswith("+++") for line in diff)
    rows.append({
        "path": rel.as_posix(),
        "source_sha256": hashlib.sha256(original).hexdigest(),
        "candidate_sha256": hashlib.sha256(candidate).hexdigest(),
        "physical_lines_before": len(old.splitlines()),
        "physical_lines_after": len(new.splitlines()),
        "deleted_lines": deleted,
        "added_lines": added,
        "net_lines_removed": deleted - added,
        "modified_statement_headers_unchanged": headers,
        "production_integration_compiled": False,
    })
patches = sorted((ROOT / "patches").glob("0*.patch")) + [ROOT / "patches" / "combined.patch"]
for patch in patches:
    subprocess.run(["git", "apply", "--check", str(patch)], cwd=args.repo, check=True)
result = {
    "measurement_pin": PIN,
    "freshness_pin": REFRESH,
    "metric": "Physical lines in complete candidate modules; includes all proposed helper/import costs.",
    "total_lines_before": sum(r["physical_lines_before"] for r in rows),
    "total_lines_after": sum(r["physical_lines_after"] for r in rows),
    "net_lines_removed": sum(r["net_lines_removed"] for r in rows),
    "patch_application_check": "pass",
    "production_integration_compiled": False,
    "files": rows,
}
args.output.parent.mkdir(parents=True, exist_ok=True)
args.output.write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({k: result[k] for k in ["total_lines_before", "total_lines_after", "net_lines_removed", "patch_application_check"]}))
