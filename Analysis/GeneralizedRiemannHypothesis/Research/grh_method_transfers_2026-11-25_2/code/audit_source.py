#!/usr/bin/env python3
"""Source inventory; this is NOT a Lean compiler or kernel audit.

Run python3 code/audit_source.py /path/to/grh-lean to check the pinned clone.
"""
import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path

PIN = "72fead102f663d5c7a407964a13dc0cf9d977207"


def without_comments(text):
    # Preserve line numbers, nested Lean block comments, and quoted strings.
    out, i, depth, string = [], 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                out.extend("  ")
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif string:
            c = text[i]
            out.append("\n" if c == "\n" else " ")
            i += 1
            if c == "\\" and i < len(text):
                out.append(" ")
                i += 1
            elif c == '"':
                string = False
        elif text.startswith("/-", i):
            depth = 1
            out.extend("  ")
            i += 2
        elif text.startswith("--", i):
            j = text.find("\n", i)
            if j == -1:
                j = len(text)
            out.extend(" " * (j-i))
            i = j
        elif text[i] == '"':
            string = True
            out.append(" ")
            i += 1
        else:
            out.append(text[i])
            i += 1
    assert depth == 0
    return "".join(out)


def run(repo):
    sha = subprocess.check_output(["git", "-C", str(repo), "rev-parse", "HEAD"],
                                  text=True).strip()
    assert sha == PIN, (sha, PIN)
    answer = {"commit": sha, "scope": "Static text inventory only; no kernel replay.",
              "editions": {}, "files": []}
    for edition in ("grh", "grh-compact"):
        files = sorted((repo/edition/"src").rglob("*.lean"))
        tokens = []
        missing = []
        for path in files:
            data = path.read_bytes()
            text = data.decode()
            clean = without_comments(text)
            for m in re.finditer(r"\b(sorry|admit|axiom|unsafe|native_decide)\b", clean):
                tokens.append({"file": str(path.relative_to(repo)), "token": m.group(),
                               "line": clean[:m.start()].count("\n")+1})
            for line in clean.splitlines():
                if line.strip().startswith("import "):
                    for module in line.strip().split()[1:]:
                        if module.startswith(("Lib.", "New.")) or module == "Statements":
                            target = repo/edition/"src"/Path(*module.split("."))
                            if not target.with_suffix(".lean").exists():
                                missing.append({"file": str(path.relative_to(repo)),
                                                "import": module})
            answer["files"].append({"path": str(path.relative_to(repo)),
                                    "bytes": len(data),
                                    "sha256": hashlib.sha256(data).hexdigest()})
        answer["editions"][edition] = {"src_lean_files": len(files),
                                       "flagged_tokens_outside_comments": tokens,
                                       "missing_local_imports": missing}
        assert not tokens, tokens
        assert not missing, missing
    a = (repo/"grh"/"src"/"Statements.lean").read_bytes()
    b = (repo/"grh-compact"/"src"/"Statements.lean").read_bytes()
    answer["statement_files_identical"] = a == b
    assert a == b
    return answer


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("repository", type=Path)
    ap.add_argument("--output", type=Path)
    args = ap.parse_args()
    result = run(args.repository)
    target = args.output or Path(__file__).resolve().parents[1]/"evidence"/"source_inventory.json"
    target.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({k:v for k,v in result.items() if k != "files"}, indent=2))
