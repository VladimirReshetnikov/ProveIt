#!/usr/bin/env python3
"""Reproducible lexical/import audit of an already obtained grh-lean snapshot.

This does not run Lean, check proof terms, or establish theorem truth.  It screens
source text for explicit admissions and trust-extending constructs after removing
nested comments and quoted strings.  It is deliberately not a full Lean parser.
Usage: python3 static_audit.py /absolute/path/to/grh-lean > static_audit.json
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

TOKENS = re.compile(
    r"(?<![\w.])(sorry|admit|axiom|unsafe|native_decide|run_tac|run_cmd|elab|macro|"
    r"implemented_by|extern|sorryAx|partial|opaque)(?![\w.])"
    r"|#eval|#check|#print|Lean\.ofReduceBool"
)
DECLARATIONS = re.compile(
    r"^\s*(?:(?:noncomputable|private|protected)\s+)*"
    r"(?:def|lemma|theorem|instance|structure|class|inductive|abbrev)\s", re.M
)

def erase_comments_and_strings(text):
    out = []
    i = 0
    depth = 0
    in_string = False
    while i < len(text):
        pair = text[i:i + 2]
        if depth:
            if pair == "/-":
                depth += 1
                out.append("  ")
                i += 2
            elif pair == "-/":
                depth -= 1
                out.append("  ")
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif in_string:
            if text[i] == "\\":
                out.append("  ")
                i += 2
            elif text[i] == '"':
                in_string = False
                out.append(" ")
                i += 1
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif pair == "/-":
            depth = 1
            out.append("  ")
            i += 2
        elif pair == "--":
            j = text.find("\n", i)
            if j == -1:
                j = len(text)
            out.append(" " * (j - i))
            i = j
        elif text[i] == '"':
            in_string = True
            out.append(" ")
            i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)

def scan_edition(root, edition):
    src = root / edition / "src"
    files = sorted(src.rglob("*.lean"))
    modules = {}
    suspicious = []
    decl_count = 0
    line_count = 0
    file_hashes = []
    for path in files:
        raw = path.read_text(encoding="utf-8")
        clean = erase_comments_and_strings(raw)
        relative = path.relative_to(root).as_posix()
        module = ".".join(path.relative_to(src).with_suffix("").parts)
        modules[module] = re.findall(r"^\s*import\s+([^\n]+)", clean, flags=re.M)
        modules[module] = [name for line in modules[module] for name in line.split()]
        line_count += len(raw.splitlines())
        decl_count += len(DECLARATIONS.findall(clean))
        for match in TOKENS.finditer(clean):
            suspicious.append({"file": relative,
                               "line": clean.count("\n", 0, match.start()) + 1,
                               "token": match.group(0)})
        file_hashes.append({"file": relative,
                            "sha256": hashlib.sha256(path.read_bytes()).hexdigest()})
    reachable = set()
    pending = ["Main"]
    while pending:
        module = pending.pop()
        if module in reachable or module not in modules:
            continue
        reachable.add(module)
        pending.extend(modules[module])
    library_to_new = [{"from": m, "to": target}
                      for m, imports in modules.items() if m.startswith("Lib.")
                      for target in imports if target.startswith("New.")]
    challenge_imports = [{"from": m, "to": target}
                         for m, imports in modules.items()
                         for target in imports if "Challenge" in target]
    return {"edition": edition, "source_files": len(files),
            "physical_source_lines": line_count,
            "approximate_declarations_regex": decl_count,
            "flagged_code_tokens": suspicious,
            "local_modules_reachable_from_Main": len(reachable),
            "local_modules_not_reachable_from_Main": sorted(set(modules) - reachable),
            "Lib_imports_New": library_to_new,
            "src_imports_Challenge": challenge_imports,
            "file_sha256": file_hashes}

def main():
    root = Path(sys.argv[1]).resolve()
    try:
        commit = subprocess.check_output(["git", "-C", str(root), "rev-parse", "HEAD"],
                                         text=True).strip()
    except subprocess.CalledProcessError:
        commit = None
    editions = [scan_edition(root, e) for e in ("grh", "grh-compact")]
    statements_equal = ((root / "grh/src/Statements.lean").read_bytes() ==
                        (root / "grh-compact/src/Statements.lean").read_bytes())
    main_code_equal = (erase_comments_and_strings((root / "grh/src/Main.lean").read_text()).split() ==
                       erase_comments_and_strings((root / "grh-compact/src/Main.lean").read_text()).split())
    print(json.dumps({"audit_kind": "static lexical and import scan; no kernel replay",
                      "commit": commit,
                      "edition_Statements_byte_identical": statements_equal,
                      "edition_Main_code_equal_ignoring_comments_whitespace": main_code_equal,
                      "editions": editions}, indent=2))

if __name__ == "__main__":
    main()
