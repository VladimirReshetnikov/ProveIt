#!/usr/bin/env python3
"""Check the exact source correspondence between retained runs and delivery.

Two Dense file comments were corrected after their original compilation.
The full noncomment text of every delivered proof is identical to the
source used in the retained run. Quoted strings are preserved, and nested
Rocq comments are removed according to their lexical delimiters.
"""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent.parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def erase_comments(source):
    result = []
    i, depth, quoted = 0, 0, False
    while i < len(source):
        if depth:
            if source[i:i + 2] == "(*":
                depth += 1
                i += 2
            elif source[i:i + 2] == "*)":
                depth -= 1
                i += 2
            else:
                i += 1
        elif quoted:
            result.append(source[i])
            if source[i] == '"':
                if source[i:i + 2] == '""':
                    result.append(source[i + 1])
                    i += 2
                    continue
                quoted = False
            i += 1
        elif source[i:i + 2] == "(*":
            depth = 1
            i += 2
        else:
            if source[i] == '"':
                quoted = True
            result.append(source[i])
            i += 1
    assert not depth and not quoted, "Unclosed comment or quoted string."
    return "".join(result)


def main():
    data = json.loads((ROOT / "receipts/source_correspondence.json").read_text())
    count = 0
    for variant, modules in data["variants"].items():
        for name, spec in modules.items():
            delivered = ROOT / "coq" / variant / (name + ".v")
            checked = ROOT / spec["checked_source_copy"] if "checked_source_copy" in spec else delivered
            assert sha(checked) == spec["checked_source_sha256"]
            assert sha(delivered) == spec["portable_source_sha256"]
            actual = erase_comments(delivered.read_text())
            assert actual == erase_comments(checked.read_text()), (variant, name)
            assert hashlib.sha256(actual.encode()).hexdigest() == spec["noncomment_text_sha256"]
            count += 1
    print(f"PASS_EXACT_PROOF_TEXT: {count} modules.")


if __name__ == "__main__":
    main()
