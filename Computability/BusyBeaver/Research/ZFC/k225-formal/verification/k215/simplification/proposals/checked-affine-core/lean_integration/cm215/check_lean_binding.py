#!/usr/bin/env python3
"""Bind the literal Lean tables to the pinned dense .tm bytes.

This is an independent artifact-identity check, not a replacement for Lean's
kernel check of the table certificates and all-tape simulation theorem.
"""
import json
import re
from hashlib import sha256
from pathlib import Path

HERE = Path(__file__).resolve().parent


def rows(path):
    result = []
    for line in path.read_text().splitlines():
        if not line or line.startswith("#"):
            continue
        q, b, w, d, n = line.split()
        assert int(q)*2 + int(b) == len(result)
        result.append((bool(int(w)), d == "R", int(n)))
    return result


def main():
    text = (HERE / "CM215Tables.lean").read_text()
    result = {}
    for name, filename in (("oldRows", "baseline215.tm"), ("newRows", "marker215.tm")):
        body = re.search(rf"def {name} : List Action := \[\n(.*?)\n\]", text, re.S)
        assert body, f"Missing literal table {name}"
        lean = [(w == "true", r == "true", int(n)) for w,r,n in
                re.findall(r"⟨(true|false), (true|false), ([0-9]+)⟩", body[1])]
        literal = rows(HERE / filename)
        assert len(lean) == 430 and lean == literal
        assert all(0 <= n < 216 for _, _, n in lean)
        result[name] = {
            "literal_file": filename,
            "literal_sha256": sha256((HERE / filename).read_bytes()).hexdigest(),
            "matched_rows": len(lean),
        }
    result["status"] = "EXACT_LEAN_LITERAL_TABLE_BINDING_PASS"
    result["source_sha256"] = sha256((HERE / "CM215Tables.lean").read_bytes()).hexdigest()
    (HERE / "lean_binding.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
