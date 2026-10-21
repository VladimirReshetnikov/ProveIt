#!/usr/bin/env python3
"""Read-only exact row audit of native K215 against the repository's Lean table.

No Lean source is executed or modified. This checks literal data after the
documented label translation; it does not prove a tape/run-semantics adapter.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re

PIN = "b6c7087477e51c017003bd729e712c8969733223"
NATIVE_SHA256 = "9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2"
REFERENCE_SHA256 = "429775b1774d41e94ba3b7283f7f50ea45bc13716d4ef27fccffe1f686a8d24c"
RENAME = {301: 102, 302: 120, 254: 230}

def require(ok, message):
    if not ok:
        raise ValueError(message)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def native(path):
    require(sha(path) == NATIVE_SHA256, "wrong native K215 bytes")
    result = {}
    start = None
    for line in path.read_text().splitlines():
        if line.startswith("#! start "):
            require(start is None, "duplicate start")
            start = int(line[9:])
        elif line and not line.startswith("#"):
            q, b, w, d, z = line.split()
            q, b, w, z = map(int, (q, b, w, z))
            require(b in (0, 1) and w in (0, 1) and d in ("L", "R"),
                    "bad binary row")
            require((q, b) not in result, "duplicate native row")
            result[q, b] = (bool(w), d == "R", z)
    return start, result

def reference(path):
    require(sha(path) == REFERENCE_SHA256, "wrong pinned repository reference bytes")
    text = path.read_text()
    prefix = "def table215 : List (Row × Row) := ["
    require(text.count(prefix) == 1, "unexpected table declaration")
    block, after = text.split(prefix, 1)[1].split("]\n", 1)
    require("def tm215 : KZip.TMN := tmOf table215" in after,
            "unexpected repository machine wrapper")
    atom = r"(?:none|some \((?:true|false), (?:true|false), [0-9]+\))"
    pattern = re.compile(r"\((" + atom + r"), (" + atom + r")\),?")
    rows = {}
    absent = []
    lines = [line.strip() for line in block.splitlines() if line.strip()]
    for q, line in enumerate(lines):
        matched = pattern.fullmatch(line)
        require(matched is not None, f"unparsed reference row {q}: {line}")
        actions = []
        for b, value in enumerate(matched.groups()):
            if value == "none":
                actions.append(None)
            else:
                write, right, target = value[6:-1].split(", ")
                action = (write == "true", right == "true", int(target))
                actions.append(action)
                rows[q, b] = action
        require((actions[0] is None) == (actions[1] is None),
                f"partially defined state {q}")
        if actions[0] is None:
            absent.append(q)
    return rows, len(lines), absent

def check(native_path, reference_path):
    start, old = native(native_path)
    lean, length, holes = reference(reference_path)
    rename = lambda q: RENAME.get(q, q)
    old_states = {q for q, _ in old}
    require(start == 0 and len(old_states) == 215 and len(old) == 430,
            "incorrect native census")
    require({z for _, _, z in old.values()} - old_states == {254},
            "native terminal differs")
    require(102 not in old_states and 120 not in old_states,
            "renaming targets are not freed native labels")
    image = {rename(q) for q in old_states | {254}}
    require(len(image) == 216, "noninjective relevant state translation")
    translated = {(rename(q), b): (w, d, rename(z))
                  for (q, b), (w, d, z) in old.items()}
    require(translated == lean, "literal renamed rows disagree")
    require(length == 226 and len(holes) == 11,
            "unexpected repository table bounds or holes")
    lean_states = {q for q, _ in lean}
    require({z for _, _, z in lean.values()} - lean_states == {230},
            "repository terminal differs")
    require(rename(start) == 0 and rename(84) == 84,
            "start or dispatcher changed")
    return {
        "status": "PASS_EXACT_LITERAL_LABEL_TRANSLATION",
        "repository_pin": PIN,
        "native_sha256": sha(native_path),
        "reference_sha256": sha(reference_path),
        "reference_repository_path": "Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KTable215.lean",
        "native_working_states": 215,
        "rows_checked": 430,
        "nonidentity_labels": RENAME,
        "initial_control": {"native": 0, "repository": 0},
        "dispatcher": {"native": 84, "repository": 84},
        "halt": {"native": 254, "repository": 230},
        "reference_table_entries": length,
        "reference_explicit_disabled_labels": holes,
        "reference_implicit_unused_labels_below_halt": list(range(length, 230)),
        "reference_disabled_labels_below_halt": sorted(set(range(230)) - lean_states),
        "direction_encoding": {"true": "R", "false": "L"},
        "scope": "Literal row and label correspondence only; "
                 "the function-tape/list-zipper run and halting adapter remains to be proved.",
    }

def main():
    p = argparse.ArgumentParser(description=__doc__)
    here = Path(__file__).resolve().parent
    p.add_argument("--native", type=Path, default=here / "inputs" / "k215.native.tm")
    p.add_argument("--reference", type=Path, default=here / "reference" / "KTable215.lean")
    p.add_argument("--out", type=Path)
    args = p.parse_args()
    result = json.dumps(check(args.native, args.reference), indent=2, sort_keys=True) + "\n"
    if args.out:
        args.out.write_text(result)
    print(result, end="")

if __name__ == "__main__":
    main()
