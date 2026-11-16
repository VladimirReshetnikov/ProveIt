"""Check the published machine, Palomar source boundaries, and optional axiom audit."""

import hashlib
import json
import os
from pathlib import Path
import re
import sys

MACHINE_SHA256 = "0610d978675320f0b4b1ef34619dcd3daa5912632d7037e200dfcc70954fea51"
AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def require(condition, message):
    if not condition:
        raise SystemExit(message)


def check_table():
    table = Path("data/pa209.tm").read_bytes()
    require(hashlib.sha256(table).hexdigest() == MACHINE_SHA256, "Machine bytes changed.")
    rows = [
        (int(q), int(b), int(w), int(next_state), direction == "R")
        for q, b, w, direction, next_state in (line.split() for line in table.decode().splitlines())
    ]
    controls = set(range(214)) - {50, 122, 150, 157, 205}
    require(
        len(controls) == 209 and len(rows) == 418
        and {(q, b) for q, b, *_ in rows} == {(q, b) for q in controls for b in range(2)}
        and all(row[3] in controls | {215} for row in rows),
        "Expected a closed 209-state table with two rows per working state.",
    )
    pattern = r"\((\d+),([01]),([01]),(\d+),(true|false)\)"
    for path in (Path("Challenge.lean"), Path("M6Data.lean")):
        source = path.read_text()
        start = source.index("def m6Rows : List RowSpec := [")
        literal = source[start : source.index("]", start)]
        encoded = [
            (int(q), int(b), int(w), int(t), direction == "true")
            for q, b, w, t, direction in re.findall(pattern, literal)
        ]
        require(encoded == rows, f"{path} does not encode the published table.")
    literal = Path("M6/Literal.lean").read_text()
    bool_to_int = {"false": 0, "true": 1}
    machine = [
        (int(q), bool_to_int[b], bool_to_int[w], int(t), direction == "true")
        for q, b, w, direction, t in re.findall(
            r"\| (\d+), (false|true) => some \((false|true), (false|true), (\d+)\)", literal
        )
    ]
    require(machine == rows, "M6/Literal.lean differs from the published table.")


def check_sources():
    for directory, directories, files in os.walk("."):
        directories[:] = [name for name in directories if name not in {".git", ".lake"}]
        for name in files:
            if not name.endswith(".lean"):
                continue
            path = Path(directory) / name
            require(not path.is_symlink(), f"Lean source symlink: {path}")
            lines = path.read_text().splitlines()
            require(len(lines) <= 10_000, f"Lean source exceeds 10,000 lines: {path}")
            if name != "lakefile.lean":
                require(next((line.strip() for line in lines if line.strip()), "") == "module",
                        f"Missing module header: {path}")
    challenge = Path("Challenge.lean").read_bytes()
    require(len(challenge) <= 100 * 1024 and len(challenge.splitlines()) <= 1_000,
            "Challenge exceeds Palomar's source limits.")
    require(set(re.findall(rb"^(?:(?:public |meta )*)import (?:all )?(.+)$", challenge, re.M)) ==
            {b"Std", b"Mathlib.Data.Finset.Image", b"Mathlib.Data.Finset.Max"},
            "Unexpected Challenge imports.")
    require(not re.search(r"\bimport (?:all )?Challenge\b", Path("Solution.lean").read_text()),
            "Solution imports Challenge.")


def check_audit(path):
    output = path.read_text()
    expected = re.findall(r"^#print axioms (\S+)", Path("Audit.lean").read_text(), re.M)
    config = json.loads(Path("comparator.json").read_text())
    require(set(config["theorem_names"]).issubset(expected), "Audit omits a compared theorem.")
    for name in expected:
        result = re.search(
            rf"'{re.escape(name)}' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",
            output,
        )
        require(result is not None, f"Missing axiom report for {name}.")
        reported = {axiom.strip() for axiom in result[1].split(",")} if result[1] else set()
        require(reported <= AXIOMS, f"{name} has unexpected axioms: {reported - AXIOMS}.")
    print(f"PASS: {len(expected)} audited declarations.")


if len(sys.argv) == 2:
    check_audit(Path(sys.argv[1]))
else:
    check_table()
    check_sources()
    print("PASS: PA209's 418 transition rows and Palomar source checks.")
