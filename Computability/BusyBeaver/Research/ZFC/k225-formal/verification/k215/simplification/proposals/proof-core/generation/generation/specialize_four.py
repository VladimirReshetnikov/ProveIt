#!/usr/bin/env python3
"""Replay the four-shape specialization of the checked generic proof.

This is an untrusted source transformation, not a proof checker.
Lean checks the emitted proof terms. The generic input is unchanged.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parent
INPUT_SHA256 = "19b91abe054e718e392c38e0638639f445643f7b11907975c9c6cb488f3f762b"
OUTPUT_SHA256 = "4a7b0746a03f8d169b14beb078c4cbb0cf7c76edd37e7b383b28ccabcae58efe"

def sha(text):
    return hashlib.sha256(text.encode()).hexdigest()

def once(text, old, new):
    assert text.count(old) == 1, (old, text.count(old))
    return text.replace(old, new)

def build():
    generic = (ROOT / "DominatedImplication.lean").read_text()
    assert sha(generic) == INPUT_SHA256
    text = (ROOT / "templates/four-prefix.txt").read_text()
    text += generic[generic.index("private structure WithSeed"):]
    text = once(text, 'local infix:50 " ≼ " => L.below',
                'local infix:50 " ≼ " => Allowed L')
    text = once(text, """
private theorem le_l {u x : A} (y : A) (h : u ≼ x) : u ≼ wim x y :=
  L.grow_left y h
private theorem le_r {u y : A} (x : A) (h : u ≼ y) : u ≼ wim x y :=
  L.grow_right x h
""", "")
    replacements = [
        ("(le_l v4 (le_l v3 (le_r v2 (L.refl _))))",
         "(Allowed.llr v2 v1 v3 v4)"),
        ("(le_l (wim (wim v0 v1) v1) (le_l v1 (L.refl _)))",
         "(Allowed.ll v0 v1 (wim (wim v0 v1) v1))"),
        ("(le_l v1 (le_l v1 (L.refl _)))",
         "(Allowed.ll v0 v1 v1)"),
        ("(le_l (wim v3 v2) (le_l v2 (L.refl _)))",
         "(Allowed.ll v0 v2 (wim v3 v2))"),
        ("(le_r v2 (L.refl _))", "(Allowed.right v2 v1)"),
    ]
    for old, new in replacements:
        text = once(text, old, new)
    assert text.count("L.refl") == 4
    text = text.replace("L.refl", "Allowed.same")
    text = once(text,
                "end SetTheory.BusyBeaver.ZFC.DominatedImplication\n",
                (ROOT / "templates/four-suffix.txt").read_text())
    assert not re.search(r"\ble_[lr]\b|L\.(?:below|refl|grow_left|grow_right)", text)
    assert sha(text) == OUTPUT_SHA256
    return text

def inventory(text):
    guards = []
    current = None
    for line in text.splitlines():
        theorem = re.match(r"(?:private )?theorem (\w+)", line)
        if theorem:
            current = theorem.group(1)
        for ctor in re.findall(r"Allowed\.(same|right|ll|llr)\b", line):
            guards.append({"theorem": current, "shape": ctor,
                           "path": {"same": "", "right": "R",
                                    "ll": "LL", "llr": "LLR"}[ctor]})
    assert len(guards) == 9
    assert {g["path"] for g in guards} == {"", "R", "LL", "LLR"}
    return guards

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()
    text = build()
    if args.check or args.out is None:
        assert text == (ROOT / "FourShapeImplication.lean").read_text()
    if args.out:
        dest = args.out / "BusyBeaver/ZFC/FourShapeImplication.lean"
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_text(text)
    report = {"status": "PASS", "generic_sha256": INPUT_SHA256,
              "four_shape_sha256": OUTPUT_SHA256,
              "bytes": len(text.encode()), "lines": len(text.splitlines()),
              "helper_count": len(re.findall(r"private theorem (?:b|cd)\d+\b", text)),
              "guard_occurrences": inventory(text),
              "claims": ["four finite shapes suffice", "no minimality claim",
                         "generic core unchanged", "untrusted generator; kernel checked output"]}
    print(json.dumps(report, indent=2))

if __name__ == "__main__":
    main()
