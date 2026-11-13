#!/usr/bin/env python3
"""Check that the Lean literal spells the pinned AQ22 straight-line graph.

This syntactic check does not compile Lean or establish a Diophantine equivalence.
An optional argument selects the literal text, allowing negative mutation tests.
"""
import hashlib
import json
import re
import sys
from pathlib import Path

D = Path(__file__).resolve().parent
candidate = D.parent / 'adaptive-square-sums22-degree10' / 'candidate.json'
raw = candidate.read_bytes()
if hashlib.sha256(raw).hexdigest() != '1266b143c5512351739ea2c71fc8e0b8b0e5cecc599392f128c0803ff78ce106':
    raise SystemExit('candidate hash differs')
c = json.loads(raw)
path = Path(sys.argv[1]) if len(sys.argv) == 2 else D / 'draft-src/AdaptiveAQ22Literal.lean'
if len(sys.argv) > 2:
    raise SystemExit('usage: check_literal.py [literal.lean]')
s = path.read_text()
header = re.search(r'^def literal \(p : Fin 4 → ℤ\) : Expr \(Fin 22\) :=$', s, re.M)
if not header:
    raise SystemExit('literal signature differs')
body = s[header.end():].split('\nend DiophantineConsistency.AdaptiveAQ22Literal', 1)[0]
lines = [line.strip() for line in body.splitlines() if line.strip()]
expected = ([f'let {name} : Expr (Fin 22) := .var {i}' for i, name in enumerate(c['witnesses'])]
            + [f'let {name} : Expr (Fin 22) := .constant (p {i})' for i, name in enumerate(c['fixed_numerals'])]
            + [f'let {name} := {a} {op} {b}' for name, op, a, b in c['source']]
            + [c['output']])
if lines != expected:
    for i in range(max(len(lines), len(expected))):
        got = lines[i] if i < len(lines) else '<missing>'
        want = expected[i] if i < len(expected) else '<none>'
        if got != want:
            raise SystemExit(f'literal differs at body line {i + 1}: got {got!r}, expected {want!r}')
if len(c['witnesses']) != 22 or len(c['fixed_numerals']) != 4 or len(c['source']) != 114:
    raise SystemExit('unexpected graph dimensions')
print('OK: 22 variables, 4 ports, and all 114 gates match the pinned graph')
