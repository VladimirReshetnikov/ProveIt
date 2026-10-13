"""Deterministic families and exact PD replacement used by the experiments."""
from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from fastunknot.diagram import Diagram, DiagramError
from fastunknot.rational import build_montesinos_tangle


def fraction_cf(p, q):
    if q == 0:
        raise ValueError("finite fraction required")
    result = []
    while q:
        a, remainder = divmod(p, q)
        result.append(a)
        p, q = q, remainder
    return result


def word_column(word, column):
    p, q = column
    for letter in reversed(word):
        if letter == "A":
            p += 2 * q
        elif letter == "B":
            q += 2 * p
        else:
            raise ValueError("word must use A and B")
    return p, q


def rational_pair(row_word, column_word=None):
    if column_word is None:
        column_word = row_word
    p, q = word_column(row_word, (1, 1))
    r, s = word_column(column_word, (3, 2))
    return {"montesinos": {"e": 0,
            "tangles": [fraction_cf(p, q), [-a for a in fraction_cf(r, s)]]}}


def alexander_one_pretzel(a):
    if type(a) is not int or a < 3 or a % 2 != 1:
        raise ValueError("a must be an odd integer at least three")
    r = (a * a + 2 * a - 1) // 2
    return {"montesinos": {"e": 0, "tangles": [[0, -a], [0, a + 2], [0, r]]}}


def insert_pattern(diagram, pattern, crossing=0):
    """Replace a crossing disk by the actual template, returning a checked map.

    The four boundary terminals are clockwise and a PD crossing is CCW.
    Try the four cyclic alignments; retain the first valid knot closure.
    No arithmetic classification is used to decide whether the generated
    rotation system or component count is valid.
    """
    old = diagram.pd[crossing]
    if len(set(old)) != 4:
        raise ValueError("replacement requires four distinct incident edges")
    template = build_montesinos_tangle(pattern["e"], pattern["tangles"])
    if len(set(template["boundary"])) != 4:
        raise ValueError("template has repeated boundary edges")
    internal = sorted({x for row in template["pd"] for x in row}
                      - set(template["boundary"]))
    fresh = max(x for row in diagram.pd for x in row) + 1
    other_rows = list(diagram.pd[:crossing] + diagram.pd[crossing + 1:])
    for offset in range(4):
        label_map = dict(zip(internal, range(fresh, fresh + len(internal))))
        label_map.update({label: old[(offset - port) % 4]
                          for port, label in enumerate(template["boundary"])})
        rows = other_rows + [tuple(label_map[x] for x in row) for row in template["pd"]]
        try:
            result = Diagram.from_pd(rows)
        except DiagramError:
            continue
        k = len(template["pd"])
        certificate = {"version": 1, "pattern": pattern,
                       "crossings": list(range(len(other_rows), len(other_rows) + k)),
                       "rotations": [0] * k}
        return result, certificate
    raise ValueError("no cyclic alignment produces a validated knot")


def conway_diagram():
    return Diagram.from_json(json.loads((ROOT / "examples/conway.json").read_text()))
