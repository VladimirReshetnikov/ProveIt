"""A Reidemeister-I/II-reduced unknot family of unbounded Seifert genus.

beta_k = sigma_2^k sigma_1 sigma_2 sigma_1^{-k}, k >= 2.
The braid relation sigma_2 sigma_1 sigma_2 = sigma_1 sigma_2 sigma_1
followed by cancellation changes beta_k into beta_{k-1}.  Hence beta_k
equals sigma_1 sigma_2, whose three-strand closure is an unknot.

The closed-form PD and complete facial decomposition below prove there
are no monogons; every digon is between same-sign crossings.  All other
faces have length at least three.  Thus no R1 or R2 applies for k >= 2.
The signed Seifert graph has three circles and defect one; its surface
genus is k.  The checks below validate the formulas against repository
converters and independently enumerated local moves on a finite range.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

# Prefer the implementation delivered beside this script, regardless of cwd.
FAST_ROOT = Path(__file__).resolve().parents[1] / "fast"
if FAST_ROOT.is_dir():
    sys.path.insert(0, str(FAST_ROOT))

from fastunknot import Diagram
from fastunknot.simplify import legal_moves
try:
    from fastunknot.seifert import seifert_data
except ImportError:
    from seifert import seifert_data


def braid_word(k: int) -> list[int]:
    if type(k) is not int or k < 0:
        raise ValueError("k must be a nonnegative integer")
    return [2] * k + [1, 2] + [-1] * k


def pd_formula(k: int) -> tuple[tuple[int, int, int, int], ...]:
    if type(k) is not int or k < 2:
        raise ValueError("the reduced family uses k >= 2")
    rows = [(2 * k + 3, 4 * k + 3, 0, 1)]
    rows.extend((2 * i - 1, 2 * i - 2, 2 * i, 2 * i + 1) for i in range(1, k))
    rows.extend(((2 * k - 2, 4 * k + 2, 2 * k, 2 * k + 1),
                 (2 * k - 1, 2 * k + 1, 2 * k + 2, 2 * k + 3),
                 (2 * k, 2 * k + 4, 2 * k + 5, 2 * k + 2)))
    rows.extend((2 * i - 2, 2 * i, 2 * i + 1, 2 * i - 1)
                for i in range(k + 3, 2 * k + 2))
    return tuple(rows)


def face_formula(k: int) -> list[tuple[int, ...]]:
    # A dart is encoded by 4 * crossing + counterclockwise port.
    faces = [
        [(0, 0), (k + 1, 0)] + [(i, 0) for i in range(k - 1, 0, -1)],
        [(0, 1)] + [(i, 3) for i in range(2 * k + 1, k, -1)],
        [(i, 2) for i in range(k)] + [(k, 1), (2 * k + 1, 2)],
        [(k - 1, 3), (k + 1, 1), (k, 0)],
        [(k, 2)] + [(i, 1) for i in range(k + 2, 2 * k + 2)],
        [(k, 3), (k + 1, 2), (k + 2, 0)],
    ]
    faces.extend([(i, 3), (i + 1, 1)] for i in range(k - 1))
    faces.extend([(i, 2), (i + 1, 0)] for i in range(k + 2, 2 * k + 1))
    return [tuple(4 * crossing + port for crossing, port in face) for face in faces]


def canonical_cycle(cycle):
    first = cycle.index(min(cycle))
    return tuple(cycle[first:] + cycle[:first])


def verify(k: int) -> dict:
    diagram = Diagram.from_braid(3, braid_word(k))
    assert diagram.pd == pd_formula(k)
    expected = {canonical_cycle(face) for face in face_formula(k)}
    actual = {canonical_cycle(face) for face in diagram.faces()}
    assert actual == expected
    assert sorted(dart for face in expected for dart in face) == list(range(4 * diagram.crossings))
    assert not legal_moves(diagram)
    signs = diagram.signs()
    for face in diagram.faces():
        if len(face) == 2:
            assert signs[face[0] // 4] == signs[face[1] // 4]
    data = seifert_data(diagram)
    assert data["seifert_circles"] == 3
    assert data["homogeneity_defect"] == 1
    assert data["canonical_genus"] == k
    # One local braid relation and one adjacent inverse cancellation.
    word = braid_word(k)
    assert word[k - 1:k + 2] == [2, 1, 2]
    rewritten = word[:k - 1] + [1, 2, 1] + word[k + 2:]
    assert rewritten[k + 1:k + 3] == [1, -1]
    reduced = rewritten[:k + 1] + rewritten[k + 3:]
    assert reduced == braid_word(k - 1)
    return {"k": k, "crossings": diagram.crossings, "canonical_genus": k,
            "homogeneity_defect": 1, "R1_R2_moves": 0}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-k", type=int, default=50)
    args = parser.parse_args()
    if args.max_k < 2:
        parser.error("max-k must be at least two")
    records = [verify(k) for k in range(2, args.max_k + 1)]
    print(json.dumps({"checked": len(records), "first": records[0], "last": records[-1]}, indent=2))


if __name__ == "__main__":
    main()
