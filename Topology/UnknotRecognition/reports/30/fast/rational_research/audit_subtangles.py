#!/usr/bin/env python3
"""Independent adversarial and invariance checks for local disk certificates."""

from __future__ import annotations

import copy
import itertools
import json
import random
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
FAST = ROOT
sys.path.insert(0, str(FAST))
from fastunknot.diagram import Diagram, DiagramError
from fastunknot.tangle_obstruction import (
    PatternError, find_subtangle_obstruction, verify_subtangle_certificate,
)
from verify_identity_family import act_word


def rational_cf(p, q):
    result = []
    while q:
        a, remainder = divmod(p, q)
        result.append(a)
        p, q = q, remainder
    return tuple(result)


def must_reject(diagram, certificate):
    try:
        verify_subtangle_certificate(diagram, certificate)
    except (PatternError, DiagramError):
        return
    raise AssertionError("forged or inapplicable certificate accepted")


def main():
    rng = random.Random(72612)
    host = Diagram.from_rational(0, ((0, 2), (0, 5), (-1, 3)))
    host = Diagram.from_pd(host.pd)
    assert host.rational_source is None
    certificate, evidence, _ = find_subtangle_obstruction(host)
    assert certificate is not None and evidence["status"] == "KNOTTED"
    assert verify_subtangle_certificate(host, certificate) == evidence
    forged = []
    for field, value in [("version", True), ("version", 2), ("status", "KNOTTED")]:
        bad = copy.deepcopy(certificate)
        bad[field] = value
        forged.append(bad)
    for replacement in [1, True, 4, -2]:
        bad = copy.deepcopy(certificate)
        bad["rotations"][0] = replacement
        forged.append(bad)
    for replacement in [True, -1, host.crossings, certificate["crossings"][1]]:
        bad = copy.deepcopy(certificate)
        bad["crossings"][0] = replacement
        forged.append(bad)
    bad = copy.deepcopy(certificate)
    bad["pattern"]["tangles"][0][0] = False
    forged.append(bad)
    for bad in forged:
        must_reject(host, bad)

    rows = list(host.pd)
    chosen = certificate["crossings"][0]
    row = rows[chosen]
    rows[chosen] = row[1:] + row[:1]
    switched = Diagram.from_pd(rows)
    must_reject(switched, certificate)

    invariant_checks = 0
    for mirror in (False, True):
        original = host.mirror() if mirror else host
        for _ in range(20):
            labels = list(range(2 * original.crossings))
            rng.shuffle(labels)
            remap = {i: 13 + 7919 * label for i, label in enumerate(labels)}
            rows = []
            for row in original.pd:
                if rng.randrange(2):
                    row = row[2:] + row[:2]
                rows.append(tuple(remap[x] for x in row))
            rng.shuffle(rows)
            scrambled = Diagram.from_pd(rows)
            cert, result, _ = find_subtangle_obstruction(scrambled)
            assert cert is not None and result["status"] == "KNOTTED"
            assert verify_subtangle_certificate(scrambled, cert) == result
            invariant_checks += 1

    unknot_checks = 0
    for m in range(5):
        for letters in itertools.product("AB", repeat=m):
            word = "".join(letters)
            left = rational_cf(*act_word(word, (1, 1)))
            right = tuple(-a for a in rational_cf(*act_word(word, (3, 2))))
            unknot = Diagram.from_rational(0, (left, right))
            unknot = Diagram.from_pd(unknot.pd)
            cert, result, _ = find_subtangle_obstruction(unknot)
            assert cert is None and result is None
            unknot_checks += 1

    # Three-exceptional tangle occurring in a determinant-one Montesinos knot.
    three_source = {"e": 0, "tangles": [[0, 2], [0, 3], [0, 5]]}
    poincare = Diagram.from_rational(0, ((0, 2), (0, 3), (0, 5), (-1,)))
    cert, result, _ = find_subtangle_obstruction(poincare, [three_source])
    assert cert is not None and result["status"] == "KNOTTED"

    # An unknottable 1/2+1/3 pattern and a sum with an internal closed component
    # must never become local rejection templates.
    invalid_patterns = [
        {"e": 0, "tangles": [[0, 2], [0, 3]]},
        {"e": 0, "tangles": [[0, 2], [0, 2]]},
        {"e": 0, "tangles": [[2], [0, 3]]},
    ]
    for pattern in invalid_patterns:
        try:
            find_subtangle_obstruction(host, [pattern])
        except (PatternError, DiagramError):
            pass
        else:
            raise AssertionError("invalid local pattern was not rejected")

    result = {
        "status": "all local certificate audit diagnostics passed",
        "forged_certificates_rejected": len(forged),
        "selected_crossing_switch_rejected": True,
        "crossing_reorder_halfturn_relabel_mirror_checks": invariant_checks,
        "known_unknot_diagrams_without_false_rejection": unknot_checks,
        "three_exceptional_determinant_one_occurrence_verified": True,
        "inapplicable_or_closed_component_patterns_rejected": len(invalid_patterns),
    }
    Path(sys.argv[1]).write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
