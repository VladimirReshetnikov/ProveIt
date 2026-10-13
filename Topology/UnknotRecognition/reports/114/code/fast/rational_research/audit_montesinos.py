#!/usr/bin/env python3
"""Independent finite diagnostics for the Montesinos arithmetic/PD boundary.

These tests are independent of the production arithmetic recurrence.  They compare
raw, separately primitive denominators with normalized production arithmetic,
construct all component counts independently of the odd-determinant gate,
and compare odd cases to the existing Alexander polynomial of the actual PD.
"""

from __future__ import annotations

import json
import pickle
import random
import sys
from math import gcd, prod
from pathlib import Path

FAST = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(FAST))
from fastunknot.alexander import alexander_polynomial, evaluate
from fastunknot.diagram import Diagram, DiagramError
from fastunknot.rational import (
    _Builder, continued_fraction, montesinos_certificate,
    verify_montesinos_certificate,
)
from fastunknot.recognize import recognize


def independent_cf(cf):
    mat = ((1, 0), (0, 1))
    for a in cf:
        # Literal matrix multiplication by ((a,1),(1,0)).
        mat = (
            (mat[0][0] * a + mat[0][1], mat[0][0]),
            (mat[1][0] * a + mat[1][1], mat[1][0]),
        )
    p, q = mat[0][0], mat[1][0]
    assert gcd(p, q) == 1
    if q < 0 or (q == 0 and p < 0):
        p, q = -p, -q
    return p, q


def raw_pd_and_components(e, tangles):
    builder = _Builder()
    boundary = builder.rational((e,))
    for cf in tangles:
        boundary = builder.horizontal(boundary, builder.rational(cf))
    return builder.numerator(boundary)


def main():
    rng = random.Random(34992)
    sources = [
        (-1, ((0, 2), (0, 3), (0, 5))),  # determinant-one nontrivial cover
        (0, ((0, 2), (0, 2))),           # no reduction of gluing numerator
        (0, ((0,),)),
        (1, ()),
        (0, ((3,),)),
        (0, ((1, 0, -1), (0, 3))),
    ]
    while len(sources) < 1200:
        e = rng.randrange(-2, 3)
        tangles = tuple(
            tuple(rng.randrange(-2, 3) for _ in range(rng.randrange(1, 5)))
            for _ in range(rng.randrange(0, 5))
        )
        if abs(e) + sum(abs(a) for cf in tangles for a in cf) > 14:
            continue
        if any(independent_cf(cf)[1] == 0 for cf in tangles):
            continue
        sources.append((e, tangles))

    counts = {"sources": 0, "knot_pd_alexander_comparisons": 0,
              "link_component_comparisons": 0, "pickle_mirror_checks": 0,
              "determinant_one_nontrivial": 0}
    for e, tangles in sources:
        slopes = [independent_cf(cf) for cf in tangles]
        for cf, slope in zip(tangles, slopes):
            assert continued_fraction(cf) == slope
        den = prod(q for _, q in slopes)
        det = e * den + sum(p * (den // q) for p, q in slopes)
        pd, components = raw_pd_and_components(e, tangles)
        assert (components == 1) == (det % 2 == 1), (e, tangles, det, components)
        counts["sources"] += 1
        if det % 2 == 0:
            try:
                montesinos_certificate(e, tangles)
            except DiagramError:
                pass
            else:
                raise AssertionError("multi-component source was accepted")
            counts["link_component_comparisons"] += 1
            continue
        certificate = montesinos_certificate(e, tangles)
        assert certificate["signed_determinant"] == det
        assert verify_montesinos_certificate(e, tangles, certificate)
        actual = Diagram.from_pd(pd)
        alexander_det = abs(evaluate(alexander_polynomial(actual), -1))
        assert alexander_det == abs(det), (e, tangles, det, alexander_det)
        counts["knot_pd_alexander_comparisons"] += 1
        if certificate["determinant"] == 1 and certificate["status"] == "KNOTTED":
            counts["determinant_one_nontrivial"] += 1
        checked = Diagram.from_rational(e, tangles)
        assert checked.pd == actual.pd
        for obj in (checked, checked.mirror()):
            restored = pickle.loads(pickle.dumps(obj))
            assert restored == obj
            assert restored.rational_source == obj.rational_source
            assert recognize(restored).status == certificate["status"]
            counts["pickle_mirror_checks"] += 1

    # Verify that public constructor reinitialization cannot retain stale provenance.
    certified_unknot = Diagram.from_rational(1, ())
    trefoil = Diagram.from_json(json.loads((FAST / "examples" / "trefoil.json").read_text()))
    try:
        certified_unknot.__init__(trefoil.pd)
    except AttributeError:
        reinitialization_guard = "present: reinitialization rejected"
    else:
        result = recognize(certified_unknot)
        reinitialization_guard = {
            "present": False,
            "replacement_pd_is_trefoil": certified_unknot.pd == trefoil.pd,
            "retained_source": certified_unknot.rational_source,
            "returned_status": result.status,
        }
    report = {"status": "arithmetic, PD, parity, and serialization diagnostics passed",
              "counts": counts, "reinitialization_guard": reinitialization_guard}
    target = Path(sys.argv[1])
    target.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
