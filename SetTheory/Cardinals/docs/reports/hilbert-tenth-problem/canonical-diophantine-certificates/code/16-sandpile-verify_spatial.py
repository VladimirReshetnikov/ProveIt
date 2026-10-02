#!/usr/bin/env python3
"""Exact checks of the explicit periodic-table spatial polynomial compiler."""
from __future__ import annotations
import json
from pathlib import Path
from sandpile_spatial import PeriodicInput, SpatialInstance


def main() -> None:
    if not __debug__:
        raise RuntimeError("verification requires assertions; do not use python -O")
    tests = accepted = mutations = 0
    line_results = []
    for chips in range(13):
        source = PeriodicInput((1,), (0,), (((0,), chips),))
        radii = []
        for R in range(7):
            inst = SpatialInstance.build(source, R)
            tests += 1
            try:
                w = inst.certificate()
            except ValueError:
                continue
            assert inst.evaluate(w) == 0
            accepted += 1
            radii.append(R)
            d = source.dimension
            expected_n = 10*(2*R+1)**d+2*d*(6*R+1)*(2*R+1)**(d-1)+1
            expected_s = 10*(2*R+1)**d+2*d*(7*R+1)*(2*R+1)**(d-1)+1
            assert len(w) == expected_n
            assert len(inst.polynomial_terms(w)) == expected_s
            for field in w:
                changed = dict(w)
                changed[field] += 1
                assert inst.evaluate(changed) > 0
                mutations += 1
        assert radii == [max(chips//2-1, 0)]
        line_results.append({"chips": chips, "canonical_radius": radii[0]})

    # The prescribed defect radius can be nonzero even when nothing topples.
    source = PeriodicInput((2,), (0, 1), (((2,), 0),))
    for R in range(2, 6):
        inst = SpatialInstance.build(source, R)
        tests += 1
        try:
            w = inst.certificate()
        except ValueError:
            assert R != 2
        else:
            assert R == 2 and w["rho"] == 0 and inst.evaluate(w) == 0
            accepted += 1
    assert source.height((-1,)) == 1 and source.height((-2,)) == 0

    # Maximal stable backgrounds plus one chip must fail spatial closure.
    explosive = 0
    for dim in (1, 2):
        source = PeriodicInput((1,)*dim, (2*dim-1,), (((0,)*dim, 2*dim),))
        for R in range(4):
            tests += 1
            try:
                SpatialInstance.build(source, R).certificate()
            except ValueError as exc:
                assert "collar" in str(exc)
                explosive += 1
            else:
                raise AssertionError("explosive input acquired a spatial certificate")

    count_checks = 0
    for dim in (1, 2, 3):
        for R in (0, 1, 2):
            source = PeriodicInput((1,)*dim, (0,))
            inst = SpatialInstance.build(source, R, minimum_radius=R)
            w = inst.certificate()
            n = 10*(2*R+1)**dim+2*dim*(6*R+1)*(2*R+1)**(dim-1)+1
            s = 10*(2*R+1)**dim+2*dim*(7*R+1)*(2*R+1)**(dim-1)+1
            assert len(w) == n and len(inst.polynomial_terms(w)) == s
            assert inst.evaluate(w) == 0
            count_checks += 1

    source = PeriodicInput((1,), (0,), (((0,), 2),))
    inst = SpatialInstance.build(source, 0)
    poly = inst.symbolic_polynomial()
    w = inst.certificate()
    assert poly.total_degree() == 3
    assert poly.as_expr().subs({x: w[str(x)] for x in poly.gens}) == 0
    assert len(poly.gens) == 13
    result = {"schema": 1, "periodic_table_box_tests": tests,
              "canonical_certificates": accepted, "coordinate_mutations_rejected": mutations,
              "explosive_collar_rejections": explosive, "spatial_count_checks": count_checks,
              "one_site_symbolic_degree": 3, "one_site_symbolic_variables": 13,
              "line_results": line_results, "all_checks_passed": True}
    Path("verification_spatial.json").write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
