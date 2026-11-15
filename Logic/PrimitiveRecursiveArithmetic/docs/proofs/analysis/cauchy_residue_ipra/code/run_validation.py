"""Run focused checks and emit reproducible exact/decimal example data."""

import json
import subprocess
import sys
from pathlib import Path

from rational_contours import (
    CQ, add_chains, edge_chain, pi_interval, quadrature_derivative_error_bound,
    reciprocal_derivative_lipschitz_bound, residue_example, trap_chain, triangles_boundary,
)


def main():
    directory = Path(__file__).resolve().parent
    subprocess.run([sys.executable, "-m", "unittest", "-v", "test_rational_contours.py"],
                   cwd=directory, check=True)
    f, poles, triangles, outer, holes = residue_example()
    pi_lo, pi_hi = pi_interval(24)
    records = []
    for label, edges, multiplier in [("outer", outer, 6), ("hole_at_0", holes[0], 2),
                                     ("hole_at_1", holes[1], 4)]:
        lipschitz = reciprocal_derivative_lipschitz_bound(edges, poles)
        for depth in (5, 7, 9):
            value = trap_chain(f, edges, depth, bits=32)
            error = quadrature_derivative_error_bound(edges, lipschitz, depth, 32)
            records.append({
                "contour": label, "depth": depth, "evaluation_bits": 32,
                "edge_count": len(edges), "quadrature_exact": value.json(),
                "quadrature_display": {"re": float(value.re), "im": float(value.im)},
                "derivative_lipschitz_bound": str(lipschitz), "error_bound_exact": str(error),
                "error_bound_display": float(error),
                "expected_imaginary_interval_exact": [str(multiplier*pi_lo), str(multiplier*pi_hi)],
            })
    expected = add_chains(edge_chain(outer), *(edge_chain(hole, -1) for hole in holes))
    result = {
        "status": "finite validation only; not a formal proof",
        "example": "f(z)=1/z+2/(z-1)",
        "geometry": {
            "outer_rectangle": "[-2,3] x [-2,2]",
            "holes": "squares of half-side 1/4 centered at 0 and 1",
            "triangles": len(triangles),
            "boundary_identity_exact": triangles_boundary(triangles) == expected,
        },
        "pi_interval_exact": [str(pi_lo), str(pi_hi)],
        "pi_interval_display": [float(pi_lo), float(pi_hi)],
        "pi_terms": 24,
        "quadratures": records,
    }
    output = directory / "validation_results.json"
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()

