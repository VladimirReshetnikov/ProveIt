"""Exact solve dimensions for a repeated coordinate-form family; no timings."""
from collections import Counter
from math import comb
import sys
from unittest.mock import patch

from .filtered_native import save
from . import kernel_rays
from .test_kernel_rays import repeated_coordinates
from projective_ports import model


def main():
    counts = {a:Counter() for a in ('prior', 'kernel')}
    old, new = model.nullspace, kernel_rays._nullspace

    def prior(rows, n):
        rows = tuple(rows)
        counts['prior'][len(rows), n] += 1
        return old(rows, n)

    def kernel(rows, n, check):
        rows = tuple(rows)
        counts['kernel'][len(rows), n] += 1
        return new(rows, n, check)

    b = repeated_coordinates(3, 4)
    with patch.object(model, 'nullspace', prior):
        r = model.enumerate_rays_by_zeros(b)
    with patch.object(kernel_rays, '_nullspace', kernel):
        s = kernel_rays.enumerate_rays_kernel(b)
    assert r == s and len(r) == 3
    assert counts['prior'] == {(9, 12):1, (9, 10):66}
    assert counts['kernel'] == {(9, 12):1, (2, 3):3}
    stats = {}
    large = kernel_rays.enumerate_rays_kernel(repeated_coordinates(3, 20), stats=stats)
    assert len(large) == 3 and stats['candidate_kernel_solves'] == 3
    save(sys.argv[1], dict(passed=True,
        solve_dimensions={a:[dict(rows=m, columns=n, count=v) for (m,n),v in c.items()]
                          for a,c in counts.items()},
        small_rays=r, large_kernel_stats=stats,
        large_prior_candidate_bound=comb(60, 2), large_prior_not_run=True))


if __name__ == '__main__':
    main()
