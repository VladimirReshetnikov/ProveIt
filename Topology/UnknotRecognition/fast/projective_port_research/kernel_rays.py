"""Complete local rays from one reusable exact matching kernel.

This research module enumerates the rays of ``x >= 0, A x = 0`` before
discarding supports containing a conflict pair.  If the columns of K are a
basis of ker(A), the coordinate forms (the rows of K) are inequalities in
h = nullity(A) parameters.  An extreme ray has h-1 independent active forms,
even when the nonnegative cone is lower dimensional.  Proportional nonzero
forms define the same hyperplane and are enumerated only once.  Their signs
are *not* discarded from the feasibility test: that test reconstructs every
original coordinate of Kz.

After one polynomial exact kernel computation, there are at most
binom(m, h-1) systems of dimension h, where m <= n counts distinct coordinate
hyperplanes.  Reconstruction and conflict testing cost polynomial work per
system.  Determinant bounds give polynomial bit lengths in the original
matrix input.  This parameter bound does not bound h for a knot exterior.

The candidate cap excludes kernel preparation, normalization, reconstruction
and output sorting; it is neither a wall-time nor a memory limit.  Cancellation
callbacks run during preparation, elimination, and enumeration.  Exceptions
from callbacks propagate unchanged, including ResourceLimit.
"""
from fractions import Fraction as Q
from itertools import combinations
from math import comb

from projective_ports.exact import primitive
from projective_ports.model import Block, ResourceLimit


def _nullspace(rows, n, check):
    """Exact rational elimination with cancellation at each row operation."""
    check()
    a = []
    for row in rows:
        check()
        a.append(list(map(Q, row)))
    pivots = []
    for j in range(n):
        check()
        p = next((i for i in range(len(pivots), len(a)) if a[i][j]), None)
        if p is None:
            continue
        i = len(pivots)
        a[i], a[p] = a[p], a[i]
        scale = a[i][j]
        a[i] = [v / scale for v in a[i]]
        for k in range(len(a)):
            check()
            if k != i and a[k][j]:
                scale = a[k][j]
                a[k] = [u - scale * v for u, v in zip(a[k], a[i])]
        pivots.append(j)
        if len(pivots) == len(a):
            break
    pivot_set = set(pivots)
    out = []
    for j in range(n):
        check()
        if j in pivot_set:
            continue
        v = [Q(0)] * n
        v[j] = Q(1)
        for i, k in enumerate(pivots):
            v[k] = -a[i][j]
        out.append(tuple(v))
    return tuple(out)


class KernelCone:
    """Prepared matching kernel; objectives and coordinate-zero queries are absent.

    ``rays`` returns admissible primitive full-cone extreme rays.  Coordinate
    zero queries may filter these rays afterward because a zero-coordinate
    face creates no new rays.  Adding general equations requires a new kernel.
    """

    def __init__(self, block, *, check=lambda: None):
        if not isinstance(block, Block):
            raise TypeError('block must be a validated projective_ports Block')
        check()
        self.block = block
        self.basis = _nullspace(block.equations, block.n, check)
        self.h = len(self.basis)
        forms = []
        hyperplanes = set()
        zero_forms = 0
        for j in range(block.n):
            check()
            row = tuple(v[j] for v in self.basis)
            forms.append(row)
            if any(row):
                hyperplanes.add(primitive(row, sign_canonical=True))
            else:
                zero_forms += 1
        self.forms = tuple(forms)
        self.hyperplanes = tuple(sorted(hyperplanes))
        m = len(hyperplanes)
        self.statistics = dict(coordinates=block.n, equations=len(block.equations),
            nullity=self.h, hyperplanes=m, zero_coordinate_forms=zero_forms,
            repeated_coordinate_hyperplanes=block.n-zero_forms-m,
            candidate_bound=comb(m, self.h-1) if self.h else 0,
            preparation_kernel_solves=1)

    def rays(self, *, max_supports=None, check=lambda: None, stats=None):
        """Enumerate all rays; ``max_supports`` counts candidate hyperplane sets.

        ``stats`` is an optional output dictionary.  Candidate counts include
        the first refused candidate; candidate kernel solves do not.  Calling
        this method again reuses preparation but repeats candidate enumeration.
        """
        if max_supports is not None and (type(max_supports) is not int or max_supports < 0):
            raise ValueError('max_supports must be a nonnegative integer or None')
        if stats is not None and type(stats) is not dict:
            raise TypeError('stats must be a dict or None')
        info = {} if stats is None else stats
        info.update(self.statistics)
        info.update(candidates=0, candidate_kernel_solves=0, independent_systems=0,
                    feasible_systems=0, incompatible_systems=0, rays=0, complete=False)
        check()
        if not self.h:
            info['complete'] = True
            return ()
        out = set()
        for rows in combinations(self.hyperplanes, self.h-1):
            check()
            info['candidates'] += 1
            if max_supports is not None and info['candidates'] > max_supports:
                raise ResourceLimit('local kernel-hyperplane budget exhausted')
            info['candidate_kernel_solves'] += 1
            basis = _nullspace(rows, self.h, check)
            if len(basis) != 1:
                continue
            info['independent_systems'] += 1
            z = basis[0]
            x = []
            for row in self.forms:
                check()
                x.append(sum((a*b for a, b in zip(row, z)), Q(0)))
            if all(a <= 0 for a in x):
                x = [-a for a in x]
            if any(a < 0 for a in x):
                continue
            # Injectivity of the prepared kernel basis makes x nonzero.
            info['feasible_systems'] += 1
            support = tuple(j for j, a in enumerate(x) if a)
            if not self.block.compatible_support(support):
                info['incompatible_systems'] += 1
                continue
            out.add(primitive(x))
            info['rays'] = len(out)
        check()
        result = tuple(sorted(out))
        info['complete'] = True
        return result


def enumerate_rays_kernel(block, *, max_supports=None, check=lambda: None, stats=None):
    """Drop-in research alternative to the report's local ray enumerators."""
    if max_supports is not None and (type(max_supports) is not int or max_supports < 0):
        raise ValueError('max_supports must be a nonnegative integer or None')
    if stats is not None and type(stats) is not dict:
        raise TypeError('stats must be a dict or None')
    if stats is not None:
        # A cancellation during preparation must not leave an earlier call's
        # successful completion flag in a reused output dictionary.
        stats.clear()
        stats.update(complete=False, preparation_kernel_solves=0)
    return KernelCone(block, check=check).rays(
        max_supports=max_supports, check=check, stats=stats)
