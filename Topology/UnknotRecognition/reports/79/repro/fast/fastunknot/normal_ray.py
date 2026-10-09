"""Short essential-disc certificates for primitive standard normal rays.

The only algebraic witness is a full-rank minor modulo a fixed known prime.
There is no expansion into discs or intersections and no orbit computation.
This certifies the supplied triangulation; source-diagram provenance is an
independent certificate and can be checked by the maintained exterior API.
"""

from math import gcd

from .normal_surface_geometry import (
    _prepare, _coordinates, _boundary_graph, _fingerprint,
)
from .normal_surface_parity import _parity_certificate


_PRIMES = (65521, 1000000007, 2, 3, 5, 7, 11, 101, 1009)


class _RankLimit(Exception):
    pass


def _independent_rows(matching, support, prime, tick):
    """Sparse forward elimination, retaining source row identities."""
    positions = {column: index for index, column in enumerate(support)}
    pivots, selected = {}, []
    for index, equation in enumerate(matching):
        tick()
        row = {positions[i]: value % prime for i, value in equation.items()
               if i in positions and value % prime}
        while row:
            tick()
            pivot = min(row)
            if pivot not in pivots:
                inverse = pow(row[pivot], -1, prime)
                pivots[pivot] = {j: value * inverse % prime
                                 for j, value in row.items()}
                selected.append(index)
                break
            multiplier = row[pivot]
            for j, value in pivots[pivot].items():
                tick()
                residue = (row.get(j, 0) - multiplier * value) % prime
                if residue:
                    row[j] = residue
                else:
                    row.pop(j, None)
        if len(selected) == len(support) - 1:
            return selected
    return selected


def certify_normal_ray_disc(triangulation, coordinates, *,
                            max_rank_operations=None, check=lambda: None):
    """Return DISC_FOUND only after a primitive extreme disc is certified.

    Missing extremality at the tried primes is NOT_CERTIFIED, not a claim
    that the vector is nonextreme or that the manifold has no disc.
    A local operation cap returns INCONCLUSIVE; caller cancellation propagates.
    Input coordinates are never silently divided or changed.
    """
    check()
    if max_rank_operations is not None and (
            type(max_rank_operations) is not int or max_rank_operations < 0):
        raise ValueError('rank operation cap must be a nonnegative integer or None')
    prepared = _prepare(triangulation, check)
    analysed = _coordinates(prepared, coordinates, check)
    rows = analysed['rows']
    flat = [value for row in rows for value in row]
    common = 0
    for value in flat:
        common = gcd(common, value)
    if (common != 1 or analysed['euler_characteristic'] != 1
            or analysed['boundary_arcs'] == 0):
        return dict(status='NOT_CERTIFIED', reason='primitive Euler-one boundary vector required')
    parity = _parity_certificate(_boundary_graph(prepared, analysed, check), check)
    if not parity['nonzero']:
        return dict(status='NOT_CERTIFIED', reason='boundary class is zero modulo two')
    support = [i for i, value in enumerate(flat) if value]
    operations = 0

    def tick():
        nonlocal operations
        check()
        if max_rank_operations is not None and operations >= max_rank_operations:
            raise _RankLimit
        operations += 1

    try:
        for prime in _PRIMES:
            selected = _independent_rows(prepared['matching'], support, prime, tick)
            if len(selected) == len(support) - 1:
                certificate = dict(
                    schema='normal-extreme-disc-v1',
                    input_sha256=_fingerprint(triangulation, analysed, check),
                    prime=prime, rank_rows=selected, boundary_homology=parity,
                )
                return dict(status='DISC_FOUND', coordinates=rows,
                            certificate=certificate,
                            stats=dict(support_size=len(support), prime=prime,
                                       rank_operations=operations),
                            trust='essential disc in the supplied triangulation')
    except _RankLimit:
        return dict(status='INCONCLUSIVE', reason='rank operation allowance exhausted',
                    stats=dict(rank_operations=operations))
    return dict(status='NOT_CERTIFIED', reason='no full-rank minor at the tried primes',
                stats=dict(rank_operations=operations))
