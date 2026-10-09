"""Independent sparse modular-rank replay for primitive normal disc rays.

Shares the maintained finite-manifold and coordinate validator. Does not
import a ray producer, LP solver, sector constructor, or orbit algorithm.
"""

from math import gcd

from .normal_surface_geometry import (
    _prepare, _coordinates, _boundary_graph, _fingerprint, NormalOrbitError,
)
from .normal_surface_parity import _verify_parity


def verify_normal_ray_disc(triangulation, coordinates, certificate, *, check=lambda: None):
    """Replay exact normal geometry, primitivity, rank and essential boundary.

    A rank-(s-1) matrix modulo a prime has rational rank at least s-1.
    The exact positive kernel vector bounds that rank by s-1. Its ray is
    therefore extreme, and its primitive integral normal surface connected.
    Euler one and nonempty boundary force a disc. A nonzero mod-two class
    forces its single boundary curve to be essential in the validated torus.
    """
    check()
    fields = {'schema', 'input_sha256', 'prime', 'rank_rows', 'boundary_homology'}
    if (type(certificate) is not dict or set(certificate) != fields
            or certificate.get('schema') != 'normal-extreme-disc-v1'):
        return False
    prime = certificate['prime']
    # Fixed, explicitly known primes: no unverified primality claim is accepted.
    if type(prime) is not int or prime not in (2, 3, 5, 7, 11, 101, 1009, 65521, 1000000007):
        return False
    try:
        prepared = _prepare(triangulation, check)
        analysed = _coordinates(prepared, coordinates, check)
    except NormalOrbitError:
        return False
    if certificate['input_sha256'] != _fingerprint(triangulation, analysed, check):
        return False
    flat = [value for row in analysed['rows'] for value in row]
    common = 0
    for value in flat:
        check()
        common = gcd(common, value)
    if (common != 1 or analysed['euler_characteristic'] != 1
            or analysed['boundary_arcs'] <= 0):
        return False
    positive = {i for i, value in enumerate(flat) if value}
    selected = certificate['rank_rows']
    if (type(selected) is not list or len(selected) != len(positive) - 1
            or any(type(i) is not int or not 0 <= i < len(prepared['matching'])
                   for i in selected) or len(set(selected)) != len(selected)):
        return False
    # Descending-column elimination is separate from the producer's forward
    # ascending-column elimination, and processes only the submitted rows.
    basis = {}
    for i in selected:
        check()
        row = {j: value % prime for j, value in prepared['matching'][i].items()
               if j in positive and value % prime}
        while row:
            check()
            j = max(row)
            if j not in basis:
                value = row[j]
                inverse = pow(value, prime - 2, prime)
                basis[j] = {k: entry * inverse % prime for k, entry in row.items()}
                break
            factor = row[j]
            for k, entry in basis[j].items():
                check()
                value = (row.get(k, 0) - factor * entry) % prime
                if value:
                    row[k] = value
                else:
                    row.pop(k, None)
        else:
            return False
    parity = certificate['boundary_homology']
    if type(parity) is not dict or parity.get('nonzero') is not True:
        return False
    return _verify_parity(_boundary_graph(prepared, analysed, check), parity, check)
