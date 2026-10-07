"""Audit the intrinsic multiplicities of a partial Khovanov complex.

This is an optional diagnostic, not an extra pass in the recognition pipeline.
The positive-degree radical of the matching algebra kills every morphism
between distinct matchings and retains the undotted identity coefficient on
an endomorphism.  The resulting scalar chain complex splits by matching.
Its Betti numbers equal the object multiplicities after exhaustive unit
cancellation, independent of the pivot rule.  See the accompanying article.

Both FastScan and the bits/sets variants of ScanComplex are supported.
No crossingless-disk or Catalan state-count assumption is used here.
"""
from __future__ import annotations

from collections import defaultdict


def _matching_key(matching):
    return tuple(sorted(tuple(sorted(pair)) for pair in matching))


def _snapshot(scan):
    if hasattr(scan, "mid"):
        objects = {i: (scan.algebra.pairs[m], scan.deg[i])
                   for i, m in enumerate(scan.mid) if m is not None}
        out = {i: scan.out[i] for i in objects}
    else:
        objects = {i: (_matching_key(m), h) for i, (m, h) in scan.objects.items()}
        out = {i: scan.out.get(i, {}) for i in objects}
    return objects, out


def _scalar(value):
    return bool(value & 1) if isinstance(value, int) else frozenset() in value


def _rank(rows):
    pivots = {}
    for row in rows:
        while row:
            top = row.bit_length() - 1
            old = pivots.get(top)
            if old is None:
                pivots[top] = row
                break
            row ^= old
    return len(pivots)


def residue_profile(scan, *, check_squared=False):
    """Return {(matching, degree): canonical multiplicity} without changing scan.

Only nonzero multiplicities are returned.  A negative dimension or a failed
optional scalar d^2 check reports an invalid complex; it never yields a knot
verdict.  Cost is the sum of ordinary F2 rank computations on scalar blocks.
"""
    objects, out = _snapshot(scan)
    groups = defaultdict(list)
    for ident, key in objects.items():
        groups[key].append(ident)
    scalar_out = {}
    for source, (matching, degree) in objects.items():
        row = []
        for target, value in out[source].items():
            if target not in objects:
                raise ArithmeticError("differential points to a deleted object")
            target_matching, target_degree = objects[target]
            if target_degree != degree + 1:
                raise ArithmeticError("differential does not increase degree by one")
            if target_matching == matching and _scalar(value):
                row.append(target)
        scalar_out[source] = row
    if check_squared:
        for row in scalar_out.values():
            parity = set()
            for middle in row:
                parity.symmetric_difference_update(scalar_out[middle])
            if parity:
                raise ArithmeticError("residue differential has nonzero square")
    ranks = {}
    for (matching, degree), sources in groups.items():
        index = {target: col for col, target in
                 enumerate(groups.get((matching, degree + 1), []))}
        rows = [sum(1 << index[target] for target in scalar_out[source])
                for source in sources]
        ranks[matching, degree] = _rank(rows)
    answer = {}
    for key, sources in groups.items():
        matching, degree = key
        beta = len(sources) - ranks.get(key, 0) - ranks.get((matching, degree - 1), 0)
        if beta < 0:
            raise ArithmeticError("negative residue homology dimension")
        if beta:
            answer[key] = beta
    return answer


def object_profile(scan):
    """Return actual object counts with the same keys as residue_profile."""
    objects, _ = _snapshot(scan)
    answer = defaultdict(int)
    for key in objects.values():
        answer[key] += 1
    return dict(answer)


def profile_records(profile):
    """A deterministic, JSON-serializable list for experiment artifacts."""
    return [{"matching": [list(pair) for pair in matching],
             "degree": degree, "multiplicity": count}
            for (matching, degree), count in sorted(profile.items())]
