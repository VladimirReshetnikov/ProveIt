"""Graded two-term controls with a nonzero radical minimal differential.

These satisfy the scanner's grading equations but are not claimed to arise
from a classical diagram. Their survivors occupy consecutive degrees, so the
existing residue degree-gap shortcut is inapplicable.
"""
import random

from fastunknot.graded_transfer import BinaryBasis, GradedTransferScan, binary_contraction, bits


def invertible_columns(size, rng):
    basis = BinaryBasis()
    result = []
    while len(result) < size:
        column = rng.getrandbits(size)
        if basis.add(column):
            result.append(column)
    return result


def dense_radical_control(size, seed=2026100803):
    rng = random.Random(seed + size)
    scan = GradedTransferScan(shape_cache=False)
    matching = scan.algebra.intern(((0, 1),))
    scan.points = frozenset((0, 1))
    source0 = list(range(size + 1))
    target0 = list(range(size + 1, 2 * size + 1))
    source2 = list(range(2 * size + 1, 3 * size + 1))
    target2 = list(range(3 * size + 1, 4 * size + 2))
    scan.live = 4 * size + 2
    scan.mid = [matching] * scan.live
    scan.deg = [0] * (size + 1) + [1] * size + [0] * size + [1] * (size + 1)
    scan.qshift = [0] * (2 * size + 1) + [2] * (2 * size + 1)
    scan.out = [{} for _ in scan.mid]
    for a, vector in zip(source0, invertible_columns(size, rng) + [rng.getrandbits(size)]):
        for j in bits(vector):
            scan.out[a][target0[j]] = 1
    for a, vector in zip(source2, invertible_columns(size, rng)):
        for j in bits(vector):
            scan.out[a][target2[j]] = 1
        if rng.getrandbits(1):
            scan.out[a][target2[-1]] = 1
    scalar = binary_contraction(scan)
    assert len(scalar['i']) == 2
    for a in source0:
        for j in bits(rng.getrandbits(size + 1)):
            scan.out[a][target2[j]] = 2
    relevant_sources = list(bits(scalar['i'][0]))
    relevant_targets = [a for a in target2 if scalar['p'][a] & 2]
    coefficient = sum(scan.out[a].get(b, 0) != 0
                      for a in relevant_sources for b in relevant_targets) % 2
    if not coefficient:
        a, b = relevant_sources[0], relevant_targets[0]
        if b in scan.out[a]:
            del scan.out[a][b]
        else:
            scan.out[a][b] = 2
    scan.inc = [set() for _ in scan.mid]
    for a, row in enumerate(scan.out):
        for b in row:
            scan.inc[b].add(a)
    return scan


def long_transfer_control(length):
    """A minimal x1...xr map needing r perturbations, not a first-order map."""
    scan = GradedTransferScan(shape_cache=False)
    matching = scan.algebra.intern(tuple((2*j, 2*j+1) for j in range(length)))
    scan.points = frozenset(range(2*length))
    scan.mid, scan.deg, scan.qshift, scan.out = [matching], [0], [0], [{}]
    previous = 0
    for j in range(1, length + 1):
        target = len(scan.mid)
        scan.mid.append(matching)
        scan.deg.append(1)
        scan.qshift.append(2*j)
        scan.out.append({})
        scan.out[previous][target] = 1 << (1 << (j-1))
        if j < length:
            previous = len(scan.mid)
            scan.mid.append(matching)
            scan.deg.append(0)
            scan.qshift.append(2*j)
            scan.out.append({target: 1})
    scan.live = len(scan.mid)
    scan.inc = [set() for _ in scan.mid]
    for a, row in enumerate(scan.out):
        for b in row:
            scan.inc[b].add(a)
    return scan
