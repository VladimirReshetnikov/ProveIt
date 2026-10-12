"""Small exact Smith kernel with elementary-operation evidence.

This Euclidean implementation is a research/reference backend. Termination
and exactness follow from the descent proof in the article, but we do NOT
claim its worst-case bit complexity equals Kannan--Bachem's polynomial bound.
The condensation itself is independent of this optional normal-form stage.
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import Sequence


class WorkLimit(RuntimeError):
    """Resource exhaustion: no result, never a topological verdict."""


def _matrix(matrix: Sequence[Sequence[int]], cols: int | None) -> tuple[list[list[int]], int]:
    a = [list(row) for row in matrix]
    n = len(a[0]) if a else (0 if cols is None else cols)
    if type(n) is not int or n < 0 or (cols is not None and cols != n):
        raise ValueError("inconsistent matrix width")
    if any(len(row) != n or any(type(x) is not int for x in row) for row in a):
        raise ValueError("matrix must be rectangular over the integers")
    return a, n


@dataclass(frozen=True)
class SmithCertificate:
    rows: int
    cols: int
    diagonal: tuple[int, ...]
    operations: tuple[tuple, ...]
    peak_entry_bits: int


def smith(matrix: Sequence[Sequence[int]], *, cols: int | None = None,
          max_operations: int | None = 1_000_000,
          max_entry_bits: int | None = None) -> SmithCertificate:
    a, n = _matrix(matrix, cols)
    m = len(a)
    if max_operations is not None and (type(max_operations) is not int or max_operations < 0):
        raise ValueError("invalid operation allowance")
    if max_entry_bits is not None and (type(max_entry_bits) is not int or max_entry_bits < 1):
        raise ValueError("invalid bit allowance")
    ops = []
    peak = max((abs(x).bit_length() for row in a for x in row), default=0)
    if max_entry_bits is not None and peak > max_entry_bits:
        raise WorkLimit("input exceeds bit allowance")

    def emit(op):
        nonlocal peak
        if max_operations is not None and len(ops) >= max_operations:
            raise WorkLimit("Smith operation allowance exhausted")
        kind, i = op[0], op[1]
        if kind == 'rs':
            j = op[2]; a[i], a[j] = a[j], a[i]
        elif kind == 'cs':
            j = op[2]
            for row in a:
                row[i], row[j] = row[j], row[i]
        elif kind == 'ra':
            j, q = op[2:]
            a[i] = [x + q*y for x, y in zip(a[i], a[j])]
        elif kind == 'ca':
            j, q = op[2:]
            for row in a:
                row[i] += q * row[j]
        elif kind == 'rn':
            a[i] = [-x for x in a[i]]
        else:
            raise AssertionError("internal invalid operation")
        ops.append(op)
        peak = max(peak, max((abs(x).bit_length() for row in a for x in row), default=0))
        if max_entry_bits is not None and peak > max_entry_bits:
            raise WorkLimit("Smith bit allowance exhausted")

    k = 0
    while k < min(m, n):
        nonzero = [(abs(a[i][j]), i, j) for i in range(k, m)
                   for j in range(k, n) if a[i][j]]
        if not nonzero:
            break
        _, i, j = min(nonzero)
        if i != k: emit(('rs', i, k))
        if j != k: emit(('cs', j, k))
        while True:
            restart = False
            for i in range(k+1, m):
                if a[i][k]:
                    q = a[i][k] // a[k][k]
                    if q: emit(('ra', i, k, -q))
                    if a[i][k]:
                        emit(('rs', i, k)); restart = True; break
            if restart:
                continue
            for j in range(k+1, n):
                if a[k][j]:
                    q = a[k][j] // a[k][k]
                    if q: emit(('ca', j, k, -q))
                    if a[k][j]:
                        emit(('cs', j, k)); restart = True; break
            if restart:
                continue
            bad = next(((i, j) for i in range(k+1, m) for j in range(k+1, n)
                        if a[i][j] % a[k][k]), None)
            if bad is None:
                break
            # Bring an offending entry into the pivot row; Euclid decreases
            # the absolute pivot on the next nonzero remainder.
            emit(('ra', k, bad[0], 1))
        if a[k][k] < 0:
            emit(('rn', k))
        k += 1
    return SmithCertificate(m, n, tuple(a[i][i] for i in range(k)), tuple(ops), peak)


def verify_smith(matrix: Sequence[Sequence[int]], cert: SmithCertificate, *,
                 cols: int | None = None, max_operations: int = 1_000_000,
                 max_entry_bits: int | None = None) -> bool:
    """Checks only local unimodular operations and the final Smith conditions."""
    try:
        a, n = _matrix(matrix, cols)
        m = len(a)
        if not isinstance(cert, SmithCertificate) or (cert.rows, cert.cols) != (m, n):
            return False
        if type(max_operations) is not int or max_operations < 0 or len(cert.operations) > max_operations:
            return False
        peak = max((abs(x).bit_length() for row in a for x in row), default=0)
        if max_entry_bits is not None and peak > max_entry_bits:
            return False
        for op in cert.operations:
            if not isinstance(op, (tuple, list)) or not op:
                return False
            name = op[0]
            arity = {'rs':3, 'cs':3, 'ra':4, 'ca':4, 'rn':2}.get(name)
            if arity != len(op) or any(type(x) is not int for x in op[1:]):
                return False
            i = op[1]
            size = m if name.startswith('r') else n
            if not 0 <= i < size:
                return False
            if name != 'rn':
                j = op[2]
                if not 0 <= j < size or i == j:
                    return False
            if name == 'rs':
                old = a[i][:]; a[i] = a[j][:]; a[j] = old
            elif name == 'cs':
                for row in a:
                    old = row[i]; row[i] = row[j]; row[j] = old
            elif name == 'ra':
                old = a[i][:]
                for c in range(n):
                    a[i][c] = old[c] + op[3]*a[j][c]
            elif name == 'ca':
                old = [a[r][i] for r in range(m)]
                for r in range(m):
                    a[r][i] = old[r] + op[3]*a[r][j]
            else:
                for c in range(n):
                    a[i][c] = -a[i][c]
            peak = max(peak, max((abs(x).bit_length() for row in a for x in row), default=0))
            if max_entry_bits is not None and peak > max_entry_bits:
                return False
        diagonal = cert.diagonal
        if len(diagonal) > min(m, n) or any(type(x) is not int or x <= 0 for x in diagonal):
            return False
        if any(b % a for a, b in zip(diagonal, diagonal[1:])):
            return False
        for r in range(m):
            for c in range(n):
                expected = diagonal[r] if r == c and r < len(diagonal) else 0
                if a[r][c] != expected:
                    return False
        return type(cert.peak_entry_bits) is int and cert.peak_entry_bits == peak
    except (TypeError, ValueError, IndexError, KeyError, AttributeError):
        return False


def torsion_blocks(diagonal: Sequence[int], binary_twos: int = 0) -> tuple[tuple[int, int], ...]:
    """Canonical invariant factors as (value, multiplicity) runs; no factoring.

    Merges an arbitrarily large binary multiplicity of Z/2 without expanding
    it. The supplied nonzero Smith diagonal must be positive and divisibility
    ordered; entries 1 are allowed and removed.
    """
    ds = tuple(diagonal)
    if type(binary_twos) is not int or binary_twos < 0:
        raise ValueError("invalid two-torsion multiplicity")
    if any(type(x) is not int or x <= 0 for x in ds) or any(b % a for a, b in zip(ds, ds[1:])):
        raise ValueError("invalid Smith diagonal")
    odd = []
    counts = {}
    for d in ds:
        e = (d & -d).bit_length() - 1
        u = d >> e
        if u > 1: odd.append(u)
        if e: counts[e] = counts.get(e, 0) + 1
    if binary_twos:
        counts[1] = counts.get(1, 0) + binary_twos
    total_two = sum(counts.values())
    total = max(total_two, len(odd))
    if not total:
        return ()
    powers = ([] if total_two == total else [(0, total-total_two)]) + sorted(counts.items())
    odds = ([] if len(odd) == total else [(1, total-len(odd))]) + [(u, 1) for u in odd]
    output = []
    i = j = 0
    e, a = powers[0]; u, b = odds[0]
    while True:
        count = min(a, b)
        value = (1 << e) * u
        if value > 1:
            if output and output[-1][0] == value:
                output[-1] = (value, output[-1][1] + count)
            else:
                output.append((value, count))
        a -= count; b -= count
        if a == 0:
            i += 1
            if i == len(powers): break
            e, a = powers[i]
        if b == 0:
            j += 1
            if j == len(odds): break
            u, b = odds[j]
    return tuple(output)


def rank_mod_two(matrix: Sequence[Sequence[int]], *, cols: int | None = None) -> int:
    a, n = _matrix(matrix, cols)
    basis = {}
    for row in a:
        word = sum((x & 1) << j for j, x in enumerate(row))
        while word:
            pivot = word.bit_length() - 1
            if pivot in basis:
                word ^= basis[pivot]
            else:
                basis[pivot] = word
                break
    return len(basis)
