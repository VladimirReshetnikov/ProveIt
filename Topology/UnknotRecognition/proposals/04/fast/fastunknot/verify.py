"""Replay mathematical evidence. Khovanov evidence requires recomputation.

This checks combinatorial certificates and invariant computations. It is not a
Lean formalization and does not eliminate the trust in the implemented TQFT.
"""
from __future__ import annotations

from time import monotonic
from math import isfinite
from .diagram import Diagram
from .simplify import Move, apply_move
from .factor import verify_decomposition
from .jones import verify_obstruction
from .alexander import alexander_polynomial
from .scan import ScanLimit, khovanov_rank


def verify_result(diagram: Diagram, result: dict, *, seconds: float | None = None) -> bool:
    if seconds is not None and (not isfinite(seconds) or seconds < 0):
        raise ValueError("seconds must be finite and nonnegative")
    deadline = None if seconds is None else monotonic() + seconds

    def remaining():
        if deadline is None:
            return None
        budget = deadline - monotonic()
        if budget <= 0:
            raise ScanLimit('verification time budget exhausted')
        return budget

    def verify(current: Diagram, record: dict) -> bool:
        remaining()
        evidence = record['evidence']
        status, method = record['status'], record['method']
        if status not in ('UNKNOT', 'KNOTTED'):
            return False
        if record['input_crossings'] != current.crossings:
            return False
        for item in evidence.get('reidemeister_trace', []):
            current = apply_move(current, Move(item['kind'], tuple(item['crossings'])))
            remaining()
        if record['reduced_crossings'] != current.crossings:
            return False
        if method == 'reidemeister-reduction':
            return status == 'UNKNOT' and current.crossings == 0
        if method == 'descending-diagram':
            dart = evidence['descending_start_dart']
            if type(dart) is not int or not 0 <= dart < 4 * current.crossings:
                return False
            alpha, seen = current.alpha(), set()
            for _ in range(2 * current.crossings):
                if dart // 4 not in seen:
                    if dart % 2 == 0:
                        return False
                    seen.add(dart // 4)
                dart = alpha[4 * (dart // 4) + (dart + 2) % 4]
            return status == 'UNKNOT' and len(seen) == current.crossings
        if method == 'jones-modular-frontier':
            return status == 'KNOTTED' and verify_obstruction(
                current, evidence['jones'], seconds=remaining())
        if method == 'alexander-polynomial':
            p = alexander_polynomial(current, deadline=deadline)
            return status == 'KNOTTED' and p != [1] and p == evidence['alexander_coefficients']
        if method == 'connected-sum':
            factors = verify_decomposition(current, evidence['decomposition'])
            checked = set()
            positive = False
            for item in evidence['factor_results']:
                index, child = item['factor_index'], item['result']
                if type(index) is not int or not 0 <= index < len(factors) or index in checked:
                    return False
                checked.add(index)
                if not verify(factors[index], child):
                    return False
                if child['status'] == 'KNOTTED':
                    positive = True
            return ((status == 'KNOTTED' and positive)
                    or (status == 'UNKNOT' and not positive and len(checked) == len(factors)))
        if method == 'reduced-khovanov-F2-scan':
            expected = evidence['khovanov']
            kh = khovanov_rank(current.pd, order=expected['scan_order'],
                               seconds=remaining(), check_d_squared=True)
            return (expected['reduced_rank'] == kh['reduced_rank']
                    and expected['unreduced_rank'] == kh['rank']
                    and status == ('UNKNOT' if kh['reduced_rank'] == 1 else 'KNOTTED'))
        return False

    try:
        return verify(diagram, result)
    except (KeyError, TypeError, ValueError, IndexError, ArithmeticError):
        return False
