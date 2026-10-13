"""Independent, source-bound replay of primitive positive extreme rays.

The only witness is its original coordinate vector.  Preparation snapshots the
source and builds a right-pivot kernel chart without producer imports.  Cached
support ranks never replace membership, primitivity, or query checks.  This is
an algebraic certificate checker, not a geometric unknot certificate checker.
"""

from collections import OrderedDict
from collections.abc import Mapping, Set
from dataclasses import dataclass, field
from fractions import Fraction
from math import gcd


def _items(values):
    if isinstance(values, (str, bytes, bytearray, Mapping, Set)):
        raise ValueError('ordered coordinate iterable required')
    return iter(values)


def _zero_indices(values):
    # Unlike coordinate vectors, a coordinate-zero face has no ordering.
    if isinstance(values, (str, bytes, bytearray, Mapping)):
        raise ValueError('coordinate-zero index iterable required')
    return iter(values)


def _q(value):
    if isinstance(value, (bool, float)) or not isinstance(value, (int, str, Fraction)):
        raise ValueError('exact rational input required')
    try:
        return Fraction(value)
    except (ZeroDivisionError, OverflowError) as exc:
        raise ValueError('invalid exact rational') from exc


def _echelon(rows, width, check, stop=None):
    """Rightmost pivots; earlier rows need no backwards elimination."""
    pivots = {}
    if stop == 0:
        return pivots
    for row in rows:
        check()
        a = list(row)
        if len(a) != width:
            raise ValueError('equation width mismatch')
        for j in range(width-1, -1, -1):
            check()
            if not a[j]:
                continue
            if j in pivots:
                scale = a[j]
                old = pivots[j]
                a = [v-scale*w for v, w in zip(a, old)]
            else:
                scale = a[j]
                pivots[j] = tuple(v/scale for v in a)
                break
        if stop is not None and len(pivots) >= stop:
            break
    return pivots


def _chart(rows, width, check):
    pivots = _echelon(rows, width, check)
    free = tuple(j for j in range(width) if j not in pivots)
    basis = []
    for j in free:
        check()
        vector = [Fraction(0)]*width
        vector[j] = Fraction(1)
        for p in sorted(pivots):
            check()
            row = pivots[p]
            vector[p] = -sum((row[k]*vector[k] for k in range(p)), Fraction(0))
        basis.append(tuple(vector))
    return free, tuple(basis)


class _Cancellation:
    def __init__(self, callback):
        self.callback = callback
        self.failed = False

    def __call__(self):
        try:
            self.callback()
        except BaseException:
            self.failed = True
            raise


@dataclass(frozen=True, init=False)
class SourceKernelVerifier:
    """Prepare one immutable source; verify query-dependent positive rays.

    ``source`` supplies ``n``, ``equations`` and ``conflicts``.  A zero cache
    size disables rank caching.  Cancellation exceptions propagate unchanged,
    including those normally used to reject malformed witness data.
    """

    n: int
    equations: tuple
    conflicts: tuple
    free: tuple
    basis: tuple
    cache_size: int
    _support_cache: OrderedDict = field(repr=False, compare=False)

    def __init__(self, source, *, check=lambda: None, cache_size=256):
        check()
        if type(cache_size) is not int or cache_size < 0:
            raise ValueError('cache_size must be a nonnegative integer')
        try:
            n, equations, conflicts = source.n, source.equations, source.conflicts
        except AttributeError as exc:
            raise ValueError('source must supply n, equations and conflicts') from exc
        if type(n) is not int or n < 1:
            raise ValueError('positive integer source dimension required')
        rows = []
        for row in _items(equations):
            check()
            values = tuple(_q(v) for v in _items(row))
            if len(values) != n:
                raise ValueError('equation width mismatch')
            rows.append(values)
        pairs = set()
        for pair in _items(conflicts):
            check()
            pair = tuple(_items(pair))
            if (len(pair) != 2 or any(type(j) is not int or not 0 <= j < n for j in pair)
                    or pair[0] == pair[1]):
                raise ValueError('invalid coordinate conflict')
            pairs.add(tuple(sorted(pair)))
        rows = tuple(rows)
        free, basis = _chart(rows, n, check)
        for name, value in (('n', n), ('equations', rows), ('conflicts', tuple(sorted(pairs))),
                            ('free', free), ('basis', basis), ('cache_size', cache_size),
                            ('_support_cache', OrderedDict())):
            object.__setattr__(self, name, value)

    @property
    def nullity(self):
        return len(self.basis)

    def verify(self, coordinates, objective, *, zeros=(), check=lambda: None):
        """Return False for malformed or incorrect rays; propagate cancellation."""
        cancel = _Cancellation(check)
        cancel()
        try:
            x = tuple(_q(v) for v in _items(coordinates))
            c = tuple(_q(v) for v in _items(objective))
            if (len(x) != self.n or len(c) != self.n or not any(x)
                    or any(v < 0 or v.denominator != 1 for v in x)):
                return False
            divisor = 0
            for value in x:
                cancel()
                divisor = gcd(divisor, int(value))
            if divisor != 1:
                return False
            for j in _zero_indices(zeros):
                cancel()
                if type(j) is not int or not 0 <= j < self.n or x[j]:
                    return False
            for a, b in self.conflicts:
                cancel()
                if x[a] and x[b]:
                    return False
            if sum((a*b for a, b in zip(c, x)), Fraction(0)) <= 0:
                return False
            # Our chart is the identity on its own free source coordinates.
            # Reconstruction authenticates membership independently of the
            # producer's chart, trace, and any previously cached support.
            coefficients = tuple(x[j] for j in self.free)
            for j, value in enumerate(x):
                cancel()
                if sum((a*row[j] for a, row in zip(coefficients, self.basis)), Fraction(0)) != value:
                    return False
            zero = tuple(j for j, value in enumerate(x) if not value)
            if zero in self._support_cache:
                cancel()
                result = self._support_cache[zero]
                self._support_cache.move_to_end(zero)
                return result
            # A nonzero matching vector proves this rank is at most h-1.
            # Therefore h-1 independent zero forms suffice, without a trace.
            target = self.nullity-1
            if target < 0:
                return False
            forms = (tuple(row[j] for row in self.basis) for j in zero)
            result = len(_echelon(forms, self.nullity, cancel, stop=target)) == target
            if self.cache_size:
                self._support_cache[zero] = result
                if len(self._support_cache) > self.cache_size:
                    self._support_cache.popitem(last=False)
            return result
        except (ValueError, TypeError, IndexError, ZeroDivisionError, OverflowError, AttributeError):
            if cancel.failed:
                raise
            return False
