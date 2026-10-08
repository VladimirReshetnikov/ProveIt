"""Exact, binary-encoded interval-pairing orbit counts.

This is an independent implementation of the Agol--Hass--Thurston (AHT)
algorithm, not a new orbit-counting algorithm.  No integer point of a paired
interval is expanded.  The default periodic merger uses the sharp
Fine--Wilf overlap threshold p + q - gcd(p, q); ``periodic_rule='aht'`` uses
the original sufficient threshold p + q for controlled comparisons.

All intervals are inclusive and zero based.  Order reversal of an interval
is distinct from an orientation character attached to a gluing.  The signed
wrapper constructs the two-sheeted parity cover explicitly as 2*k *interval
pairings*, not as 2*n points.

The unlimited kernel has the classical polynomial bound in k and log(n+1).
``max_cycles`` limits begun AHT cycles, not bit operations or elapsed time.
An interrupted run returns no count.  It never turns an unfinished topology
calculation into a negative certificate.  No weighted component extraction,
ambient-manifold recognition, or hierarchy construction is implemented here.

References:
  I. Agol, J. Hass, W. Thurston, The computational complexity of knot genus
  and spanning area, Trans. AMS 358 (2006), 3821--3850, Section 4.
  N. J. Fine, H. S. Wilf, Uniqueness theorems for periodic functions,
  Proc. AMS 16 (1965), 109--114.
"""

from dataclasses import dataclass
from math import gcd
from typing import Iterable


def _integer(value, label, minimum=0):
    if type(value) is not int or value < minimum:
        raise ValueError(f'{label} must be an integer >= {minimum}')
    return value


@dataclass(frozen=True, slots=True)
class IntervalPairing:
    """An isometry [a,b] -> [c,d], identifying the same pairs as its inverse.

    Domain and range are put in left-to-right order.  ``reverse`` specifies
    x -> a+d-x; otherwise the pairing is x -> x+c-a.  Equal intervals and
    identity pairings are allowed.  Empty intervals are not.
    """

    a: int
    b: int
    c: int
    d: int
    reverse: bool = False

    def __post_init__(self):
        for name in ('a', 'b', 'c', 'd'):
            _integer(getattr(self, name), name)
        if type(self.reverse) is not bool:
            raise ValueError('reverse must be bool')
        if self.a > self.b or self.c > self.d:
            raise ValueError('pairing intervals must be nonempty')
        if self.b - self.a != self.d - self.c:
            raise ValueError('pairing intervals must have equal width')
        if self.a > self.c:
            a, b, c, d = self.c, self.d, self.a, self.b
            for name, value in zip(('a', 'b', 'c', 'd'), (a, b, c, d)):
                object.__setattr__(self, name, value)

    @property
    def width(self):
        return self.b - self.a + 1

    @property
    def identity(self):
        return self.a == self.c and (not self.reverse or self.width == 1)

    @property
    def periodic(self):
        return not self.reverse and self.a < self.c <= self.b + 1

    @property
    def period(self):
        if not self.periodic:
            raise ValueError('pairing is not periodic')
        return self.c - self.a

    def image(self, x):
        _integer(x, 'x')
        if not self.a <= x <= self.b:
            raise ValueError('point is outside the domain')
        return self.a + self.d - x if self.reverse else x + self.c - self.a


@dataclass(frozen=True, slots=True)
class OrbitResult:
    complete: bool
    orbits: int | None
    cycles: int
    stats: dict[str, int]
    certificate: dict | None = None


def _validate(n, pairings, max_cycles, periodic_rule):
    _integer(n, 'n')
    if max_cycles is not None:
        _integer(max_cycles, 'max_cycles')
    if periodic_rule not in ('fine_wilf', 'aht'):
        raise ValueError("periodic_rule must be 'fine_wilf' or 'aht'")
    pairs = list(pairings)
    for pair in pairs:
        if not isinstance(pair, IntervalPairing):
            raise ValueError('pairings must contain IntervalPairing values')
        if pair.d >= n:
            raise ValueError('a pairing endpoint is outside [0,n)')
    return pairs


def _trim(pair):
    """Discard duplicate reflection arrows and their fixed midpoint."""
    if not pair.reverse or pair.b < pair.c:
        return pair
    centre_twice = pair.a + pair.d
    return IntervalPairing(pair.a, (centre_twice - 1) // 2,
                           centre_twice // 2 + 1, pair.d, True)


def _contract(n, pairs):
    """Remove all uncovered intervals in one order-preserving coordinate map."""
    intervals = sorted((lo, hi) for p in pairs
                       for lo, hi in ((p.a, p.b), (p.c, p.d)))
    occupied = []
    for lo, hi in intervals:
        if occupied and lo <= occupied[-1][1] + 1:
            occupied[-1] = (occupied[-1][0], max(hi, occupied[-1][1]))
        else:
            occupied.append((lo, hi))
    endpoints = sorted({v for p in pairs for v in (p.a, p.b, p.c, p.d)})
    new_endpoints = {}
    cursor = block = 0
    for lo, hi in occupied:
        while cursor < len(endpoints) and endpoints[cursor] <= hi:
            old = endpoints[cursor]
            new_endpoints[old] = block + old - lo
            cursor += 1
        block += hi - lo + 1
    mapped = [IntervalPairing(*(new_endpoints[v] for v in (p.a, p.b, p.c, p.d)),
                              p.reverse) for p in pairs]
    return block, mapped, n - block


def periodic_merge(first, second, *, periodic_rule='fine_wilf'):
    """Return a justified periodic union, or None if this rule does not apply.

    For two periodic pairings the Fine--Wilf criterion is exact: their
    generated relation on their union is the gcd-periodic relation iff the
    support overlap has at least p+q-gcd(p,q) points.  This statement concerns
    these two pairings alone; other generators can justify additional merges.
    """
    if periodic_rule not in ('fine_wilf', 'aht'):
        raise ValueError("periodic_rule must be 'fine_wilf' or 'aht'")
    if not first.periodic or not second.periodic:
        return None
    p, q = first.period, second.period
    common = gcd(p, q)
    overlap = min(first.d, second.d) - max(first.a, second.a) + 1
    threshold = p + q - (common if periodic_rule == 'fine_wilf' else 0)
    if overlap < threshold:
        return None
    lo, hi = min(first.a, second.a), max(first.d, second.d)
    return IntervalPairing(lo, hi - common, lo + common, hi)


def _transmit(pair, carrier):
    """Maximal power transmission, computed by division instead of iteration."""
    if not carrier.c <= pair.c <= pair.d <= carrier.d:
        return pair
    domain_moves = carrier.c <= pair.a <= pair.b <= carrier.d
    if carrier.reverse:
        total = carrier.a + carrier.d
        c, d = total - pair.d, total - pair.c
        if domain_moves:
            a, b = total - pair.b, total - pair.a
        else:
            a, b = pair.a, pair.b
        reverse = pair.reverse ^ True ^ domain_moves
    else:
        period = carrier.c - carrier.a
        r = (pair.c - carrier.c) // period + 1
        c, d = pair.c - r * period, pair.d - r * period
        if domain_moves:
            s = (pair.a - carrier.c) // period + 1
            a, b = pair.a - s * period, pair.b - s * period
        else:
            a, b = pair.a, pair.b
        reverse = pair.reverse
    return IntervalPairing(a, b, c, d, reverse)


def count_orbits(n: int, pairings: Iterable[IntervalPairing], *,
                 max_cycles: int | None = None,
                 periodic_rule: str = 'fine_wilf', check=None,
                 record_certificate: bool = False) -> OrbitResult:
    """Count components of an interval equivalence relation, without expansion.

    On budget exhaustion, ``complete`` is false and ``orbits`` is None.
    The input objects are never mutated.  ``stats`` counts structural events;
    in particular ``pair_tests`` counts candidate periodic-merger tests.
    An optional ``check()`` callback is called on entry, at each cycle, and
    during scans.  Its exceptions propagate, permitting cooperative deadlines
    or cancellation without disguising either as an ordinary resource result.
    Optional local-reduction certificates replay independently with
    interval_orbit_verify.verify_orbit_certificate. Version 2 admits the sharp
    merger; version 1 retains the classical threshold. Use integer_codec.json_safe
    when serializing binary integers beyond Python's decimal conversion limit.
    Incomplete runs never return a certificate or a partial orbit count.
    """
    checkpoint = check if check is not None else lambda: None
    checkpoint()
    if type(record_certificate) is not bool:
        raise ValueError('record_certificate must be bool')
    pairs = _validate(n, pairings, max_cycles, periodic_rule)
    initial_n, initial_k = n, len(pairs)
    initial_rows = [[p.a, p.b, p.c, p.d, -1 if p.reverse else 1]
                    for p in pairs] if record_certificate else None
    operations = [] if record_certificate else None
    stats = {'initial_pairings': initial_k, 'input_bits': n.bit_length(),
             'identity_deletions': 0, 'static_points': 0, 'contractions': 0,
             'trims': 0, 'mergers': 0, 'pair_tests': 0, 'transmissions': 0,
             'truncations': 0, 'truncated_points': 0}
    total = cycles = 0
    while n:
        checkpoint()
        if max_cycles is not None and cycles >= max_cycles:
            return OrbitResult(False, None, cycles, stats)
        cycles += 1
        if operations is not None:
            operations.extend({'op': 'delete', 'index': i}
                              for i in range(len(pairs) - 1, -1, -1)
                              if pairs[i].identity)
        retained = [p for p in pairs if not p.identity]
        stats['identity_deletions'] += len(pairs) - len(retained)
        pairs = retained
        if not pairs:
            if operations is not None:
                operations.append({'op': 'contract', 'gaps': [[0, n - 1]]})
            total += n
            stats['static_points'] += n
            stats['contractions'] += 1
            n = 0
            break
        if operations is not None:
            # Record the original gaps; replay computes them independently.
            gaps, end = [], 0
            for lo, hi in sorted((lo, hi) for p in pairs
                                 for lo, hi in ((p.a, p.b), (p.c, p.d))):
                checkpoint()
                if lo > end:
                    gaps.append([end, lo - 1])
                end = max(end, hi + 1)
            if end < n:
                gaps.append([end, n - 1])
            if gaps:
                operations.append({'op': 'contract', 'gaps': gaps})
        n, pairs, removed = _contract(n, pairs)
        total += removed
        if removed:
            stats['static_points'] += removed
            stats['contractions'] += 1
        for i, pair in enumerate(pairs):
            checkpoint()
            if pair.reverse and pair.b >= pair.c:
                if operations is not None:
                    operations.append({'op': 'trim', 'index': i})
                pairs[i] = _trim(pair)
                stats['trims'] += 1
        while True:
            found = False
            for i in range(len(pairs)):
                checkpoint()
                if not pairs[i].periodic:
                    continue
                for j in range(i + 1, len(pairs)):
                    checkpoint()
                    if not pairs[j].periodic:
                        continue
                    stats['pair_tests'] += 1
                    merged = periodic_merge(pairs[i], pairs[j],
                                            periodic_rule=periodic_rule)
                    if merged is not None:
                        if operations is not None:
                            operations.append({'op': 'merge', 'left': i, 'right': j})
                        pairs[i] = merged
                        pairs.pop(j)
                        stats['mergers'] += 1
                        found = True
                        break
                if found:
                    break
            if not found:
                break
        index = max(range(len(pairs)),
                    key=lambda i: (pairs[i].d, -pairs[i].c, -pairs[i].a,
                                   int(pairs[i].reverse)))
        carrier = pairs[index]
        for i, pair in enumerate(pairs):
            checkpoint()
            if i != index and carrier.c <= pair.c and pair.d <= carrier.d:
                if operations is not None:
                    domain_moves = carrier.c <= pair.a <= pair.b <= carrier.d
                    if carrier.reverse:
                        source_power, target_power = int(domain_moves), 1
                    else:
                        period = carrier.c - carrier.a
                        target_power = (pair.c - carrier.c) // period + 1
                        source_power = ((pair.a - carrier.c) // period + 1
                                        if domain_moves else 0)
                    operations.append({'op': 'transmit', 'transmitter': index,
                                       'target': i, 'source_power': source_power,
                                       'target_power': target_power})
                pairs[i] = _transmit(pair, carrier)
                stats['transmissions'] += 1
        # Canonical ranges contain each pairing's rightmost endpoint.  The
        # transmitted carriers' ranges all end below n-1, leaving this suffix
        # incident only to carrier.  The carrier's own domain may overlap it.
        cut = max([carrier.c] + [p.d + 1 for i, p in enumerate(pairs)
                                  if i != index])
        if not carrier.c <= cut < n or carrier.d != n - 1:
            raise AssertionError('AHT transmission did not expose a suffix')
        removed = n - cut
        if operations is not None:
            operations.append({'op': 'truncate', 'index': index, 'new_size': cut})
        if cut == carrier.c:
            pairs.pop(index)
        elif carrier.reverse:
            pairs[index] = IntervalPairing(carrier.a + removed, carrier.b,
                                            carrier.c, cut - 1, True)
        else:
            pairs[index] = IntervalPairing(carrier.a, carrier.b - removed,
                                            carrier.c, cut - 1)
        n = cut
        stats['truncations'] += 1
        stats['truncated_points'] += removed
    if stats['static_points'] + stats['truncated_points'] != initial_n:
        raise AssertionError('interval accounting failed')
    certificate = (dict(version=2 if periodic_rule == 'fine_wilf' else 1,
                        size=initial_n, pairings=initial_rows, orbit_count=total,
                        operations=operations) if record_certificate else None)
    return OrbitResult(True, total, cycles, stats, certificate)


@dataclass(frozen=True, slots=True)
class SignedPairing:
    pairing: IntervalPairing
    parity: int

    def __post_init__(self):
        if not isinstance(self.pairing, IntervalPairing):
            raise ValueError('pairing must be an IntervalPairing')
        if type(self.parity) is not int or self.parity not in (0, 1):
            raise ValueError('parity must be 0 or 1')


@dataclass(frozen=True, slots=True)
class SignedOrbitResult:
    complete: bool
    orbits: int | None
    consistent_components: int | None
    inconsistent_components: int | None
    base: OrbitResult
    cover: OrbitResult | None

    @property
    def cycles(self):
        return self.base.cycles + (self.cover.cycles if self.cover else 0)


def signed_cover(n: int, pairings: Iterable[SignedPairing]):
    """Encode (x,e) ~ (g(x), e+parity) with two blocks of n points."""
    _integer(n, 'n')
    result = []
    for signed in pairings:
        if not isinstance(signed, SignedPairing):
            raise ValueError('signed pairings must contain SignedPairing values')
        p = signed.pairing
        if p.d >= n:
            raise ValueError('a pairing endpoint is outside [0,n)')
        for sheet in (0, 1):
            source, target = sheet * n, (sheet ^ signed.parity) * n
            result.append(IntervalPairing(p.a + source, p.b + source,
                                          p.c + target, p.d + target, p.reverse))
    return result


def signed_orbit_counts(n: int, pairings: Iterable[SignedPairing], *,
                        max_cycles: int | None = None,
                        periodic_rule: str = 'fine_wilf', check=None) -> SignedOrbitResult:
    """Count components with/without a consistent binary orientation label.

    A component is consistent iff every closed walk has parity zero.  For
    surface gluings carrying the actual orientation character these are the
    orientable components.  The budget is SHARED by the base and cover runs.
    """
    signed = list(pairings)
    lifted = signed_cover(n, signed)
    base = count_orbits(n, (s.pairing for s in signed), max_cycles=max_cycles,
                        periodic_rule=periodic_rule, check=check)
    if not base.complete:
        return SignedOrbitResult(False, None, None, None, base, None)
    remaining = None if max_cycles is None else max_cycles - base.cycles
    cover = count_orbits(2 * n, lifted, max_cycles=remaining,
                         periodic_rule=periodic_rule, check=check)
    if not cover.complete:
        return SignedOrbitResult(False, None, None, None, base, cover)
    assert base.orbits is not None and cover.orbits is not None
    if not base.orbits <= cover.orbits <= 2 * base.orbits:
        raise AssertionError('binary cover component count is inconsistent')
    return SignedOrbitResult(True, base.orbits, cover.orbits - base.orbits,
                             2 * base.orbits - cover.orbits, base, cover)


def same_orbit(n: int, pairings: Iterable[IntervalPairing], x: int, y: int, *,
               max_cycles: int | None = None,
               periodic_rule: str = 'fine_wilf', check=None) -> bool | None:
    """Exact membership query by adjoining the single relation x~y.

    The two orbit counts share max_cycles.  None means unfinished.  This
    decision operation does not enumerate or extract an entire component.
    """
    if check is not None:
        check()
    pairs = _validate(n, pairings, max_cycles, periodic_rule)
    for point, label in ((x, 'x'), (y, 'y')):
        _integer(point, label)
        if point >= n:
            raise ValueError(f'{label} must lie in [0,n)')
    if x == y:
        return True
    base = count_orbits(n, pairs, max_cycles=max_cycles,
                        periodic_rule=periodic_rule, check=check)
    if not base.complete:
        return None
    remaining = None if max_cycles is None else max_cycles - base.cycles
    linked = count_orbits(n, pairs + [IntervalPairing(x, x, y, y)],
                          max_cycles=remaining, periodic_rule=periodic_rule,
                          check=check)
    if not linked.complete:
        return None
    return linked.orbits == base.orbits
