"""Exact inherited arithmetic helpers from ProveIt package31.

Original package offered under MIT-0; see ../licenses/package31-LICENSE.
Source commit 22e75dd6b87b1b199bb08c778d7cf075ae5aae08,
31-sun10/signed10/build_signed10.py. Functions unchanged.
"""
def geometric_pair(d, base, n):
    """Return (base^n, sum(base^i, 0<=i<n)) without division."""
    assert n >= 0
    if n == 0:
        return d.const(1), d.const(0)
    if n == 1:
        return base, d.const(1)
    power, total = geometric_pair(d, base, n // 2)
    power2 = d.times(power, power)
    total2 = d.times(total, d.plus(d.const(1), power))
    if n % 2:
        return d.times(power2, base), d.plus(total2, power2)
    return power2, total2


def quadratic_norm(d, X, radicands):
    """Product over all signs of X + sum(sign_i sqrt(radicand_i)).

    Operate in a free rank-2^k algebra with formal r_i^2=radicand_i.
    At each step write an element A+r_i B and replace it by A^2-a_i B^2.
    Exactly k steps leave a scalar. No radicals occur in the emitted circuit.
    """
    count = len(radicands)
    if count == 3:
        # Collected form of the three quadratic norms (35 expanded terms).
        # The verifier proves this identity against all eight signed factors.
        a0, a1, a2 = radicands
        x2 = d.times(X, X)
        v = d.minus(d.minus(d.plus(x2, a2), a0), a1)
        v2 = d.times(v, v)
        four_xa = d.times(d.const(4), x2, a2)
        w = d.minus(d.plus(v2, four_xa), d.times(d.const(4), a0, a1))
        return d.minus(d.times(w, w), d.times(d.const(4), v2, four_xa))
    def ring_square(a):
        result = {}
        items = sorted(a.items())
        for ii, (mask, value) in enumerate(items):
            for jj in range(ii, len(items)):
                mask2, value2 = items[jj]
                term = d.times(value, value2)
                overlap = mask & mask2
                for k in range(count):
                    if overlap & (1 << k):
                        term = d.times(term, radicands[k])
                if ii != jj:
                    term = d.times(d.const(2), term)
                key = mask ^ mask2
                result[key] = d.plus(result.get(key, d.const(0)), term)
        return result

    element = {0: X, **{1 << i: d.const(1) for i in range(count)}}
    for i, radicand in enumerate(radicands):
        bit = 1 << i
        a = {mask: value for mask, value in element.items() if not mask & bit}
        b = {mask ^ bit: value for mask, value in element.items() if mask & bit}
        aa, bb = ring_square(a), ring_square(b)
        element = {}
        for mask in sorted(aa.keys() | bb.keys()):
            value = d.minus(aa.get(mask, d.const(0)),
                            d.times(radicand, bb.get(mask, d.const(0))))
            if d.known.get(value) != 0:
                element[mask] = value
    assert set(element) == {0}
    return element[0]

