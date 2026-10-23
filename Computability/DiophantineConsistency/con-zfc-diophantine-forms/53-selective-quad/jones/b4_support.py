"""Shared sparse evaluation adapted from the companion Sun B4 implementation."""
from functools import lru_cache
def coding_blocks_b4(d, base, keys, weights):
    """Sparse homogeneous Horner form of sum c_alpha B^(4t-alpha.w).

    The dummy alpha_0 is absent from P and is removed rather than coded.
    Four-sum-distinct weights guarantee coefficient extraction; they do not
    need base-five spacing. Every exponent is a fixed nonnegative integer.
    """
    A,M,P,c=d.plus,d.times,d.power,d.const
    t=max(weights)
    # Shared fixed-window exponentiation is substantially smaller than 63
    # independent binary chains for the irregular B4 positions.
    @lru_cache(None)
    def chunk(position,digit):
        if digit==0:return c(1)
        if digit==1:
            return base if position==0 else P(chunk(position-1,1),16)
        return M(chunk(position,digit-1),chunk(position,1))
    @lru_cache(None)
    def bp(n):
        factors=[];position=0
        while n:
            if n%16:factors.append(chunk(position,n%16))
            n//=16;position+=1
        return M(*factors)
    v=[bp(t)]+[bp(t-w) for w in weights]
    terms=[]
    for alpha,name in keys:
        if alpha[0]!=0:raise ValueError("unexpected padded coordinate")
        ex=(4-sum(alpha),)+tuple(alpha[1:])
        terms.append((ex,c(name) if isinstance(name,int) else d.fixed(name)))
    @lru_cache(None)
    def horner(ts):
        if not ts:return c(0)
        counts=[sum(ex[j]>0 for ex,co in ts) for j in range(len(v))]
        if not max(counts):return A(*(co for ex,co in ts))
        j=max(range(len(v)),key=lambda j:(counts[j],sum(ex[j] for ex,co in ts),j))
        yes=[];no=[]
        for ex,co in ts:
            if ex[j]:
                ee=list(ex);ee[j]-=1;yes.append((tuple(ee),co))
            else:no.append((ex,co))
        return A(horner(tuple(no)),M(v[j],horner(tuple(yes))))
    return bp(4*t), A(*(bp(w) for w in weights)),horner(tuple(terms)),v[0]


def geometric_pair(d, base, n):
    """Return (base^n, sum(base^i, 0<=i<n)) without division."""
    if n < 0:raise ValueError("negative geometric length")
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
    if set(element) != {0}:raise ValueError("non-scalar norm")
    return element[0]

