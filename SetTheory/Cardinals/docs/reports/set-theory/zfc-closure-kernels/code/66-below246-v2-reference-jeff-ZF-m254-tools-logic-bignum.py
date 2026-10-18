"""Natural numbers that may be astronomically large, for simulating the program on real formula codes.

A value is a Python int (exact) while below LIMIT; above it, an N object carrying
  * residues modulo two large primes (fingerprint; equality is decided by the fingerprint),
  * the pair decomposition (a, b) when the value was built as P(a, b)  (needed by unpair).
The program never decomposes formula codes; it unpairs only the theorem stack and the command list,
whose values are built by P (or are small).  Equality of two N values is fingerprint equality
(false positive probability ~ 2^-120 per comparison).
"""
LIMIT = 1 << 512
PR = ((1 << 61) - 1, (1 << 89) - 1)

def tri(n):
    return n * (n + 1) // 2

def _fp_int(v):
    return tuple(v % p for p in PR)

class N:
    __slots__ = ('fp', 'pair', 'off')
    def __init__(self, fp, pair=None, off=0):
        self.fp = fp; self.pair = pair; self.off = off   # value = P(*pair) + off when pair is known
    def __repr__(self):
        return f'N<{self.fp[0] % 10**6}>'
    # arithmetic with ints / N
    def __add__(self, o):
        if isinstance(o, int):
            if o == 0:
                return self
            return N(tuple((x + o) % p for x, p in zip(self.fp, PR)), self.pair, self.off + o)
        return N(tuple((x + y) % p for x, y, p in zip(self.fp, o.fp, PR)))
    __radd__ = __add__
    def __sub__(self, o):
        assert isinstance(o, int)
        return self + (-o)
    def __mul__(self, k):
        assert isinstance(k, int)
        return N(tuple((x * k) % p for x, p in zip(self.fp, PR)))
    __rmul__ = __mul__
    def __eq__(self, o):
        if not isinstance(o, (int, N)):
            return NotImplemented
        return fp(self) == fp(o)
    def __ne__(self, o):
        return not self.__eq__(o)
    def __hash__(self):
        return hash(self.fp)
    def __gt__(self, o):
        assert isinstance(o, int) and o < LIMIT
        return True
    def __bool__(self):
        return True
    def bit_length(self):
        return 10**9

def fp(v):
    return v.fp if isinstance(v, N) else _fp_int(v)

def norm(v):
    if isinstance(v, int) and v >= LIMIT:
        return N(_fp_int(v))
    return v

def P(a, b):
    """dual Cantor pairing tri(a+b) + b."""
    if isinstance(a, int) and isinstance(b, int):
        v = tri(a + b) + b
        if v < LIMIT:
            return v
    fa, fb = fp(a), fp(b)
    out = []
    for x, y, p in zip(fa, fb, PR):
        s = (x + y) % p
        out.append((s * (s + 1) * pow(2, -1, p) + y) % p)
    return N(tuple(out), (a, b))

def unP(z):
    if isinstance(z, int):
        import math
        s = (math.isqrt(8 * z + 1) - 1) // 2
        b = z - tri(s)
        return s - b, b
    assert z.pair is not None and z.off == 0, 'unpair of a large value without known decomposition'
    return z.pair

def add(a, b):
    v = a + b
    return norm(v) if isinstance(v, int) else v
