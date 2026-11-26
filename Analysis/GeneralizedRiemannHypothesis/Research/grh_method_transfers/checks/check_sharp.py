"""Exhaustively check the odd-characteristic matching in small local rings.

The integer encoding a+p*v means a+epsilon*v in the split ring, and
the ordinary residue a+p*v in the mixed-characteristic ring Z/p^2.
Polynomials are tuples in increasing order of exponent.
"""
from itertools import product


class LocalRing:
    def __init__(self, p, split):
        self.p = p
        self.size = p*p
        if split:
            self.add = lambda a, b: ((a % p + b % p) % p
                                     + p*((a//p + b//p) % p))
            self.mul = lambda a, b: ((a*b) % p
                                     + p*((a % p * (b//p) + b % p * (a//p)) % p))
        else:
            self.add = lambda a, b: (a+b) % self.size
            self.mul = lambda a, b: (a*b) % self.size

    def neg(self, a):
        return next(b for b in range(self.size) if self.add(a, b) == 0)

    def padd(self, f, g):
        length = max(len(f), len(g))
        return trim([self.add(at(f, j), at(g, j)) for j in range(length)])

    def pmul(self, f, g):
        a = [0] * (len(f)+len(g)-1)
        for i, u in enumerate(f):
            for j, v in enumerate(g):
                a[i+j] = self.add(a[i+j], self.mul(u, v))
        return trim(a)

    def value(self, f, x):
        result = 0
        for coeff in reversed(f):
            result = self.add(self.mul(result, x), coeff)
        return result

    def divide_linear(self, f, beta):
        quotient = [0] * (len(f)-1)
        carry = f[-1]
        for j in range(len(f)-2, -1, -1):
            quotient[j] = carry
            carry = self.add(f[j], self.mul(beta, carry))
        return trim(quotient), carry


def at(f, j):
    return f[j] if j < len(f) else 0


def trim(f):
    i = len(f)
    while i and f[i-1] == 0:
        i -= 1
    return tuple(f[:i])


def residue(f, p):
    return trim([u % p for u in f])


def scalar_value(coefficients, gamma, p):
    return sum(a * gamma**j for j, a in enumerate(coefficients)) % p


def check(p, split, n, shift):
    R = LocalRing(p, split)
    points = [(x+p*shift) % R.size for x in range(p)]
    assert all(x % p == j for j, x in enumerate(points))
    powers = {}
    for beta in points:
        linear = (R.neg(beta), 1)
        powers[beta] = [(1,)]
        for _ in range(n):
            powers[beta].append(R.pmul(powers[beta][-1], linear))

    used = set()
    accepted = eligible = 0
    for low in product(range(R.size), repeat=n-1):
        a = residue(low, p)
        nonsingular = [j for j in range(p) if scalar_value(a, j, p)]
        if not nonsingular:
            continue
        eligible += p
        beta = points[nonsingular[0]]
        s = n + 1 - len(a)
        for top in range(p, R.size, p):
            f = (*low, top)
            c = p * ((-(top//p) * pow(2*a[-1], -1, p)) % p)
            assert c
            ratio = R.padd(powers[beta][1], R.pmul((c,), R.padd(powers[beta][s], (1,))))
            y = R.pmul(ratio, f)
            z = R.pmul(ratio, y)
            assert len(y) == n+1 and len(z) <= n+1
            assert y[n] == R.neg(R.mul(c, a[-1]))
            if len(z) != n+1:
                continue
            if any(R.value(f, t) == 0 for t in points if t != beta):
                continue
            Y = residue(y, p)
            candidates = []
            for point in points:
                reduced_quotient, rem = R.divide_linear(Y, point)
                A_candidate = residue(reduced_quotient, p)
                evaluation = scalar_value(A_candidate, point % p, p)
                if rem % p or not evaluation:
                    continue
                predicted = p * ((-(y[n]//p) * evaluation * pow(Y[-1], -1, p)) % p)
                if R.value(y, point) == predicted:
                    candidates.append(point)
            if len(candidates) != 1:
                assert beta in candidates
                continue
            assert candidates == [beta]
            assert all(R.value(y, t) for t in points)
            assert [t for t in points if R.value(z, t) == 0] == [beta]
            quotient, rem = R.divide_linear(z, beta)
            assert rem == 0
            assert R.value(quotient, beta) == R.mul(c, 2 * scalar_value(a, beta%p, p) % p)
            assert f not in used and y not in used and z not in used
            assert len({f, y, z}) == 3
            used.update([f, y, z])
            accepted += 1
    assert accepted > 0
    if n-1 >= p:
        # Uniformity in the rectangle modulo x^p-x.
        assert eligible * p**p == (R.size**(n-1)*p) * (p**p-1)
    return eligible, accepted


if __name__ == "__main__":
    for p, n in [(3, 4), (3, 5), (5, 3)]:
        for split in (False, True):
            for shift in (0, 1):
                raw, kept = check(p, split, n, shift)
                name = f"F_{p}[e]/(e^2)" if split else f"Z/{p*p}Z"
                print(f"{name}, n={n}, lift shift={shift}: {raw} eligible starts,"
                      f" {kept} disjoint triples", flush=True)
