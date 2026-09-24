"""Exact decimal tetration residues and a valuation-based APS algorithm.

Python 3.9+; standard library only.  Zero-padded decimal convention:
k_b = v_10(T_(b+1)-T_b), V_1 = k_1, V_b = k_b-k_(b-1) (b>=2).
"""
from functools import lru_cache
from typing import Tuple


def vp(n: int, p: int) -> int:
    """p-adic valuation of a positive integer (p must be prime)."""
    if n <= 0 or p < 2:
        raise ValueError("vp requires n>0 and p>=2")
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


@lru_cache(maxsize=4096)
def split_smooth(m: int) -> Tuple[int, int]:
    if m < 1:
        raise ValueError("modulus must be positive")
    exponents = []
    for p in (2, 5):
        e = 0
        while m % p == 0:
            m //= p
            e += 1
        exponents.append(e)
    if m != 1:
        raise ValueError("modulus must have no prime factors other than 2 and 5")
    return tuple(exponents)


class Tower:
    """Compute T_h modulo 2^u 5^v without constructing a large tower."""
    def __init__(self, a: int):
        if a < 2:
            raise ValueError("base must be at least 2")
        self.a = a
        self._mod_cache = {}
        self._cap_cache = {}

    def capped(self, h: int, cap: int) -> int:
        """Return min(T_h, cap), with T_0=1. Integer arithmetic only."""
        if h < 0 or cap < 1:
            raise ValueError("height must be nonnegative, cap positive")
        key = (h, cap)
        if key in self._cap_cache:
            return self._cap_cache[key]
        if h == 0 or cap == 1:
            ans = 1
        else:
            threshold, power = 0, 1
            while power < cap:
                power *= self.a
                threshold += 1
            exponent = self.capped(h - 1, threshold)
            ans = cap if exponent >= threshold else self.a ** exponent
        self._cap_cache[key] = ans
        return ans

    def mod(self, h: int, m: int) -> int:
        """Return T_h mod m for a 2,5-smooth positive modulus."""
        if h < 0 or m < 1:
            raise ValueError("height must be nonnegative, modulus positive")
        key = (h, m)
        if key in self._mod_cache:
            return self._mod_cache[key]
        if m == 1:
            return 0
        if h == 0:
            return 1 % m
        e2, e5 = split_smooth(m)
        residues = []
        for p, e in ((2, e2), (5, e5)):
            if e == 0:
                continue
            q = p ** e
            if self.a % p == 0:
                threshold = (e + vp(self.a, p) - 1) // vp(self.a, p)
                exponent = self.capped(h - 1, threshold)
                residue = 0 if exponent >= threshold else pow(self.a, exponent, q)
            else:
                phi = (p - 1) * p ** (e - 1)
                exponent = self.mod(h - 1, phi)
                residue = pow(self.a, exponent, q)
            residues.append((residue, q))
        ans, modulus = residues[0]
        if len(residues) == 2:
            residue, q = residues[1]
            ans += modulus * (((residue - ans) * pow(modulus, -1, q)) % q)
        self._mod_cache[key] = ans
        return ans

    def decimal_phase(self, b: int, k: int) -> int:
        """Return -(T_(b+1)-T_b)/10^k mod 10, checking the supplied k."""
        if b < 1 or k < 0:
            raise ValueError("b must be positive and k nonnegative")
        tenk = 10 ** k
        m = tenk * 10
        residue = (self.mod(b, m) - self.mod(b + 1, m)) % m
        if residue % tenk or residue == 0:
            raise ArithmeticError("incorrect valuation supplied")
        return residue // tenk


class PhaseModel:
    """Exact valuation formulas, certified onset, and phase prediction."""
    def __init__(self, a: int):
        if a < 2 or a % 10 == 0:
            raise ValueError("base must be at least 2 and not divisible by 10")
        self.a = a
        self.tower = Tower(a)
        if a % 2:
            self.A = vp(a - 1, 2)
            self.t = max(self.A, vp(a + 1, 2))
        else:
            self.e = vp(a, 2)
        if a % 5:
            self.o = next(j for j in (1, 2, 4) if pow(a, j, 5) == 1)
            self.r = vp(a ** self.o - 1, 5)
            if a % 2:
                self.epsilon = 1 if self.o == 1 else (
                    -1 if self.o == 4 and a % 4 == 3 else 0)
            else:
                self.epsilon = 1 if self.o == 1 else (
                    -2 if self.o == 4 and a % 4 == 2 else -1)
        else:
            self.f = vp(a, 5)
        self.speed = (min(self.t, self.r) if a % 2 and a % 5 else
                      self.t if a % 5 == 0 else self.r)

    def valuations_capped(self, b: int) -> Tuple[int, int]:
        """Return local valuations, capping a huge nonunit one at other+1.

        The returned pair preserves the minimum and all <,=,> comparisons.
        """
        if b < 1:
            raise ValueError("height must be positive")
        a = self.a
        if a % 2 and a % 5:
            return self.A + b * self.t, (b + self.epsilon) * self.r
        if a % 2 == 0:
            y = max(0, (b + self.epsilon) * self.r)
            cap = y // self.e + 1
            x = self.e * self.tower.capped(b - 1, cap)
            return x, y
        x = self.A + b * self.t
        cap = x // self.f + 1
        y = self.f * self.tower.capped(b - 1, cap)
        return x, y

    def k(self, b: int) -> int:
        """Number of stable digits; the artificial value k(0)=0 sets V_1."""
        return 0 if b == 0 else min(self.valuations_capped(b))

    def onset(self) -> int:
        """Exact minimal b from which V_b is constant, not a sampled guess."""
        a = self.a
        if a % 2 == 0:
            if self.o == 1:
                return 2 if self.k(1) == 2 * self.r else 3
            return 3 if self.epsilon == -2 else 2
        if a % 5 == 0:
            if a == 5:
                return 4
            return 2 if self.k(1) == self.A + self.t else 3
        t, r, A, eps = self.t, self.r, self.A, self.epsilon
        if t == r:
            return 1 if self.k(1) == t else 2
        # Let delta_b be the larger-slope line minus the smaller-slope line.
        if t > r:
            intercept, slope = A - eps * r, t - r
        else:
            intercept, slope = eps * r - A, r - t
        if self.k(1) == self.speed and intercept + slope >= 0:
            return 1
        # V_b is the limiting slope exactly when delta_(b-1) >= 0 (b>=2).
        ceil_crossing = (-intercept + slope - 1) // slope
        return max(2, ceil_crossing + 1)

    def phase_word(self) -> Tuple[int, ...]:
        """The first four exact phases at onset, reduced to period 1,2,4."""
        B = self.onset()
        word = tuple(self.tower.decimal_phase(b, self.k(b)) for b in range(B, B + 4))
        return reduce_word(word)

    def predicted_word(self) -> Tuple[int, ...]:
        """Independent structure calculation: one exact phase plus a multiplier."""
        B = self.onset()
        x, y = self.valuations_capped(B)
        if x < y:
            return (5,)
        if x == y:
            v = self.t
            c = ((self.a - 1) // (10 ** v)) % 10
            return reduce_word(tuple((-pow(c, b + 1, 10)) % 10 for b in range(B, B + 4)))
        first = self.tower.decimal_phase(B, self.k(B))
        # L = a^(T_B) * (a^o-1)/(o*5^r) * 2^(-r) in F_5.
        u = ((self.a ** self.o - 1) // (5 ** self.r)) % 5
        L = (pow(self.a, self.tower.mod(B, 4), 5) * u *
             pow(self.o, -1, 5) * pow(pow(2, self.r, 5), -1, 5)) % 5
        def even_lift(z: int) -> int:
            return z if z % 2 == 0 else z + 5
        return reduce_word(tuple(even_lift((first * pow(L, j, 5)) % 5) for j in range(4)))


def reduce_word(word: Tuple[int, ...]) -> Tuple[int, ...]:
    if len(word) != 4:
        raise ValueError("expected four phases")
    if word[:2] == word[2:]:
        return word[:1] if word[0] == word[1] else word[:2]
    return word


def word_number(word: Tuple[int, ...]) -> int:
    return int(''.join(str(x) for x in word))


def modular_word(a: int) -> Tuple[int, ...]:
    """The A376446 convention: start at nu(a)+2 instead of minimal onset."""
    model = PhaseModel(a)
    H = (model.t if a % 5 == 0 else model.r) + 2
    return reduce_word(tuple(model.tower.decimal_phase(b, model.k(b)) for b in range(H, H+4)))


def sharp_onset_base(r: int) -> int:
    """A CRT base with v5(a^2+1)=r and minimal onset r+2 (r>=3)."""
    if r < 3:
        raise ValueError("r must be at least 3")
    m2, m5 = 2 ** r, 5 ** (r + 1)
    z2 = 2 ** (r - 1) - 1
    z5 = pow(2, 5 ** (r - 1), m5)
    return z2 + m2 * (((z5 - z2) * pow(m2, -1, m5)) % m5)



if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('base', type=int)
    parser.add_argument('--terms', type=int, default=8)
    args = parser.parse_args()
    model = PhaseModel(args.base)
    print(f'base={args.base}; limiting speed={model.speed}; onset={model.onset()}')
    print('APS=' + str(word_number(model.phase_word())))
    for b in range(1, max(args.terms, model.onset() + 4) + 1):
        k = model.k(b)
        print(f'b={b}: k_b={k}, V_b={k-model.k(b-1)}, s_b={model.tower.decimal_phase(b,k)}')
