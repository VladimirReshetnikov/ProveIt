"""Finite relational witness checker; exact integers only.
Demonstration, not an iPRA proof and not a general PR interpreter.
"""
from functools import lru_cache
from fractions import Fraction


def find_chain(width, good, edge, horizon):
    @lru_cache(None)
    def viable(i, a):
        return bool(good(i, a)) and (i == horizon or any(
            edge(i, a, b) and viable(i + 1, b)
            for b in range(width(i + 1))))
    starts = [a for a in range(width(0)) if viable(0, a)]
    if not starts:
        return None
    out = [starts[0]]
    for i in range(horizon):
        bs = [b for b in range(width(i + 1))
              if edge(i, out[-1], b) and viable(i + 1, b)]
        assert bs
        out.append(bs[0])
    assert all(good(i, a) for i, a in enumerate(out))
    assert all(edge(i, out[i], out[i+1]) for i in range(horizon))
    return out


def sqrt_instance(a, initial_precision=1):
    assert isinstance(a, Fraction) and a >= 0
    def scale(i):
        return 2**(initial_precision+i)
    def width(i):
        s = scale(i)
        # j/s <= a+1; include one extra element
        return (a.numerator * s // a.denominator) + s + 2
    def good(i, j):
        s = scale(i)
        q = Fraction(j, s)
        return abs(q*q-a) <= (2*a+3)/s
    def edge(i, j, k):
        q = Fraction(j, scale(i))
        r = Fraction(k, scale(i+1))
        return abs(q-r) <= Fraction(3, scale(i))
    return width, good, edge


def test():
    vals = [Fraction(0),Fraction(1,100),Fraction(2,3),Fraction(2),Fraction(9,4)]
    for a in vals:
        w,g,e = sqrt_instance(a)
        chain=find_chain(w,g,e,5)
        assert chain is not None, a
        print(f'a={a}, compatible numerators={chain}')
    w=lambda i: 2
    g=lambda i,a: (i==0 or a==1)
    e=lambda i,a,b: b==0
    assert find_chain(w,g,e,3) is None
    print('unsatisfiable constraint instance correctly rejected')

if __name__=='__main__': test()
