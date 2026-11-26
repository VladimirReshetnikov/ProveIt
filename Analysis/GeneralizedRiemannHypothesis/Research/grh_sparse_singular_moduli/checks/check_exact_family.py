"""Check factorial cutoffs for the first four examples without listing their roots."""
from itertools import count


def weight(n):
    quotient = n
    result = n
    while quotient:
        quotient //= 7
        result -= quotient
    return result


def check(m):
    M = 7**m
    exponent = 3*7**(m-1)-2
    h = 2**exponent
    assert 4*h % M == 1
    # For i<h, w(i) <= 5i/6 + digits_7(h). For n>=h, w(n)>=5n/6.
    digits = next(d for d in count(1) if 7**d > h)
    radius = 2*digits+3
    w = weight(h)
    assert all(weight(i) < w for i in range(max(0, h-radius), h))
    assert all(weight(i) > w for i in range(h+1, h+radius+1))
    if h > radius:
        assert 5*(h-radius)+6*digits < 6*w
    assert 5*(h+radius) > 6*w
    print(f"m={m}, discriminant=-2^{6*7**(m-1)}, h=2^{exponent}, minimum=2^{exponent}+1")


if __name__ == "__main__":
    assert 5**6 < 7**5 and 2**18 < 7**7
    for index in range(1, 5):
        check(index)
