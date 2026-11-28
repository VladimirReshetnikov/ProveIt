"""Exact finite multiplicities and approximate limiting slopes (Python 3)."""
from fractions import Fraction
from math import ceil, log


def multiply(left, right):
    result = [0] * (len(left) + len(right) - 1)
    for i, x in enumerate(left):
        for j, y in enumerate(right):
            result[i + j] += x * y
    return result


def finite_thresholds(c, orders):
    poly = [1]
    quadratic = [c.denominator, -2 * c.numerator, c.denominator]
    thresholds = []
    for m in range(1, max(orders) + 1):
        poly = multiply(poly, quadratic)
        if m not in orders:
            continue
        smoothed, r = poly, 0
        while min(smoothed) < 0:
            smoothed = [a + b for a, b in zip(smoothed + [0], [0] + smoothed)]
            r += 1
        thresholds.append(r)
        if c <= Fraction(1, 2):
            assert r == ceil(2 * c * m)
        if m == 1:
            assert r == 2 * ceil(1 / (1-c)) - 3
    return thresholds


def limiting_slope(c):
    if c <= 0.5:
        return 2 * c

    def log_g(a):
        return log((1+c)/((a+1)*(1-c))) + a*log(a*(1+c)/(2*(a+1)))

    low, high = c, 2.0
    while log_g(high) > 0:
        high *= 2
    for _ in range(80):
        mid = (low + high) / 2
        if log_g(mid) > 0:
            low = mid
        else:
            high = mid
    return low + high


if __name__ == "__main__":
    orders = (1, 2, 5, 10, 20)
    print(r"\begin{tabular}{rrrrrrr}\toprule")
    print(r"$c$ & $m=1$ & $m=2$ & $m=5$ & $m=10$ & $m=20$ & $\tau(c)$ \\\midrule")
    for c in map(Fraction, ("1/4", "1/2", "3/5", "3/4", "9/10")):
        values = list(map(str, finite_thresholds(c, orders)))
        print(" & ".join([str(c)] + values + [f"{limiting_slope(float(c)):.4f}"]) + r" \\")
    print(r"\bottomrule\end{tabular}")
