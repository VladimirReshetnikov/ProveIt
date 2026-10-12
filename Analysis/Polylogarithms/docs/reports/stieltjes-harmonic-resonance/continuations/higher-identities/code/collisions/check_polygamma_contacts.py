"""Independent diagnostic for the all-rank zero-Stieltjes contact formula.

No fitted asymptotic coefficients are used: K is calculated by local rational
partial fractions, and the original positive-shift integral by quadrature.
"""
from itertools import combinations
from math import factorial, comb
import json
import mpmath as mp


def conv(a, b, degree):
    out = [mp.mpf(0)] * (degree + 1)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            if i + j <= degree:
                out[i + j] += ai * bj
    return out


def local_kernel(nodes, orders, degree):
    """FP at infinity of x^degree / prod(x+node)^order.

    This implementation uses the rational partial fraction formula and is
    intentionally independent of the Hermite divided difference recursion.
    All supplied nodes in the diagnostics are distinct.
    """
    result = mp.mpf(0)
    for i, (ai, hi) in enumerate(zip(nodes, orders)):
        top = hi - 1
        coeff = [mp.mpf(0)] * (top + 1)
        for v in range(min(degree, top) + 1):
            coeff[v] = comb(degree, v) * (-ai) ** (degree - v)
        for j, (aj, hj) in enumerate(zip(nodes, orders)):
            if j == i:
                continue
            diff = aj - ai
            factor = [(-1) ** k * mp.rf(hj, k) / factorial(k)
                      / diff ** (hj + k) for k in range(top + 1)]
            coeff = conv(coeff, factor, top)
        for q in range(1, hi + 1):
            ciq = coeff[hi - q]
            result += (-ciq * mp.log(ai) if q == 1 else
                       ciq * ai ** (1 - q) / (q - 1))
    return result


def regular(r, a, centered=False):
    return mp.polygamma(r, 1 + a) + (mp.euler if centered and r == 0 else 0)


def contact(shifts, derivatives, centered=False):
    n = len(shifts)
    result = mp.mpf(0)
    for size in range(1, n + 1):
        for subset_tuple in combinations(range(n), size):
            subset = set(subset_tuple)
            H = sum(derivatives[i] + 1 for i in subset)
            coeff = [mp.mpf(1)] + [mp.mpf(0)] * (H - 1)
            for j in range(n):
                if j not in subset:
                    poly = [regular(derivatives[j] + d, shifts[j], centered)
                            / factorial(d) for d in range(H)]
                    coeff = conv(coeff, poly, H - 1)
            pref = mp.mpf(1)
            for i in subset:
                pref *= (-1) ** (derivatives[i] + 1) * factorial(derivatives[i])
            nodes = [shifts[i] for i in subset_tuple]
            orders = [derivatives[i] + 1 for i in subset_tuple]
            result += pref * sum(coeff[d] * local_kernel(nodes, orders, d)
                                 for d in range(H))
    return result


def integral(shifts, derivatives, centered=False):
    def f(x):
        answer = mp.mpf(1)
        for a, r in zip(shifts, derivatives):
            answer *= mp.polygamma(r, x + a) + (mp.euler if centered and r == 0 else 0)
        return answer
    cuts = sorted(set([mp.mpf(0)] + shifts + [mp.sqrt(max(shifts)), mp.mpf(1)]))
    return mp.quad(f, cuts)


def run():
    mp.mp.dps = 65
    rows = []
    for centered in (False, True):
        baseline = mp.zeta(3) if centered else mp.zeta(3) - 2 * mp.euler * mp.zeta(2)
        for derivative_position in range(3):
            rs = [int(i == derivative_position) for i in range(3)]
            for eps in (mp.mpf('0.001'), mp.mpf('0.00001')):
                aa = [eps ** mp.sqrt(3), eps ** mp.sqrt(2), eps]
                I = integral(aa, rs, centered)
                Q = contact(aa, rs, centered)
                rows.append(dict(centered=centered, derivative_position=derivative_position + 1,
                                 epsilon=str(eps), remainder=mp.nstr(I - Q, 35),
                                 baseline=mp.nstr(baseline, 35),
                                 residual=mp.nstr(I - Q - baseline, 12)))
                print(json.dumps(rows[-1]), flush=True)
    return rows


if __name__ == '__main__':
    run()
