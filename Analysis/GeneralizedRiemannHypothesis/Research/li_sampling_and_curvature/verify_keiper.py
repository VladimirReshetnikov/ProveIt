#!/usr/bin/env python3
"""Unconditional verification of the first negative Riemann Li curvature.

Requires python-flint (tested with 0.9.0). All series coefficients are
Arb real balls. The identity used is log(2 xi(z/(z-1))) = sum(lambda_n z^n/n).
"""

from flint import arb, arb_series, ctx


def main():
    if not __debug__:
        raise RuntimeError("Run Python without -O so all checks are enabled.")
    ctx.prec = 512  # working precision in bits
    ctx.cap = 120   # include coefficients through degree 119
    z = arb_series([0, 1])
    s = -z / (1-z)

    # 2 xi(s) = (1-s) (-2 zeta(s)) pi^(-s/2) Gamma(1+s/2).
    # All factors have positive constant term; the chosen logarithm is
    # real near z=0 and its constant coefficient is zero.
    logarithm = ((1-s).log() + (-2*s.zeta()).log()
                 - s*(arb.pi().log()/2) + (1+s/2).lgamma())
    li = [n * logarithm[n] for n in range(120)]
    curvature = [2*li[1]]
    curvature.extend(li[n-1] - 2*li[n] + li[n+1] for n in range(1, 119))
    assert all(x > arb('0.00014') for x in curvature[:118])
    assert curvature[118] < arb('-0.00026')

    print('Arb verified the 118 strict positive comparisons and one negative comparison.')
    print('d_117 =', curvature[117].str(24))
    print('d_118 =', curvature[118].str(24))


if __name__ == '__main__':
    main()
