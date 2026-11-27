#!/usr/bin/env python3
"""Certify low zeta zero counts from Taylor coefficients, using python-flint 0.9.0.

Install with `python -m pip install python-flint==0.9.0` and run this file.
Every reported test uses rigorous Arb enclosures. No zero ordinate is evaluated.
"""
from flint import arb, arb_mat, arb_poly, arb_series, ctx


def scaled_moments(degree):
    """Return M_j = 200**j sum (1/4 + gamma**2)**(-j), j=1,...,degree."""
    ctx.prec = 320
    ctx.cap = degree + 1
    u = arb_series([0, 1])
    s = (1 - (1 - 4*u).sqrt()) / 2
    xi = (s-1) * (1+s/2).gamma() * (-s*arb.pi().log()/2).exp() * s.zeta()
    log_xi = (2*xi).log()
    return [None] + [-j * 200**j * log_xi[j] for j in range(1, degree+1)]


def spectral_sum(poly, moments):
    """Sum a polynomial with zero constant term on the scaled zero parameters."""
    assert poly[0].is_zero()
    return sum(poly[j] * moments[j] for j in range(1, poly.length()))


def parameter(height):
    return 200 / (arb(height)**2 + arb(1)/4)


def sign_of(ball):
    if ball > 0:
        return 1
    if ball < 0:
        return -1
    raise ArithmeticError(f'Cannot certify sign: {ball}')


def positive_directions(moments, height):
    """Inertia of sum y (y-h) v(y)v(y)^T, with v=(1,y,...,y^4)."""
    h = parameter(height)
    signs = [1]
    for dim in range(1, 6):
        principal = arb_mat([[moments[i+j+2] - h*moments[i+j+1]
                              for j in range(dim)] for i in range(dim)])
        signs.append(sign_of(principal.det()))
    return signs, sum(s == t for s,t in zip(signs, signs[1:]))


def main():
    moments = scaled_moments(10)
    for j, moment in enumerate(moments[1:], start=1):
        print(f'M{j:02}  {moment.str(22)}')

    y = arb_poly([0, 1])
    top_lower = arb(9973)/10000
    cutoff = parameter(20)
    w = y*y - (arb(3)/8)*y + arb(1)/100
    g = (y * (y-arb(1)/7))**2
    existence = spectral_sum(y*(y-top_lower)*w*w, moments)
    exclusion = spectral_sum(g, moments) - g(top_lower) - g(cutoff)
    assert sign_of(existence) == 1 and sign_of(exclusion) == -1
    print('Six moments, existence:', existence.str(16))
    print('Six moments, exclusion:', exclusion.str(16))
    print('Exactly one positive ordinate at or below 20, counted with multiplicity.')

    for height, npos in [('14.13474', 1), ('21.11', 2)]:
        signs, n = positive_directions(moments, height)
        assert n == npos
        print(f'Ten moments, height {height}: minor signs {signs}, {n} positive directions')

    first, second = parameter('14.13474'), parameter('21.11')
    third = parameter(24)
    remaining = moments[6] - first**6 - second**6
    assert remaining > 0 and remaining < third**6
    print('Available sixth-power sum after two lower bounds:', remaining.str(16))
    print('Sixth power required by a third zero at or below 24:', (third**6).str(16))
    lower_height = (200/moments[10]**(arb(1)/10)-arb(1)/4).sqrt()
    assert lower_height > arb('14.1344')
    print('First ordinate bounded below by', lower_height.str(16))
    print('One ordinate in (14.1344,14.13474), another in (20,21.11), none further up to 24.')


if __name__ == '__main__':
    main()
