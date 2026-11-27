"""Numerical illustration for the two conjugate primitive quartic characters modulo 5.

Run with Python 3 and mpmath. All reported brackets are found by sampling.
The scan does not certify completeness, multiplicities, or the precision of an interval.
"""
from functools import partial
import mpmath as mp

mp.mp.dps = 35
MODULUS = 5
HEIGHT = 20
STEP = mp.mpf(1) / 8


def character_data(sign):
    values = [0, 1, sign * 1j, -sign * 1j, -1]
    gauss = sum(values[a] * mp.exp(2j * mp.pi * a / MODULUS)
                for a in range(1, MODULUS))
    epsilon = gauss / (1j * mp.sqrt(MODULUS))
    return values, epsilon


def hardy(t, values, epsilon):
    s = mp.mpc(mp.mpf(1) / 2, t)
    phase = (t * mp.log(MODULUS / mp.pi) / 2
             + mp.im(mp.loggamma((s + 1) / 2)) - mp.arg(epsilon) / 2)
    rotated = mp.exp(1j * phase) * mp.dirichlet(s, values)
    if abs(rotated.imag) > mp.mpf('1e-26') * (1 + abs(rotated)):
        raise ArithmeticError('functional-equation reality check failed')
    return rotated.real


def sign_changes(sign, height=HEIGHT):
    values, epsilon = character_data(sign)
    f = partial(hardy, values=values, epsilon=epsilon)
    a = mp.mpf(0)
    fa = f(a)
    roots = []
    for k in range(1, int(height / STEP) + 1):
        b = k * STEP
        fb = f(b)
        if fa * fb < 0:
            root = mp.findroot(f, (a, b), solver='anderson', tol=mp.mpf('1e-28'))
            residual = abs(mp.dirichlet(mp.mpc('0.5', root), values))
            mirrored = abs(mp.dirichlet(mp.mpc('0.5', -root),
                                        character_data(-sign)[0]))
            if not (a < root < b and max(residual, mirrored) < mp.mpf('1e-24')):
                raise ArithmeticError('root check failed')
            roots.append(root)
        elif fa == 0 or fb == 0:
            raise ArithmeticError('grid endpoint zero requires separate handling')
        a, fa = b, fb
    return roots


if __name__ == '__main__':
    print(f'Numerical sign-change scan, 0 < t <= {HEIGHT}, step 1/8, {mp.mp.dps} digits')
    for sign in (1, -1):
        roots = sign_changes(sign)
        print(f"chi(2) = {'+i' if sign > 0 else '-i'}: " +
              ', '.join(mp.nstr(t, 13) for t in roots))
        other = character_data(-sign)[0]
        cross_value = abs(mp.dirichlet(mp.mpc('0.5', roots[0]), other))
        print('  |L(1/2+it, conjugate character)| at the first listed root: ' +
              mp.nstr(cross_value, 12))
    print('Each reported root has |L(1/2+it,chi)| and conjugate mirrored residual < 1e-24.')
    print('These are numerical sign changes; completeness and interval certification are outside this check.')
