#!/usr/bin/env python3
"""Exact dyadic certificates for the real bracket, noncancellation and amplitude."""
import argparse
import hashlib
import json
from pathlib import Path
from fractions import Fraction
from rigorous import (A, E, IV, P, S, determinant, inverse_bound, matrix, norm,
                      require, row, solve, states, tail_bounds)

HEIGHT = 20
Z_LOW = '0.78615504'
Z_HIGH = '0.78615506'


def derivative_tail_bounds(height, r):
    b, c, t = IV(0), IV(0), IV(0)
    for u in states(height + 16, 'K'):
        inside, outside = IV(0), IV(0)
        for (v, e), coefficient in row(u, 'K').items():
            w = abs(coefficient)*e*r**(e-1) if e else IV(0)
            if sum(v) <= height:
                inside += w
            else:
                outside += w
        if sum(u) <= height:
            b = IV(max(b.hi, outside.hi), raw=True)
        else:
            c = IV(max(c.hi, inside.hi), raw=True)
            t = IV(max(t.hi, outside.hi), raw=True)
        if sum(u) > height + 3:
            require(inside.hi == 0, 'far derivative tail reaches core')
    # For h>=height+17, every exponent e>=m=3h-6. e*r^(e-1)
    # decreases with e once (m+1)*r<m; its height majorant decreases too.
    m = 3*(height + 17)-6
    require((m+1)*r.hi < m*S, 'derivative-tail monotonicity failed')
    t = IV(max(t.hi, (27*m*r**(m-1)).hi), raw=True)
    return b, c, t


def real_certificate(proposals):
    low, high = IV(Z_LOW), IV(Z_HIGH)
    interval = IV(low.lo, high.hi, True)
    result = {'status': 'PASS', 'precision_bits': P, 'height': HEIGHT,
              'z_interval': [Z_LOW, Z_HIGH],
              'rho_interval_exact': [str(Fraction(z)**2) for z in (Z_LOW, Z_HIGH)]}
    context = None
    for label, kind, z in [('L_low', 'L', low), ('L_high', 'L', high),
                           ('K_interval', 'K', interval)]:
        vs, aa = matrix(HEIGHT, z, kind)
        d = determinant(aa)
        kappa, epsilon, inverse_point = inverse_bound(aa, proposals[label])
        b, c, t, delta = tail_bounds(HEIGHT, high, kind)
        test = kappa*delta
        require(test.hi < S, label + ': Schur homotopy not a contraction')
        require(d.lo*d.hi > 0, label + ': determinant sign uncertain')
        if label == 'L_low':
            require(d.lo > 0, 'lower numerator endpoint not positive')
        else:
            require(d.hi < 0, label + ': determinant not negative')
        result[label] = {'dimension': len(vs), 'determinant': d.certificate(),
                         'inverse_norm': kappa.certificate(),
                         'inverse_residual': epsilon.certificate(),
                         'B': b.certificate(), 'C': c.certificate(),
                         'T': t.certificate(), 'Schur_correction': delta.certificate(),
                         'Schur_contraction': test.certificate()}
        if label == 'K_interval':
            context = (vs, aa, kappa, inverse_point, interval, high)
    result['conclusion'] = ('N changes sign between the stated squared endpoints; '
                            'D is strictly negative throughout that interval. '
                            'The global certificate makes the unique zero simple.')
    return result, context


def residue_certificate(context):
    vs, aa, kappa, inverse_point, z, high = context
    n = len(vs)
    index = {v: i for i, v in enumerate(vs)}
    kp = [[IV(0) for _ in range(n)] for _ in range(n)]
    for i, u in enumerate(vs):
        for (v, e), coefficient in row(u, 'K').items():
            if v in index and e:
                kp[i][index[v]] += coefficient*e*z**(e-1)
    a1 = IV(max(sum(x.abshi().hi for x in r) for r in kp), raw=True)
    rhs = [IV(0) for _ in vs]
    rhs[index[A]], rhs[index[E]] = IV(1), z**3
    u, error_u = solve(aa, rhs, kappa, inverse_point)
    derivative_rhs = [sum((kp[i][j]*u[j] for j in range(n)), IV(0)) for i in range(n)]
    derivative_rhs[index[E]] += 3*z**2
    up, error_up = solve(aa, derivative_rhs, kappa, inverse_point)
    b, c, t, delta = tail_bounds(HEIGHT, high, 'K')
    b1, c1, t1 = derivative_tail_bounds(HEIGHT, high)
    delta1 = b1*c/(1-t) + b*t1*c/(1-t)**2 + b*c1/(1-t)
    eta = kappa*delta
    require(eta.hi < S, 'residue Schur contraction failed')
    core_error = kappa*delta*norm(u)/(1-eta)
    core_bound = norm(u)+core_error
    derivative_error = kappa/(1-eta)*(delta*norm(up) + a1*core_error + delta1*core_bound)
    iz = IV(up[index[A]].lo-derivative_error.hi,
            up[index[A]].hi+derivative_error.hi, True)
    require(iz.lo > 0, 'infinite derivative not positive')
    amplitude = IV(2)/(z*iz)
    iq = iz/(2*z)
    residue = -IV(1)/iq
    require(IV('0.1838102868').hi < amplitude.lo and
            amplitude.hi < IV('0.1838120734').lo, 'published amplitude enclosure failed')
    return {'status': 'PASS', 'height': HEIGHT, 'z_interval': [Z_LOW, Z_HIGH],
            'finite_Iz': up[index[A]].certificate(),
            'finite_solve_error_u': error_u.certificate(),
            'finite_solve_error_uz': error_up.certificate(),
            'K_inverse': kappa.certificate(), 'Kprime': a1.certificate(),
            'Schur': delta.certificate(), 'Schur_derivative': delta1.certificate(),
            'solution_tail_error': core_error.certificate(),
            'derivative_tail_error': derivative_error.certificate(),
            'infinite_Iz': iz.certificate(), 'infinite_Iprime_q': iq.certificate(),
            'residue_q': residue.certificate(), 'asymptotic_amplitude': amplitude.certificate(),
            'amplitude_widened_decimal': ['0.1838102868', '0.1838120734']}


def run(data_dir):
    path = data_dir/'inverse_proposals.json'
    data = json.loads(path.read_text())
    require(data['format'] == 'Report183 exact dyadic inverse proposals v1',
            'unknown inverse proposal format')
    real, context = real_certificate(data['proposals'])
    return {'status': 'PASS', 'arithmetic': 'outward-rounded dyadic integer endpoints',
            'inverse_proposals_sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
            'real': real, 'residue': residue_certificate(context)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--data-dir', type=Path, default=Path(__file__).resolve().parent.parent/'data')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    text = json.dumps(run(args.data_dir), indent=2, sort_keys=True)+'\n'
    if args.output:
        args.output.write_text(text)
    print(text, end='')


if __name__ == '__main__':
    main()
