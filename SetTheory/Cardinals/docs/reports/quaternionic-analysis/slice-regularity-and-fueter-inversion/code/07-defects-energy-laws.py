#!/usr/bin/env python3
"""Independent diagnostics of the Cauchy layer and the higher-pole energy law.

Run from the archive root:
  python checks/verify_sources_and_poles.py --output checks/source_and_pole_results.json
These floating-point tests do not replace the analytic proofs.
"""
from __future__ import annotations
import argparse
import json
import math
from pathlib import Path
import numpy as np
from verify import paired_kernel


def multiply(p: np.ndarray, q: np.ndarray) -> np.ndarray:
    """Hamilton product, component order (real, i, j, k), broadcast leading axes."""
    p, q = np.broadcast_arrays(np.asarray(p, dtype=float), np.asarray(q, dtype=float))
    if p.shape[-1] != 4:
        raise ValueError('Last dimension must be four quaternion components.')
    scalar = p[..., :1]*q[..., :1] - np.sum(p[..., 1:]*q[..., 1:], axis=-1, keepdims=True)
    vector = p[..., :1]*q[..., 1:] + q[..., :1]*p[..., 1:] + np.cross(p[..., 1:], q[..., 1:])
    return np.concatenate((scalar, vector), axis=-1)


def layer(q: np.ndarray, zeta: complex, a: np.ndarray, b: np.ndarray,
          n: int = 100) -> np.ndarray:
    """Sphere integration: Gauss-Legendre in cos(theta), trapezoidal in phi."""
    u, w = np.polynomial.legendre.leggauss(n)
    phi = 2*math.pi*np.arange(2*n)/(2*n)
    u, phi = np.meshgrid(u, phi, indexing='ij')
    I = np.stack((np.zeros_like(u), np.sqrt(1-u*u)*np.cos(phi),
                  np.sqrt(1-u*u)*np.sin(phi), u), axis=-1)
    p = zeta.imag*I
    p[..., 0] = zeta.real
    v = q-p
    norm_squared = np.sum(v*v, axis=-1)
    if np.any(norm_squared == 0):
        raise ValueError('Evaluation point must not lie on the source sphere.')
    conjugate = v*np.array([1., -1., -1., -1.])
    E = conjugate/(2*math.pi**2*norm_squared**2)[..., None]
    density = (zeta.real*a+b)/zeta.imag + multiply(I, a)
    integrand = multiply(E, density)
    return 2*zeta.imag**2*(2*math.pi/(2*n))*np.sum(integrand*w[:, None, None], axis=(0, 1))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path('source_and_pole_results.json'))
    args = parser.parse_args()
    zeta = 0.3+1.7j
    a = np.array([1., -.5, .8, 1.2])
    b = np.array([.2, 1.4, -.3, .7])
    layer_rows = []
    for q in (np.array([.8, .4, .1, .2]), np.array([-1., 2.4, .8, -.3]),
              np.array([4., -.7, 1.1, 2.])):
        y = np.linalg.norm(q[1:])
        Iq = np.r_[0., q[1:]/y]
        P, Q = paired_kernel(q[0], y, zeta, a, b)
        value = P+multiply(Iq, Q)
        integral = layer(q, zeta, a, b)
        error = float(np.max(np.abs(integral-value)))
        if error > 1e-10:
            raise AssertionError(f'Cauchy layer test failed with error {error}.')
        layer_rows.append({'q': q.tolist(), 'formula': value.tolist(),
                           'layer_integral': integral.tolist(), 'max_absolute_error': error})

    # C is a quaternion complexification: four complex coordinate coefficients.
    C = np.array([1.+.4j, -.2+.7j, .6-.3j, -.5+1.1j])
    angles = 2*math.pi*np.arange(2048)/2048
    pole_rows = []
    for k in (1, 2, 3):
        cnorm_squared = float(np.vdot(C, C).real)
        expected_shell = 32*math.pi**2*k*k*cnorm_squared
        rows = []
        for rho in (1e-2, 1e-3, 1e-4):
            z = zeta+rho*np.exp(1j*angles)
            y = z.imag
            w, wr = z-zeta, z-zeta.conjugate()
            F = w[:, None]**(-k)*C + wr[:, None]**(-k)*C.conjugate()
            Fp = -k*(w[:, None]**(-k-1)*C+wr[:, None]**(-k-1)*C.conjugate())
            P = -2*Fp.imag/y[:, None]
            Q = 2*Fp.real/y[:, None]-2*F.imag/y[:, None]**2
            scaled_shell = float(8*math.pi**2*rho**(2*k+2)*np.mean(
                y*y*np.sum(P*P+Q*Q, axis=-1)))
            error = abs(scaled_shell/expected_shell-1)
            rows.append({'rho': rho, 'scaled_shell': scaled_shell, 'relative_error': error})
        if rows[-1]['relative_error'] > 1e-6:
            raise AssertionError('Higher-pole shell coefficient test failed.')
        pole_rows.append({'pole_order': k, 'expected_scaled_shell': expected_shell,
                          'predicted_integrated_coefficient': 16*math.pi**2*k*cnorm_squared,
                          'tests': rows})
    result = {'scope': 'Independent numerical diagnostics, not formal verification.',
              'cauchy_layer': layer_rows, 'higher_poles': pole_rows}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()
