#!/usr/bin/env python3
"""Reproducible finite checks for Sharp Symmetry Certification.

Requires Python >= 3.10 and NumPy.  Enumerations of tensors, cube-root phases, and additive
polynomial identities use integer arithmetic. Complex phase checks use
float64/complex128 and tolerance 3e-10; they are not formal proofs.
Run: python checks/verify.py --output checks/results.json
"""
from __future__ import annotations
import argparse
import itertools
import json
import math
from pathlib import Path
import platform
import time
import numpy as np

SEED = 20261006
TOL = 3e-10


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def space(p: int, n: int) -> tuple[np.ndarray, np.ndarray]:
    points = np.array(list(itertools.product(range(p), repeat=n)), dtype=np.int64)
    weights = p ** np.arange(n - 1, -1, -1)
    shifts = (((points[:, None, :] + points[None, :, :]) % p) @ weights)
    return points, shifts


def phase(a: np.ndarray, p: int) -> np.ndarray:
    return np.exp(2j * np.pi * (a % p) / p)


def rank_mod(a: np.ndarray, p: int) -> int:
    a = a.copy() % p
    row = 0
    for col in range(a.shape[1]):
        pivots = np.flatnonzero(a[row:, col])
        if not len(pivots):
            continue
        pivot = row + int(pivots[0])
        a[[row, pivot]] = a[[pivot, row]]
        a[row] = a[row] * pow(int(a[row, col]), -1, p) % p
        for j in range(a.shape[0]):
            if j != row:
                a[j] = (a[j] - a[j, col] * a[row]) % p
        row += 1
        if row == a.shape[0]:
            break
    return row


def q_b(g: np.ndarray, v: np.ndarray, b: np.ndarray,
        points: np.ndarray, shifts: np.ndarray, p: int) -> float:
    phases = phase(-(points @ b @ points.T), p)
    coefficients = np.mean(g[shifts] * np.conj(v)[None, :] * phases, axis=1)
    return float(np.mean(np.abs(coefficients) ** 2))


def bounded_random(rng: np.random.Generator, size: int) -> np.ndarray:
    return rng.random(size) * np.exp(2j * np.pi * rng.random(size))


def bilinear_checks(rng: np.random.Generator) -> dict:
    p = 3
    points, shifts = space(p, 2)
    max_violation = 0.0
    max_sharp_error = 0.0
    mixed_cases = 0
    for entries in itertools.product(range(p), repeat=4):
        b = np.array(entries, dtype=np.int64).reshape(2, 2)
        r = rank_mod(b - b.T, p) // 2
        for _ in range(4):
            g = bounded_random(rng, len(points))
            v = bounded_random(rng, len(points))
            bound = p ** (-r) * np.mean(abs(g) ** 2) * np.mean(abs(v) ** 2)
            value = q_b(g, v, b, points, shifts, p)
            max_violation = max(max_violation, value - bound)
            require(value <= bound + TOL, 'mixed bilinear inequality')
            mixed_cases += 1
        b0 = np.array([[0, (b[0, 1] - b[1, 0]) % p], [0, 0]])
        s = (b - b0) % p
        require(np.array_equal(s, s.T), 'quadratic gauge is symmetric')
        polynomial = (2 * np.einsum('xi,ij,xj->x', points, s, points)) % p
        g = phase(polynomial, p)
        error = abs(q_b(g, g, b, points, shifts, p) - p ** (-r))
        max_sharp_error = max(max_sharp_error, error)
        require(error < TOL, 'sharp quadratic gauge example')
    points4, shifts4 = space(p, 4)
    for _ in range(48):
        b = rng.integers(0, p, (4, 4))
        r = rank_mod(b - b.T, p) // 2
        g = bounded_random(rng, len(points4))
        v = bounded_random(rng, len(points4))
        value = q_b(g, v, b, points4, shifts4, p)
        bound = p ** (-r) * np.mean(abs(g)**2) * np.mean(abs(v)**2)
        require(value <= bound + TOL, 'four-dimensional mixed bound')
        mixed_cases += 1
    b = np.zeros((4, 4), dtype=np.int64)
    b[0, 1] = b[2, 3] = 1
    value = q_b(np.ones(81), np.ones(81), b, points4, shifts4, p)
    require(abs(value - 1/9) < TOL, 'rank-four sharp example')
    return {'all_2_by_2_bilinear_matrices_F3': 81,
            'mixed_random_cases': mixed_cases,
            'quadratic_extremizers_checked': 81,
            'max_mixed_bound_violation': max_violation,
            'max_extremizer_absolute_error': max_sharp_error,
            'rank_four_example_value': value}


def all_root_functions() -> dict:
    p = 3
    points, shifts = space(p, 2)
    b = np.array([[0, 1], [0, 0]], dtype=np.int64)
    exponents = np.array(list(itertools.product(range(p), repeat=9)), dtype=np.int64)
    numerators = np.zeros(len(exponents), dtype=np.int64)
    for h in range(9):
        residues = (exponents[:, shifts[h]] - exponents
                    - (points[h] @ b @ points.T)[None, :]) % p
        counts = [(residues == j).sum(axis=1) for j in range(3)]
        a, c, d = counts
        # |a + c*omega + d*omega^2|^2, omega^2+omega+1=0.
        numerators += a*a+c*c+d*d-a*c-a*d-c*d
    denominator = 9**3
    require(int(numerators.max()) == denominator//3,
            'exact exhaustive root function maximum')
    unique, counts = np.unique(numerators, return_counts=True)
    return {'functions_enumerated': len(exponents),
            'maximum_numerator': int(numerators.max()),
            'denominator': denominator,
            'maximizers_exact': int(np.count_nonzero(numerators == denominator//3)),
            'numerator_histogram': {str(int(a)): int(b) for a, b in zip(unique, counts)},
            'arithmetic': 'exact int64 cyclotomic norm; omega^2+omega+1=0'}


def tensor_checks(rng: np.random.Generator) -> dict:
    p = 3
    points, shifts = space(p, 2)
    tensors = np.array(list(itertools.product(range(p), repeat=8)), dtype=np.int64)
    tensors = tensors.reshape(-1, 2, 2, 2)
    sigma = np.einsum('ai,bj,tijc->tabc', points, points, tensors) % p
    zero_counts = np.sum(np.all(sigma == 0, axis=-1), axis=(1, 2))
    symmetric = (np.all(tensors == tensors.transpose(0, 3, 2, 1), axis=(1,2,3))
                 & np.all(tensors == tensors.transpose(0, 1, 3, 2), axis=(1,2,3)))
    require(int(symmetric.sum()) == 81, 'symmetric tensor dimension')
    require(int(zero_counts[~symmetric].max()) == 45, 'sharp threshold 45/81')
    contractions = [np.einsum('uj,tijc->tuic', points, tensors) % p,
                    np.einsum('ui,tijc->tujc', points, tensors) % p]
    rank_flags = []
    for bs in contractions:
        flags = bs[:, :, 0, 1] != bs[:, :, 1, 0]
        rank_flags.append(flags)
        # E 3^-r = (27 - 2 * number of rank-two slices) / 27.
        profile_numerator81 = 3 * (27 - 2 * flags.sum(axis=1))
        require(bool(np.all(zero_counts <= profile_numerator81)), 'exact profile bound')
    f = bounded_random(rng, 9)
    first = f[shifts] * np.conj(f)[None, :]
    # d2[a,b,x] = derivative_b(derivative_a(f))(x).
    d2 = first[:, shifts] * np.conj(first)[:, None, :]
    chosen = rng.choice(len(tensors), size=256, replace=False)
    max_violation = 0.0
    max_cube_error = 0.0
    m2 = np.mean(abs(first)**2, axis=1)**2
    for index in chosen:
        kernel = phase(-np.einsum('abj,xj->abx', sigma[index], points), p)
        coeff = np.mean(d2 * kernel, axis=2)
        a_value = float(np.mean(abs(coeff)**2))
        for flags in rank_flags:
            profile = float(np.mean(np.where(flags[index], 1/3, 1) * m2))
            max_violation = max(max_violation, a_value - profile)
            require(a_value <= profile + TOL, 'amplitude-sensitive profile')
        # Independent Fourier-square expansion: average in x,y.
        d3 = d2[:, :, shifts] * np.conj(d2)[:, :, None, :]
        tphase = phase(-np.einsum('abj,yj->aby', sigma[index], points), p)
        cube = np.mean(d3 * tphase[:, :, :, None])
        err = abs(a_value - cube)
        max_cube_error = max(max_cube_error, float(err))
        require(err < TOL, 'Fourier-square/cube expansion sign')
    return {'trilinear_tensors_enumerated': len(tensors),
            'fully_symmetric_tensors': int(symmetric.sum()),
            'nonsymmetric_max_zero_frequency_count': int(zero_counts[~symmetric].max()),
            'denominator': 81,
            'nonsymmetric_endpoint_tensors': int(np.count_nonzero((~symmetric) & (zero_counts == 45))),
            'random_function_profiles_checked': len(chosen),
            'max_amplitude_profile_violation': max_violation,
            'max_cube_identity_absolute_error': max_cube_error,
            'tensor_count_arithmetic': 'exact int64 over F3'}


def symmetric_tensor(rng: np.random.Generator, p: int, d: int) -> np.ndarray:
    coefficients = rng.integers(0, p, d + 1)
    t = np.empty((2,) * d, dtype=np.int64)
    for indices in itertools.product(range(2), repeat=d):
        t[indices] = coefficients[sum(indices)]
    return t


def evaluate_tensor(t: np.ndarray, vectors: list[np.ndarray], p: int) -> np.ndarray:
    # Each vector is batch x 2; this is intentionally explicit for auditing.
    result = np.zeros(vectors[0].shape[0], dtype=np.int64)
    for indices in itertools.product(range(2), repeat=len(vectors)):
        term = np.full_like(result, t[indices])
        for vector, index in zip(vectors, indices):
            term = term * vector[:, index] % p
        result = (result + term) % p
    return result


def polarization_checks(rng: np.random.Generator) -> dict:
    count = 0
    for p, d in [(5, 3), (7, 4), (7, 5)]:
        inv_factorial = pow(math.factorial(d), -1, p)
        for _ in range(6):
            t = symmetric_tensor(rng, p, d)
            x = rng.integers(0, p, (1024, 2))
            hs = [rng.integers(0, p, (1024, 2)) for _ in range(d)]
            diff = np.zeros(1024, dtype=np.int64)
            for bits in itertools.product(range(2), repeat=d):
                y = (x + sum((h for h, bit in zip(hs, bits) if bit), start=np.zeros_like(x))) % p
                value = evaluate_tensor(t, [y] * d, p) * inv_factorial % p
                diff = (diff + (-1) ** (d - sum(bits)) * value) % p
            require(np.array_equal(diff, evaluate_tensor(t, hs, p)), 'exact polarization')
            count += 1024
    p = 5
    points, shifts = space(p, 2)
    max_error = 0.0
    max_pointwise_error = 0.0
    for _ in range(12):
        t = symmetric_tensor(rng, p, 3)
        polynomial = evaluate_tensor(t, [points]*3, p) * pow(6, -1, p) % p
        sigma = np.einsum('ai,bj,ijc->abc', points, points, t) % p
        f = bounded_random(rng, 25)
        g = f * phase(-polynomial, p)
        df = f[shifts] * np.conj(f)[None, :]
        dg = g[shifts] * np.conj(g)[None, :]
        d2f = df[:, shifts] * np.conj(df)[:, None, :]
        d2g = dg[:, shifts] * np.conj(dg)[:, None, :]
        kernel = phase(-np.einsum('abj,xj->abx', sigma, points), p)
        left = abs(np.mean(d2f * kernel, axis=2))**2
        right = abs(np.mean(d2g, axis=2))**2
        err = float(np.max(abs(left-right)))
        max_pointwise_error = max(max_pointwise_error, err)
        max_error = max(max_error, abs(float(np.mean(left)-np.mean(right))))
        require(err < TOL, 'pointwise lossless spectral shift')
    return {'exact_sampled_polarization_tuples': count,
            'full_F5_squared_energy_identity_cases': 12,
            'max_pointwise_identity_absolute_error': max_pointwise_error,
            'max_average_identity_absolute_error': max_error}


def low_characteristic_and_affine_checks() -> dict:
    count = 0
    for x, a, b, c in itertools.product(range(3), repeat=4):
        total = 0
        for bits in itertools.product(range(2), repeat=3):
            y = (x + a*bits[0] + b*bits[1] + c*bits[2]) % 3
            total += (-1)**(3-sum(bits)) * y
        require(total % 9 == (-3*a*b*c) % 9, 'nonclassical third derivative')
        count += 1
    points, shifts = space(3, 1)
    f = phase(np.arange(3), 9)
    df = f[shifts]*np.conj(f)[None, :]
    d2 = df[:, shifts]*np.conj(df)[:, None, :]
    sigma = -(points[:,0,None] * points[None,:,0]) % 3
    kernel = phase(-sigma[:,:,None]*points[None,None,:,0], 3)
    energy = float(np.mean(abs(np.mean(d2*kernel, axis=2))**2))
    require(abs(energy-1) < TOL, 'nonclassical perfect energy')
    # Affine selector offset: top homogeneous term is zero, but energy is
    # not U^2(f)^4. This is a boundary on the lossless homogeneous theorem.
    p = 17
    points, shifts = space(p, 1)
    chi = phase(points[:,0], p)
    f = (1+chi)/2
    df = f[shifts]*np.conj(f)[None,:]
    a_value = float(np.mean(abs(np.mean(df*np.conj(chi)[None,:], axis=1))**2))
    u2fourth = float(np.mean(abs(np.mean(df, axis=1))**2))
    require(abs(a_value-1/16) < TOL, 'affine offset energy')
    require(abs(u2fourth-1/8) < TOL, 'affine offset U2')
    return {'exact_nonclassical_tuples': count,
            'nonclassical_energy': energy,
            'affine_offset_energy_F17': a_value,
            'affine_offset_U2_fourth_power': u2fourth}


def multiaffine_checks(rng: np.random.Generator) -> dict:
    p = 3
    points, shifts = space(p, 2)
    f = bounded_random(rng, 9)
    first = f[shifts] * np.conj(f)[None, :]
    d2 = first[:, shifts] * np.conj(first)[:, None, :]
    m2 = np.mean(abs(first)**2, axis=1)**2
    max_violation = 0.0
    for _ in range(256):
        t = rng.integers(0, p, (2, 2, 2))
        l1 = rng.integers(0, p, (2, 2))
        l2 = rng.integers(0, p, (2, 2))
        offset = rng.integers(0, p, 2)
        sigma = (np.einsum('ai,bj,ijc->abc', points, points, t)
                 + (points @ l1)[:, None, :] + (points @ l2)[None, :, :]
                 + offset) % p
        kernel = phase(-np.einsum('abj,xj->abx', sigma, points), p)
        value = float(np.mean(abs(np.mean(d2 * kernel, axis=2))**2))
        bs = [(np.einsum('uj,ijc->uic', points, t)+l1) % p,
              (np.einsum('ui,ijc->ujc', points, t)+l2) % p]
        for b in bs:
            flags = b[:, 0, 1] != b[:, 1, 0]
            bound = float(np.mean(np.where(flags, 1/3, 1) * m2))
            max_violation = max(max_violation, value-bound)
            require(value <= bound+TOL, 'multiaffine profile with offsets')
    return {'seeded_multiaffine_selectors': 256,
            'profiles_per_selector': 2,
            'max_bound_violation': max_violation}


def extension_field_checks(rng: np.random.Generator) -> dict:
    # F9 = F3[t]/(t^2+1), encoded a+3*b for a+b*t; Trace(a+b*t)=2*a.
    elems = np.arange(9, dtype=np.int64)
    a, b = elems % 3, elems // 3
    add = ((a[:, None]+a[None, :]) % 3
           + 3*((b[:, None]+b[None, :]) % 3))
    mul = ((a[:, None]*a[None, :]-b[:, None]*b[None, :]) % 3
           + 3*((a[:, None]*b[None, :]+b[:, None]*a[None, :]) % 3))
    points = np.array(list(itertools.product(range(9), repeat=2)), dtype=np.int64)
    shifts = (9*add[points[:, None, 0], points[None, :, 0]]
              + add[points[:, None, 1], points[None, :, 1]])
    bvalues = mul[points[:, None, 0], points[None, :, 1]]
    kernel = phase(-2*(bvalues % 3), 3)
    one_value = float(np.mean(abs(np.mean(kernel, axis=1))**2))
    require(abs(one_value-1/9) < TOL, 'F9 bilinear endpoint')
    for _ in range(24):
        g = bounded_random(rng, 81)
        v = bounded_random(rng, 81)
        value = float(np.mean(abs(np.mean(g[shifts]*np.conj(v)[None,:]*kernel,
                                          axis=1))**2))
        bound = np.mean(abs(g)**2)*np.mean(abs(v)**2)/9
        require(value <= bound+TOL, 'F9 mixed bilinear bound')
    # Selector sigma(h1,h2)=(a(h1)*a(h2))*c has 17/81 zero frequency.
    values = mul[points[:, None, 0], points[None, :, 0]]
    count = int(np.count_nonzero(values == 0))
    require(count*81 == 17*81**2, 'F9 trilinear endpoint count')
    return {'field': 'F3[t]/(t^2+1)', 'mixed_cases': 24,
            'bilinear_endpoint_value': one_value,
            'trilinear_zero_frequency_count': count,
            'trilinear_total_tuples': 81**2,
            'trilinear_energy_fraction': '17/81'}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path(__file__).with_name('results.json'))
    args = parser.parse_args()
    start = time.time()
    rng = np.random.default_rng(SEED)
    results = {'seed': SEED, 'tolerance': TOL, 'python': platform.python_version(),
               'numpy': np.__version__, 'status': 'running'}
    for name, fun in [('bilinear', lambda: bilinear_checks(rng)),
                      ('root_functions', all_root_functions),
                      ('trilinear', lambda: tensor_checks(rng)),
                      ('polarization', lambda: polarization_checks(rng)),
                      ('boundary_examples', low_characteristic_and_affine_checks),
                      ('multiaffine', lambda: multiaffine_checks(rng)),
                      ('extension_field', lambda: extension_field_checks(rng))]:
        results[name] = fun()
        print(f'{name}: PASS', flush=True)
    results['status'] = 'all checks passed'
    results['elapsed_seconds'] = round(time.time()-start, 3)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(results, indent=2)+'\n', encoding='utf-8')
    print(json.dumps(results, indent=2))


if __name__ == '__main__':
    main()
