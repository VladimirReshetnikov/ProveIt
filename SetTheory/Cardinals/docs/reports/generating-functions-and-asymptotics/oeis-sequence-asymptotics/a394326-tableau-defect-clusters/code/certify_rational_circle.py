#!/usr/bin/env python3
"""Exact standard-library global zero-count certificate for A394326.

All acceptance predicates use Python integers or fractions.Fraction.  The
mathematical mesh/homotopy proof is given in the accompanying report.  No asserted
condition depends on Python's removable ``assert`` statement.
"""
import argparse
import hashlib
import json
from collections import defaultdict
from fractions import Fraction as F
from pathlib import Path

H = 8
R = F(63, 100)
Z_RADIUS = F(4, 5)
MESH_PER_QUADRANT = 2048
A = (1, 0)
E = (0, 2)


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def sign(n):
    return (n > 0) - (n < 0)


def states(height):
    return [(x, h - x) for h in range(1, height + 1)
            for x in range(h + 1)
            if (x + 2 * (h - x)) % 3 == 1 and (x, h - x) != A]


def edges(u, gauged):
    x, y = u
    if gauged:
        out = [((x + 1, y), 2*x + y - 1)]
        if x:
            out.append(((x - 1, y + 1), x + y - 1))
        if y and u != (0, 1):
            out.append(((x, y - 1), x + 2*y - 1))
    else:
        out = [((x + 1, y), 0)]
        if x:
            out.append(((x - 1, y + 1), x - 1))
        if y and u != (0, 1):
            out.append(((x, y - 1), x + 2*y - 2))
    require(all(e >= 0 for _, e in out), 'negative transition exponent')
    return out


def fold(u, gauged):
    current = {(u, 0): 1}
    for _ in range(3):
        nxt = defaultdict(int)
        for (v, exponent), multiplicity in current.items():
            for w, cost in edges(v, gauged):
                nxt[w, exponent + cost] += multiplicity
        current = nxt
    return dict(current)


def row(u, gauged=True):
    result = defaultdict(int, fold(u, gauged))
    if u == E:
        shift = 3 if gauged else 2
        for (v, exponent), multiplicity in fold(A, gauged).items():
            result[v, exponent + shift] -= multiplicity
    return {(v, exponent): multiplicity
            for (v, exponent), multiplicity in result.items()
            if v != A and multiplicity}


def gauge(u):
    x, y = u
    return x*x + x*y + y*y - 2*x - 2*y


def polynomial_matrix(vs, gauged):
    index = {v: j for j, v in enumerate(vs)}
    matrix = [[{} for _ in vs] for _ in vs]
    for i, u in enumerate(vs):
        matrix[i][i][0] = 1
        for (v, exponent), coefficient in row(u, gauged).items():
            if v in index:
                entry = matrix[i][index[v]]
                entry[exponent] = entry.get(exponent, 0) - coefficient
        for j in range(len(vs)):
            matrix[i][j] = {k: c for k, c in matrix[i][j].items() if c}
    return matrix


def validate_data(poly_data, ad):
    require(poly_data.get('H') == H, 'wrong polynomial section height')
    p = poly_data['coeffs']
    require(p and all(type(c) is int for c in p), 'invalid polynomial coefficients')
    require(len(p) == 162 and p[-1] != 0, 'wrong N8 polynomial degree')
    require(p[0] == 1, 'wrong N8 constant term')
    vs = states(H)
    require(ad['states'] == [list(v) for v in vs], 'incomplete or misordered states')
    n = len(vs)
    require(len(ad['adjugate']) == n*n, 'wrong adjugate dimension')
    require(all(isinstance(v, list) and v and all(type(c) is int for c in v)
                for v in ad['adjugate']), 'invalid adjugate entries')
    require(all(type(c) is int for c in ad['den']), 'invalid denominator')
    require(ad['den'][::2] == p and not any(ad['den'][1::2]),
            'denominator is not exactly N8(z^2)')
    return p, vs


def verify_adjugate(matrix, ad):
    n = len(matrix)
    den = ad['den']
    for i in range(n):
        for j in range(n):
            product = defaultdict(int)
            for k in range(n):
                for e, coefficient in matrix[i][k].items():
                    for d, a in enumerate(ad['adjugate'][k*n + j]):
                        product[e + d] += coefficient*a
            actual = {e: c for e, c in product.items() if c}
            target = {e: c for e, c in enumerate(den) if c} if i == j else {}
            require(actual == target, 'adjugate polynomial identity failed')


def bareiss_integer_determinant(matrix):
    """Exact fraction-free elimination, including zero pivots and singularity."""
    n = len(matrix)
    require(all(len(row_) == n for row_ in matrix), 'nonsquare determinant')
    if not n:
        return 1
    work = [row_[:] for row_ in matrix]
    previous = 1
    orientation = 1
    for k in range(n - 1):
        pivot_row = next((i for i in range(k, n) if work[i][k]), None)
        if pivot_row is None:
            return 0
        if pivot_row != k:
            work[k], work[pivot_row] = work[pivot_row], work[k]
            orientation = -orientation
        pivot = work[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                numerator = work[i][j]*pivot - work[i][k]*work[k][j]
                quotient, remainder = divmod(numerator, previous)
                require(remainder == 0, 'Bareiss division was not exact')
                work[i][j] = quotient
            work[i][k] = 0
        previous = pivot
    return orientation*work[-1][-1]


def evaluate_real_polynomial(coefficients, q):
    value = 0
    for coefficient in reversed(coefficients):
        value = value*q + coefficient
    return value


def verify_genuine_determinant(raw_matrix, p):
    # The Leibniz formula proves this degree bound; no interpolation assumption.
    row_degrees = [max((e for entry in row_ for e in entry), default=0)
                   for row_ in raw_matrix]
    bound = sum(row_degrees)
    require(len(p) - 1 <= bound, 'polynomial exceeds determinant degree bound')
    evaluations = hashlib.sha256()
    for q in range(bound + 1):
        matrix = [[sum(c*pow(q, e) for e, c in entry.items())
                   for entry in row_] for row_ in raw_matrix]
        determinant = bareiss_integer_determinant(matrix)
        require(determinant == evaluate_real_polynomial(p, q),
                'genuine determinant identity failed at integer q=' + str(q))
        evaluations.update((str(q) + ':' + str(determinant) + '\n').encode('ascii'))
    return {'method': 'degree-bounded integer evaluations and exact Bareiss',
            'row_degree_bounds': row_degrees,
            'determinant_degree_bound': bound,
            'distinct_integer_evaluations': bound + 1,
            'evaluation_sha256': evaluations.hexdigest()}


def verify_gauge_and_structure(vs):
    # Independently match the ungauged and gauged signed polynomial rows,
    # including every destination outside the finite core.
    for u in vs:
        converted = {(v, 2*e + gauge(v) - gauge(u)): c
                     for (v, e), c in row(u, False).items()}
        require(converted == row(u, True), 'raw/gauged row mismatch')
    expected_E = {((0, 2), 8): 1, ((3, 2), 9): 1,
                  ((1, 3), 5): 1, ((1, 3), 7): 1, ((4, 0), 12): -1}
    require(row(E) == expected_E, 'exceptional signed row mismatch')
    return len(vs)


def structural_bounds(vs, ad, p):
    b = c = tail = F(0)
    for height in range(1, 23):
        for x in range(height + 1):
            u = (x, height - x)
            if u == A or (x + 2*(height - x)) % 3 != 1:
                continue
            terms = row(u)
            require(all(abs(sum(v) - height) <= 3 for v, _ in terms),
                    'three-step height change exceeded three')
            inside = sum((abs(a)*Z_RADIUS**e for (v, e), a in terms.items()
                          if sum(v) <= H), F(0))
            outside = sum((abs(a)*Z_RADIUS**e for (v, e), a in terms.items()
                           if sum(v) > H), F(0))
            if height <= H:
                b = max(b, outside)
            else:
                c = max(c, inside)
                tail = max(tail, outside)
            if height > H + 3:
                require(inside == 0, 'far row unexpectedly reaches core')
            if height >= 3:
                require(sum(abs(a) for a in terms.values()) <= 27,
                        'three-step path count exceeded 27')
                require(all(e >= 3*height - 6 for _, e in terms),
                        'three-step exponent lower bound failed')
    universal_tail = 27*Z_RADIUS**(3*23 - 6)
    tail = max(tail, universal_tail)
    require(b < F(27, 1000), 'B-tail bound failed')
    require(c < F(21, 1000), 'C-tail bound failed')
    require(tail < F(1, 50), 'D-tail bound failed')
    n = len(vs)
    adj_bound = max(sum((sum((abs(a)*Z_RADIUS**e for e, a in
                              enumerate(ad['adjugate'][i*n + j])), F(0))
                         for j in range(n)), F(0)) for i in range(n))
    require(adj_bound < F(63, 10), 'adjugate row bound failed')
    derivative = sum((e*abs(a)*R**(e - 1) for e, a in enumerate(p) if e), F(0))
    require(derivative < 24, 'polynomial derivative bound failed')
    require(R < Z_RADIUS**2, 'q circle not inside z majorant disk')
    return {'B_exact_row_majorant': str(b), 'C_exact_row_majorant': str(c),
            'D_exact_row_majorant': str(tail),
            'universal_tail_from_height_23': str(universal_tail),
            'adjugate_exact_row_majorant': str(adj_bound),
            'derivative_exact_coefficient_majorant': str(derivative)}


def rational_nodes(m):
    require(type(m) is int and m > 0, 'invalid rational mesh size')
    t = 2*m
    for quadrant in range(4):
        for j in range(m):
            s = 2*j + 1
            a = R.numerator*(t*t - s*s)
            b = R.numerator*2*s*t
            d = R.denominator*(t*t + s*s)
            for _ in range(quadrant):
                a, b = -b, a
            # No reduction is necessary: the common denominator stays positive.
            verify_node_on_circle(a, b, d)
            yield a, b, d


def verify_node_on_circle(a, b, d):
    require(d > 0 and (a*a + b*b)*R.denominator**2 == d*d*R.numerator**2,
            'rational mesh node is off circle')


def evaluate_complex_integer(p, a, b, d):
    """Return U,V,D with P((a+ib)/d)=(U+iV)/D, without gcds."""
    require(d > 0, 'nonpositive complex denominator')
    real, imag, denominator = p[-1], 0, 1
    for coefficient in reversed(p[:-1]):
        denominator *= d
        real, imag = (real*a - imag*b + coefficient*denominator,
                      real*b + imag*a)
    return real, imag, denominator


def verify_node_value(value, minimum=F(1, 25)):
    x, y, d = value
    require(d > 0, 'nonpositive evaluated denominator')
    require((x*x + y*y)*minimum.denominator**2 >
            d*d*minimum.numerator**2, 'node modulus threshold failed')
    require(y != 0, 'polygon vertex has zero imaginary part')


def crossing(v, w):
    x1, y1, d1 = v
    x2, y2, d2 = w
    require(d1 > 0 and d2 > 0, 'crossing denominator nonpositive')
    require(y1 != 0 and y2 != 0, 'polygon vertex has zero imaginary part')
    if sign(y1) == sign(y2):
        return None
    # x_intersection=(x1*y2-x2*y1)/(y2*d1-y1*d2).
    numerator = x1*y2 - x2*y1
    denominator = y2*d1 - y1*d2
    require(numerator != 0 and denominator != 0, 'polygon edge meets origin')
    real_sign = sign(numerator)*sign(denominator)
    return (1 if y1 < 0 else -1), real_sign


def polygon_winding(values, expected=1):
    total = 0
    crossings = []
    for j, v in enumerate(values):
        result = crossing(v, values[(j + 1) % len(values)])
        if result is None:
            continue
        direction, real_sign = result
        if real_sign > 0:
            total += direction
        crossings.append({'edge_index': j, 'direction': 'up' if direction > 0 else 'down',
                          'real_ray': 'positive' if real_sign > 0 else 'negative'})
    require(total == expected, 'polygon winding count failed')
    return total, crossings


def verify_circle(p, m=MESH_PER_QUADRANT):
    # Analytic proof: every rational parametrization arc has angle <=2/m.
    arc_bound = 24*R*F(2, m)
    require(arc_bound < F(3, 125), 'mesh too coarse for certified arc bound')
    circle_bound = F(1, 25) - arc_bound
    require(circle_bound > F(2, 125), 'circle lower bound inadequate')
    digest = hashlib.sha256()
    values = []
    # A modest rational lower bound on all squared moduli, found by exact floor.
    squared_modulus_floor = None
    floor_scale = 10**12
    for index, (a, b, d) in enumerate(rational_nodes(m)):
        value = evaluate_complex_integer(p, a, b, d)
        verify_node_value(value)
        real, imag, denominator = value
        floor_ = floor_scale*(real*real + imag*imag)//(denominator*denominator)
        squared_modulus_floor = floor_ if squared_modulus_floor is None else min(
            squared_modulus_floor, floor_)
        # Hex integers avoid any interpreter decimal-digit conversion limit.
        digest.update((':'.join(format(v, 'x') for v in
                                (index, a, b, d, real, imag, denominator)) + '\n').encode('ascii'))
        values.append(value)
    require(len(values) == 4*m, 'incomplete rational mesh')
    winding, crossings = polygon_winding(values)
    return {'mesh_per_quadrant': m, 'mesh_points': len(values),
            'mesh_parameters': 'u_j=(2j+1)/(2M); q_j=R*((1-u_j^2)+2*i*u_j)/(1+u_j^2)',
            'angular_gap_bound': str(F(2, m)),
            'node_modulus_strict_lower': '1/25',
            'minimum_squared_node_modulus_lower': str(F(squared_modulus_floor, floor_scale)),
            'arc_image_variation_strict_upper': str(arc_bound),
            'circle_modulus_strict_lower': str(circle_bound),
            'conservative_circle_modulus_strict_lower': '2/125',
            'node_and_value_sha256': digest.hexdigest(),
            'positive_real_ray_winding': winding, 'ray_crossings': crossings}


def run(data_dir):
    poly_path = data_dir/'N_H8.json'
    ad_path = data_dir/'adjugate_H8.json'
    poly_data = json.loads(poly_path.read_text())
    ad = json.loads(ad_path.read_text())
    p, vs = validate_data(poly_data, ad)
    verify_gauge_and_structure(vs)
    matrix = polynomial_matrix(vs, True)
    verify_adjugate(matrix, ad)
    determinant = verify_genuine_determinant(polynomial_matrix(vs, False), p)
    bounds = structural_bounds(vs, ad, p)
    circle = verify_circle(p)
    delta = F(27, 1000)*F(21, 1000)/(1 - F(1, 50))
    kappa = F(63, 10)/F(2, 125)
    contraction = kappa*delta
    require(contraction < F(23, 100), 'Schur homotopy contraction failed')
    stronger_kappa = F(63, 10)/F(circle['circle_modulus_strict_lower'])
    return {'status': 'PASS', 'arithmetic': 'Python standard-library exact integers and fractions',
            'finite_height': H, 'finite_dimension': len(vs), 'N8_degree': len(p) - 1,
            'q_circle_radius': str(R), 'z_majorant_radius': str(Z_RADIUS),
            'input_sha256': {path.name: hashlib.sha256(path.read_bytes()).hexdigest()
                             for path in (poly_path, ad_path)},
            'genuine_determinant': determinant,
            'exact_structural_bounds': bounds, 'rational_circle': circle,
            'Schur': {'B_strict_upper': '27/1000', 'C_strict_upper': '21/1000',
                      'D_strict_upper': '1/50', 'adjugate_strict_upper': '63/10',
                      'correction_strict_upper': str(delta),
                      'inverse_strict_upper': str(kappa),
                      'contraction_strict_upper': str(contraction),
                      'stronger_inverse_strict_upper': str(stronger_kappa),
                      'stronger_contraction_strict_upper': str(stronger_kappa*delta)},
            'conclusion': 'The full Fredholm numerator N(q) has exactly one zero, counted with multiplicity, in |q|<63/100 and no boundary zero. It is simple and real. Its positive location and denominator noncancellation are separate certificates.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--data-dir', type=Path, default=Path(__file__).resolve().parent.parent/'data')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    text = json.dumps(run(args.data_dir), indent=2, sort_keys=True) + '\n'
    if args.output:
        args.output.write_text(text)
    print(text, end='')


if __name__ == '__main__':
    main()
