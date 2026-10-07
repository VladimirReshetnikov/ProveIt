#!/usr/bin/env python3
"""Independent standard-library rational checks supplementing the main verifier."""
import ast
import argparse
import hashlib
import json
from fractions import Fraction
from pathlib import Path
import certify_rational_circle as c


def check(condition, message):
    if not condition:
        raise ArithmeticError(message)


def fraction_determinant(matrix):
    """Ordinary rational Gaussian elimination, independent of Bareiss recurrence."""
    a = [[Fraction(x) for x in row] for row in matrix]
    n = len(a)
    determinant = Fraction(1)
    for k in range(n):
        pivot = next((j for j in range(k, n) if a[j][k]), None)
        if pivot is None:
            return Fraction(0)
        if pivot != k:
            a[k], a[pivot] = a[pivot], a[k]
            determinant = -determinant
        diagonal = a[k][k]
        determinant *= diagonal
        for i in range(k + 1, n):
            multiplier = a[i][k] / diagonal
            for j in range(k + 1, n):
                a[i][j] -= multiplier * a[k][j]
            a[i][k] = Fraction(0)
    return determinant


def direct_complex_power_sum(p, node):
    """Forward power summation in Fraction pairs, not reverse integer Horner."""
    a, b, d = node
    z = (Fraction(a, d), Fraction(b, d))
    power = (Fraction(1), Fraction(0))
    total = (Fraction(0), Fraction(0))
    for coefficient in p:
        total = (total[0] + coefficient * power[0],
                 total[1] + coefficient * power[1])
        power = (power[0] * z[0] - power[1] * z[1],
                 power[0] * z[1] + power[1] * z[0])
    return total


def fraction_ray_winding(values, transform):
    """Direct segment interpolation in rational coordinates."""
    total = 0
    crossings = []
    for i, (v, w) in enumerate(zip(values, values[1:] + values[:1])):
        x1, y1 = transform(Fraction(v[0], v[2]), Fraction(v[1], v[2]))
        x2, y2 = transform(Fraction(w[0], w[2]), Fraction(w[1], w[2]))
        check(y1 and y2, 'review ray meets a vertex')
        if (y1 > 0) == (y2 > 0):
            continue
        t = -y1 / (y2 - y1)
        intercept = (1 - t) * x1 + t * x2
        check(intercept != 0, 'review polygon edge meets zero')
        if intercept > 0:
            direction = 1 if y1 < y2 else -1
            total += direction
            crossings.append([i, direction])
    return {'winding': total, 'crossings': crossings}


def run(data_dir):
    root = Path(__file__).resolve().parent
    sources = ['certify_rational_circle.py', 'test_rational_circle.py']
    hashes = {name: hashlib.sha256((root / name).read_bytes()).hexdigest() for name in sources}
    data = json.loads((data_dir / 'N_H8.json').read_text())
    ad = json.loads((data_dir / 'adjugate_H8.json').read_text())
    p, vs = c.validate_data(data, ad)
    raw = c.polynomial_matrix(vs, False)
    degrees = [max(e for cell in row for e in cell) for row in raw]
    check(sum(degrees) == 239, 'unexpected degree bound')
    for q in range(240):
        matrix = [[sum(coefficient * q**exponent for exponent, coefficient in cell.items())
                   for cell in row] for row in raw]
        check(fraction_determinant(matrix) == sum(a * q**k for k, a in enumerate(p)),
              'rational Gaussian determinant disagreement at ' + str(q))
    nodes = list(c.rational_nodes(c.MESH_PER_QUADRANT))
    for a, b, d in nodes:
        check(d > 0 and Fraction(a*a + b*b, d*d) == Fraction(63, 100)**2,
              'node circle membership')
    normalized = {(Fraction(a, d), Fraction(b, d)) for a, b, d in nodes}
    check(len(normalized) == 8192, 'repeated circle point')
    for v, w in zip(nodes, nodes[1:] + nodes[:1]):
        check(v[0] * w[1] - v[1] * w[0] > 0, 'nonpositive adjacent orientation')
    for quadrant in range(4):
        for a, b, d in nodes[quadrant*2048:(quadrant+1)*2048]:
            for _ in range(quadrant):
                a, b = b, -a
            check(a > 0 and b > 0, 'point outside its prescribed open quadrant')
    values = [c.evaluate_complex_integer(p, *node) for node in nodes]
    selections = sorted({0, 1, 1024, 2047, 2048, 4095, 4096, 6143, 6144, 8191,
                         *[x for i in [673, 2092, 3193, 4095, 4673, 6056, 7177, 8191]
                           for x in (i, (i+1) % 8192)]})
    for i in selections:
        real, imag = direct_complex_power_sum(p, nodes[i])
        x, y, d = values[i]
        check((real, imag) == (Fraction(x, d), Fraction(y, d)), 'direct power sum disagreement')
    ray_results = {
        'positive_real': fraction_ray_winding(values, lambda x, y: (x, y)),
        'negative_real': fraction_ray_winding(values, lambda x, y: (-x, -y)),
        'diagonal': fraction_ray_winding(values, lambda x, y: (x+y, y-x)),
    }
    check(all(result['winding'] == 1 for result in ray_results.values()), 'independent ray count disagreement')
    check(any(edge == 8191 for edge, _ in ray_results['negative_real']['crossings']),
          'negative-ray check did not exercise the closing edge')
    syntax = {}
    for name in sources[:2]:
        tree = ast.parse((root / name).read_text())
        syntax[name] = {
            'removable_assertions': sum(isinstance(n, ast.Assert) for n in ast.walk(tree)),
            'float_literals': sum(isinstance(n, ast.Constant) and type(n.value) is float for n in ast.walk(tree)),
        }
        check(all(x == 0 for x in syntax[name].values()), 'inexact or removable construct')
    check(hashes == {name: hashlib.sha256((root / name).read_bytes()).hexdigest() for name in sources},
          'review sources changed during execution')
    result = {'status': 'PASS', 'source_sha256': hashes, 'rational_gaussian_determinants': 240,
              'degree_bound': sum(degrees), 'distinct_positive_order_nodes': len(nodes),
              'direct_power_sum_node_indices': selections, 'ray_results': ray_results,
              'source_syntax': syntax}
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--data-dir', type=Path, default=Path(__file__).resolve().parent.parent/'data')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    text = json.dumps(run(args.data_dir), sort_keys=True, indent=2)+'\n'
    if args.output:
        args.output.write_text(text)
    print(text, end='')


if __name__ == '__main__':
    main()
