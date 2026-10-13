"""Fixed inputs, complete source pins, and independent exact result replay."""
from fractions import Fraction as Q
from hashlib import sha256
from itertools import combinations
import json
from math import gcd
from pathlib import Path
from random import Random

from fastunknot.diagram import Diagram
from fastunknot.integer_codec import encoded_integer, json_safe
from fastunknot.normal_crushing_chain import verify_crushing_chain
from fastunknot.normal_crushing_search import verify_crushing_recognition
from tests.test_polynomial_exact_lp import determinant, normalized_vertices

ROOT = Path(__file__).resolve().parents[2]
PACKAGE = Path(__file__).resolve().parent
SEED = 2026101301
ARMS = ('bland', 'polynomial')
MASK = [[0, 0], [1, 0], [1, 2]]
CONFIG = dict(sector_method='transversal', tree_model='source',
    lp_strategy='envelope', reduce_vertices=True, max_tree_nodes=256,
    max_pivots=10000, max_anchors=10000, max_hitting_subsets=10000,
    max_ellipsoid_iterations=10000, max_feasibility_calls=10000,
    max_crushes=None)


def source_hashes():
    paths = list((ROOT/'fast/fastunknot').rglob('*.py'))
    paths += [p for p in PACKAGE.rglob('*') if p.is_file() and p.suffix in ('.py', '.md')]
    paths += [ROOT/'fast'/name for name in (
        'normal_orbit_research/fixtures.py', 'tests/test_polynomial_exact_lp.py',
        'tests/test_normal_crushing_search.py')]
    paths += [path for path in (ROOT/'fast/tests/__init__.py',
                              ROOT/'fast/normal_orbit_research/__init__.py') if path.exists()]
    return {str(path.relative_to(ROOT)): sha256(path.read_bytes()).hexdigest()
            for path in sorted(set(paths))}


def encode(value):
    return json.dumps(json_safe(value), sort_keys=True, separators=(',', ':')).encode()


def digest(value):
    return sha256(encode(value)).hexdigest()


def save(path, value):
    Path(path).write_text(json.dumps(json_safe(value), indent=2)+'\n')


def rational(value):
    if type(value) is Q:
        return value
    if type(value) is list:
        assert len(value) == 2
        a, b = map(encoded_integer, value)
        assert b > 0
        return Q(a, b)
    return Q(encoded_integer(value))


def pairs(values):
    return [[Q(v).numerator, Q(v).denominator] for v in values]


def rank(matrix, width):
    """Rank by exact minors, independent of every producer elimination helper."""
    for size in range(min(len(matrix), width), 0, -1):
        for rows in combinations(matrix, size):
            for columns in combinations(range(width), size):
                if determinant([[row[j] for j in columns] for row in rows]):
                    return size
    return 0


def check_lp(matrix, objective, answer, *, reduce_rows):
    """Original-row dual or positive vertex, support rank and full slack basis."""
    matrix = [list(map(rational, row)) for row in matrix]
    objective = list(map(rational, objective))
    n = len(objective)
    vertices = normalized_vertices(matrix, n)
    positive = {x for x in vertices if sum(c*a for c, a in zip(objective, x)) > 0}
    assert answer['status'] == ('POSITIVE' if positive else 'NONPOSITIVE')
    selected = answer['equation_rows']
    assert all(type(i) is int and 0 <= i < len(matrix) for i in selected)
    assert len(set(selected)) == len(selected)
    retained = [matrix[i] for i in selected]
    full_rank = rank(matrix, n)
    assert rank(retained, n) == full_rank
    if reduce_rows:
        assert len(selected) == full_rank
    else:
        assert selected == list(range(len(matrix)))
    if positive:
        x = tuple(map(rational, answer['x']))
        assert x in positive and len(x) == n and sum(x) == 1
        ray = list(map(encoded_integer, answer['primitive_x']))
        assert len(ray) == n and all(v >= 0 for v in ray) and any(ray)
        divisor = 0
        for v, a in zip(ray, x):
            divisor = gcd(divisor, v)
            assert Q(v, sum(ray)) == a
        assert divisor == 1
        assert all(sum(a*v for a, v in zip(row, x)) == 0 for row in matrix)
        assert sum(c*v for c, v in zip(objective, x)) == rational(answer['objective']) > 0
        support = [j for j, v in enumerate(x) if v]
        assert len(support)-rank([[row[j] for j in support] for row in matrix], len(support)) == 1
        inequalities = retained+[[-a for a in row] for row in retained]+[[Q(1)]*n]
        m, basis = len(inequalities), answer['basis']
        assert len(basis) == len(set(basis)) == m
        assert all(type(j) is int and 0 <= j < n+m for j in basis)
        assert set(support) <= set(basis)
        square = [[row[j] if j < n else Q(j-n == i) for j in basis]
                  for i, row in enumerate(inequalities)]
        assert determinant(square), 'singular original slack basis'
    else:
        y = list(map(rational, answer['y']))
        assert len(y) == len(matrix)
        assert all(sum(row[j]*v for row, v in zip(matrix, y)) >= c
                   for j, c in enumerate(objective))
    return sorted(vertices)


def small_cases():
    cases = [
        ('empty', [], []), ('zero_width', [[], []], []),
        ('orthant', [], [1, 1]), ('zero_cone', [[1, 1]], [1, 1]),
        ('positive_line', [[1, -1]], [1, 0]),
        ('negative_line', [[1, -1]], [1, -2]),
        ('rational_rows', [[Q(1, 2), Q(-1, 3)], [3, -2]], [1, 0]),
        ('rational_dual', [[Q(1, 7), Q(-1, 11)], [3, Q(-21, 11)]],
                          [Q(1, 13), Q(-1, 2)]),
        ('unsorted_pivots', [[0, 1, -1], [1, 0, -1]], [1, 0, 0]),
        ('three_rays', [[1, 1, -1]], [1, 1, 0]),
        ('four_dimensional_negative', [[1, 1, 1, 1]], [1, 0, 0, 0]),
    ]
    rng = Random(SEED)
    for i in range(4):
        cases.append(('random_'+str(i), [[rng.randrange(-2, 3) for _ in range(2)]],
                      [rng.randrange(-2, 3) for _ in range(2)]))
    return cases


def diagrams():
    return [('circle', Diagram.from_pd([])),
            ('trefoil', Diagram.from_braid(2, [1, 1, 1])),
            ('figure_eight', Diagram.from_braid(3, [1, -2, 1, -2]))]


def configs():
    return {arm: dict(CONFIG, lp_policy=arm) for arm in ARMS}


def verify_result(diagram, result):
    assert result['status'] in ('UNKNOT', 'KNOTTED')
    assert result['certificate']['status'] == result['status']
    assert verify_crushing_recognition(diagram, result['certificate'])
    assert verify_crushing_chain(diagram, result['certificate']['chain'])
    return True


def bounded_cases():
    return [
        ('three_dimensional_singleton',
         [[1, 0, 0], [-1, 0, 0], [0, 1, 0], [0, -1, 0], [0, 0, 1], [0, 0, -1]],
         [Q(1, 16), Q(-1, 16), 0, 0, 0, 0], [Q(1, 16), Q(0), Q(0)]),
        ('three_dimensional_gap', [[1, 1, 1], [-1, -1, -1]],
         [0, Q(-1, 16)], None),
    ]


def psd(matrix):
    return all(determinant([[matrix[i][j] for j in indices] for i in indices]) >= 0
               for k in range(1, len(matrix)+1) for indices in combinations(range(len(matrix)), k))


def root_leq(value, square, integer):
    """Exact value/sqrt(square) <= integer, including negative values."""
    if value >= 0:
        return integer >= 0 and value*value <= integer*integer*square
    return integer >= 0 or value*value >= integer*integer*square


def check_rounding(record):
    old, ideal, new = [list(map(lambda row: list(map(rational, row)), record[key]))
                       for key in ('old_shape', 'ideal_shape', 'new_shape')]
    rho, grid, floor = [rational(record[key]) for key in ('rho', 'grid', 'spectral_floor')]
    d = len(old)
    assert d == 3 and rho == Q(1, 100*d*d)
    assert type(record['step']) is int and record['step'] >= 0
    assert grid.numerator == 1 and grid.denominator & (grid.denominator-1) == 0
    assert all(new[i][j] == new[j][i] for i in range(d) for j in range(d))
    assert all(determinant([row[:k] for row in new[:k]]) > 0 for k in range(1, d+1))
    assert psd([[new[i][j]-(1+rho)**2*ideal[i][j] for j in range(d)] for i in range(d)])
    assert psd([[(1+rho)**3*ideal[i][j]-new[i][j] for j in range(d)] for i in range(d)])
    assert psd([[ideal[i][j]-(floor if i == j else 0) for j in range(d)] for i in range(d)])
    assert determinant(new) <= (1-Q(1, 4*d))**2*determinant(old)
    normal = list(map(rational, record['normal']))
    image = [sum(a*b for a, b in zip(row, normal)) for row in old]
    square = sum(a*b for a, b in zip(normal, image))
    assert square > 0
    for i in range(d):
        for j in range(d):
            assert ideal[i][j] == Q(d*d, d*d-1)*(old[i][j]-Q(2, d+1)*image[i]*image[j]/square)
        integer = (rational(record['old_center'][i])-rational(record['new_center'][i]))/grid
        assert integer.denominator == 1
        value = image[i]/((d+1)*grid)
        assert root_leq(value, square, integer.numerator)
        assert not root_leq(value, square, integer.numerator-1)
    assert d*grid*grid <= rho*rho*floor, 'center error exceeds proved ellipsoid norm allowance'


def fraction_tree(value):
    if type(value) is Q:
        return [value.numerator, value.denominator]
    if isinstance(value, dict):
        return {key: fraction_tree(item) for key, item in value.items()}
    if isinstance(value, (tuple, list)):
        return [fraction_tree(item) for item in value]
    return value
