#!/usr/bin/env python3
"""Emit literal ordinary local polynomials and independently count their ASTs.
No external executable source is imported. Baseline source files are evidence only.
"""

def require(condition, message='validation failure'):
    if not condition:
        raise RuntimeError(message)
from pathlib import Path
import hashlib, json
from itertools import product
import sympy as sp
import argparse
_parser=argparse.ArgumentParser(description=__doc__)
_parser.add_argument('--check', action='store_true', help='Verify sealed JSON artifacts without modifying them')
CHECK_ONLY=_parser.parse_args().check
HERE = Path(__file__).resolve().parent

def save_json(path, value):
    data=json.dumps(value, indent=2)+'\n'
    if CHECK_ONLY:
        require(path.is_file(), 'missing sealed artifact: '+str(path))
        require(path.read_text()==data, 'sealed artifact differs: '+str(path))
    else:
        path.write_text(data)

def A(x, y):
    return ['+', x, y]

def S(x, y):
    return ['-', x, y]

def M(x, y):
    return ['*', x, y]

def sq(x):
    return M(x, x)

def sum0(xs):
    result = 0
    for x in reversed(xs):
        result = A(x, result)
    return result

def treeops(e):
    return 0 if not isinstance(e, list) else 1 + treeops(e[1]) + treeops(e[2])

def dagops(e):
    seen = set()

    def walk(x):
        if not isinstance(x, list):
            return
        walk(x[1])
        walk(x[2])
        seen.add(json.dumps(x, separators=(',', ':')))
    walk(e)
    return len(seen)

def sym(e):
    if isinstance(e, str):
        return sp.Symbol(e)
    if isinstance(e, int):
        return sp.Integer(e)
    x, y = (sym(e[1]), sym(e[2]))
    return {'+': lambda: x + y, '-': lambda: x - y, '*': lambda: x * y}[e[0]]()

def ev(e, v):
    if isinstance(e, str):
        return v[e]
    if isinstance(e, int):
        return e
    x, y = (ev(e[1], v), ev(e[2], v))
    return {'+': lambda: x + y, '-': lambda: x - y, '*': lambda: x * y}[e[0]]()

def render(e):
    if not isinstance(e, list):
        return str(e)
    return '(' + render(e[1]) + ' ' + e[0] + ' ' + render(e[2]) + ')'

def pair_terms(z='z', a='a', b='b', t='t', s='s'):
    boolean = M(t, S(t, 1))
    branch = A(S(S(a, b), s), M(t, A(M(2, s), 1)))
    shell = A(S(M(4, S(S(z, a), b)), sq(A(A(a, b), s))), t)
    return ([boolean, sq(branch), sq(shell)], (boolean, branch, shell))

def pred_term(n='n', p='p', extras=()):
    d = S(S(n, p), 1)
    norms = [sq(n), sq(p)] + [sq(x) for x in extras]
    norm = norms[0]
    for x in norms[1:]:
        norm = A(norm, x)
    return M(sq(d), norm)
gadgets = []

def add(name, inputs, aux, terms, meaning, degree):
    e = sum0(terms)
    variables = inputs + aux
    p = sp.Poly(sp.expand(sym(e)), *[sp.Symbol(x) for x in variables])
    require(p.total_degree() == degree, 'validation condition failed at authored source line 57')
    terms_json = [{'coefficient': str(c), 'powers': list(m)} for m, c in p.terms()]
    data = dict(name=name, domain='all visible and auxiliary variables are natural numbers, including zero', inputs=inputs, auxiliaries=aux, auxiliary_count=len(aux), total_variables=len(variables), meaning=meaning, expression=e, formula=render(e), tree_binary_operations=treeops(e), shared_dag_binary_operations=dagops(e), degree=p.total_degree(), monomials=len(p.terms()), expanded_terms=terms_json)
    save_json(HERE / (name + '.json'), data)
    gadgets.append(data)
    return data
terms, rows = pair_terms()
add('max_square_pair_quartic', ['z', 'a', 'b'], ['t', 's'], terms, 'z = Nat.pair(a,b): b*b+a if a<b, otherwise a*a+a+b', 4)
add('max_square_pair_sos_quartic', ['z', 'a', 'b'], ['t', 's'], [sq(rows[0]), terms[1], terms[2]], 'same exact max-square pairing graph; strict sum of three quadratic-row squares', 4)
add('unpair_left_quartic', ['z', 'a'], ['b', 't', 's'], terms, 'a = first component of Nat.unpair(z)', 4)
add('unpair_right_quartic', ['z', 'b'], ['a', 't', 's'], terms, 'b = second component of Nat.unpair(z)', 4)
T = S(sq(A(A('a', 'b'), 's')), M(4, S(S('z', 'a'), 'b')))
branch = A(S(S('a', 'b'), 's'), M(T, A(M(2, 's'), 1)))
add('max_square_pair_sextic', ['z', 'a', 'b'], ['s'], [M(T, S(T, 1)), sq(branch)], 'same exact max-square pairing graph, with selector eliminated', 6)
add('predecessor_quartic', ['n', 'p'], [], [pred_term()], 'p = max(n-1,0)', 4)
for side in ('left', 'right'):
    add('tree_' + side + '_quartic', ['n', 'a' if side == 'left' else 'b'], ['p', 'b' if side == 'left' else 'a', 't', 's'], pair_terms('p')[0] + [pred_term()], f"{('a' if side == 'left' else 'b')} = {side} component of Nat.unpair(max(n-1,0)); right also equals actual listTail", 4)
add('if_zero_quartic', ['n', 'a', 'b', 'c'], ['s'], [sq(M('n', S('c', 'b'))), sq(M(S('c', 'a'), S(S('n', 's'), 1)))], 'c = a if n=0, else b', 4)
add('zero_test_quartic', ['n', 'bit'], ['s'], [sq(M('n', 'bit')), sq(M(S('bit', 1), S(S('n', 's'), 1)))], 'bit = 1 if n=0, else 0', 4)
add('list_head_quartic', ['n', 'c'], ['p', 'a', 'b', 't', 's'], pair_terms('p')[0] + [pred_term(extras=('c',)), sq(M('n', S(S('c', 'a'), 1)))], 'c = 0 if n=0, else first(Nat.unpair(n-1))+1', 4)
a, b, z, t, s, n, p, c = sp.symbols('a b z t s n p c')
f0 = t * (t - 1)
f1 = a - b - s + t * (2 * s + 1)
f2 = 4 * (z - a - b) - (a + b + s) ** 2 + t
require(sp.expand(f1.subs({t: 0, a: b + s})) == 0, 'validation condition failed at authored source line 80')
require(sp.expand(f1.subs({t: 1, b: a + s + 1})) == 0, 'validation condition failed at authored source line 81')
require(sp.expand(f2.subs({t: 0, a: b + s}) - 4 * (z - ((b + s) ** 2 + (b + s) + b))) == 0, 'validation condition failed at authored source line 82')
require(sp.expand(f2.subs({t: 1, b: a + s + 1}) - 4 * (z - ((a + s + 1) ** 2 + a))) == 0, 'validation condition failed at authored source line 83')
require(sp.expand((n * (p + 1 - n)) ** 2 + (p * (p + 1 - n)) ** 2 - (n - p - 1) ** 2 * (n * n + p * p)) == 0, 'validation condition failed at authored source line 84')
require(sp.expand((n - p - 1) ** 2 * (n * n + p * p) + (c * (n - p - 1)) ** 2 - (n - p - 1) ** 2 * (n * n + p * p + c * c)) == 0, 'validation condition failed at authored source line 85')
pair6 = next((x for x in gadgets if x['name'] == 'max_square_pair_sextic'))
require(sp.expand(sym(pair6['expression']) - sym(gadgets[0]['expression']).subs(t, (a + b + s) ** 2 - 4 * (z - a - b))) == 0, 'validation condition failed at authored source line 87')

def pair(x, y):
    return y * y + x if x < y else x * x + x + y

def pairpoly(z, a, b, t, s):
    return t * (t - 1) + (a - b - s + t * (2 * s + 1)) ** 2 + (4 * (z - a - b) - (a + b + s) ** 2 + t) ** 2

def p6(z, a, b, s):
    T = (a + b + s) ** 2 - 4 * (z - a - b)
    return T * (T - 1) + (a - b - s + T * (2 * s + 1)) ** 2
counts = {}
k = 0
for a, b, z, t, s in product(range(9), range(9), range(101), range(5), range(13)):
    P = pairpoly(z, a, b, t, s)
    require(P >= 0, 'validation condition failed at authored source line 99')
    if P == 0:
        require(z == pair(a, b), 'validation condition failed at authored source line 100')
    k += 1
counts['quartic_pair_soundness_assignments'] = k
for a, b in product(range(65), repeat=2):
    t = 0 if a >= b else 1
    s = a - b if a >= b else b - a - 1
    z = pair(a, b)
    require(pairpoly(z, a, b, t, s) == 0 and p6(z, a, b, s) == 0, 'validation condition failed at authored source line 105')
counts['pair_unbounded_formula_completeness_samples'] = 65 ** 2
k = 0
for a, b, z, s in product(range(8), range(8), range(81), range(12)):
    P = p6(z, a, b, s)
    require(P >= 0, 'validation condition failed at authored source line 109')
    if P == 0:
        require(z == pair(a, b), 'validation condition failed at authored source line 110')
    k += 1
counts['sextic_pair_soundness_assignments'] = k
k = 0
for n, a, b, c, s in product(range(8), repeat=5):
    P = (n * (c - b)) ** 2 + ((c - a) * (n - s - 1)) ** 2
    if P == 0:
        require(c == (a if n == 0 else b), 'validation condition failed at authored source line 116')
    k += 1
counts['conditional_soundness_assignments'] = k
for n, a, b in product(range(20), repeat=3):
    c = a if n == 0 else b
    s = max(n - 1, 0)
    require((n * (c - b)) ** 2 + ((c - a) * (n - s - 1)) ** 2 == 0, 'validation condition failed at authored source line 121')
counts['conditional_completeness_samples'] = 20 ** 3
for n, p in product(range(100), repeat=2):
    require(((n - p - 1) ** 2 * (n * n + p * p) == 0) == (p == max(n - 1, 0)), 'validation condition failed at authored source line 124')
counts['predecessor_assignments'] = 100 ** 2
for n, bit, s in product(range(20), repeat=3):
    P = (n * bit) ** 2 + ((bit - 1) * (n - s - 1)) ** 2
    if P == 0:
        require(bit == (1 if n == 0 else 0), 'validation condition failed at authored source line 128')
counts['zero_test_soundness_assignments'] = 20 ** 3
k = 0
for a, b, n, c in product(range(16), range(16), range(257), range(18)):
    p = pair(a, b)
    t = 0 if a >= b else 1
    s = a - b if a >= b else b - a - 1
    P = pairpoly(p, a, b, t, s) + (n - p - 1) ** 2 * (n * n + p * p + c * c) + (n * (c - a - 1)) ** 2
    if P == 0:
        require(c == (0 if n == 0 else a + 1) and p == max(n - 1, 0), 'validation condition failed at authored source line 135')
    k += 1
counts['list_head_decoded_soundness_assignments'] = k
for a, b in product(range(65), repeat=2):
    p = pair(a, b)
    n = p + 1
    c = a + 1
    t = 0 if a >= b else 1
    s = a - b if a >= b else b - a - 1
    require(pairpoly(p, a, b, t, s) + (n - p - 1) ** 2 * (n * n + p * p + c * c) + (n * (c - a - 1)) ** 2 == 0, 'validation condition failed at authored source line 140')
require(pairpoly(0, 0, 0, 0, 0) + (-1) ** 2 * 0 + 0 == 0, 'validation condition failed at authored source line 141')
counts['list_head_completeness_samples'] = 65 ** 2 + 1
summary = [{k: g[k] for k in ['name', 'auxiliary_count', 'total_variables', 'degree', 'tree_binary_operations', 'shared_dag_binary_operations', 'monomials']} for g in gadgets]
report = {'status': 'PASS', 'scope': 'Symbolic polynomial identities, exact AST/expansion/count audits, finite controls. Universal correctness is proved in LOCAL_GADGET_PROOFS.md, not machine-checked in Lean.', 'checks': counts, 'total_numeric_controls': sum(counts.values()), 'gadgets': summary}
save_json(HERE / 'LOCAL_CHECK_RESULTS.json', report)
print(json.dumps(report, indent=2))
