#!/usr/bin/env python3
"""Independent inert-source audit of the fixed auxiliary-ordinate theorem."""
import argparse
import hashlib
import json
from pathlib import Path

AUTHOR = {
    'py': '9d8ea463330b31dea1af8187784981b576c932a3799ca45a5dabfe2ea0bc2c94',
    'json': '8101345c3c6588539fe56f340322ba573e66ce66b978db7da8154781c23547f8',
    'md': '9cc0fc5f3d9f72dd3fc150c1253cb038fef1eb0666dc72b1096ed86c85481b53',
}
STEM = 'complete84_auxiliary_ordinate_absorption'

def require(ok, message):
    if not ok:
        raise ValueError(message)

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'))

def read(path):
    def pairs(items):
        result = {}
        for key, value in items:
            require(key not in result, 'duplicate JSON key')
            result[key] = value
        return result
    def reject(value):
        raise ValueError('noninteger JSON: ' + value)
    return json.loads(path.read_text(), object_pairs_hook=pairs,
                      parse_float=reject, parse_constant=reject)

# Integer sparse polynomials, using sorted tuples of variable names.
def constant(c):
    return {(): c} if c else {}

def variable(name):
    return {(name,): 1}

def plus(p, q, sign=1):
    out = dict(p)
    for monomial, coeff in q.items():
        out[monomial] = out.get(monomial, 0) + sign * coeff
    return {m: c for m, c in out.items() if c}

def times(p, q):
    out = {}
    for m, c in p.items():
        for n, d in q.items():
            key = tuple(sorted(m + n))
            out[key] = out.get(key, 0) + c * d
    return {m: c for m, c in out.items() if c}

def product(*ps):
    out = constant(1)
    for p in ps:
        out = times(out, p)
    return out

def square(p):
    return times(p, p)

def serial(p):
    return [[list(m), c] for m, c in sorted(p.items())]

def build(root, author_root):
    for ext, expected in AUTHOR.items():
        require(digest(author_root / (STEM + '.' + ext)) == expected, 'author pin ' + ext)
    report = read(author_root / (STEM + '.json'))
    require(report['source_sha256'] == AUTHOR['py'], 'author source binding')
    dependency_pins = {}
    for key in ['pins', 'authenticated_transitive_pins']:
        for name, expected in report[key].items():
            require(digest(root / name) == expected, 'dependency pin ' + name)
            if name in dependency_pins:
                require(dependency_pins[name] == expected, 'overlapping pin')
            dependency_pins[name] = expected
    packet = read(root / 'complete84_scaled_strong_output.json')['packet']
    rows, free = packet['source'], packet['free']
    require(rows == report['authenticated_parent_source'], 'entire author source')
    require(len(rows) == 84 and len(free) == len(set(free)) == 25, 'source sizes')
    defs = {}
    dependencies = {name: {name} for name in free}
    for name, op, left, right in rows:
        require(name not in dependencies and op in ['+', '-', '*'], 'SSA opcode')
        deps = set()
        for value in [left, right]:
            require(type(value) is int or type(value) is str and value in dependencies, 'paid topology')
            if type(value) is str:
                deps.update(dependencies[value])
        dependencies[name] = deps
        defs[name] = [op, left, right]
    omitted = {'auxiliary_quotient', 'y_aux'}
    previous_omitted = omitted | {'i', 'f'}
    outside = [r[0] for r in rows if not dependencies[r[0]] & omitted]
    old = [r[0] for r in rows if not dependencies[r[0]] & previous_omitted]
    supplied = [name for name in free if name not in omitted]
    require(outside == report['census']['computed_in_source_order'] and len(outside) == 70, 'computed 70')
    require(supplied == report['census']['free_values'] and len(supplied) == 23, 'supplied 23')
    require(old == report['census']['previous_computed'] and len(old) == 64, 'old 64')
    added = [name for name in outside if name not in old]
    require(added == ['L16', 'auxiliary_R_f2', 'aux_coefficient_root', 'R16', 'scaled_f_square', 'norm_strong'], 'six added')
    require([r[0] for r in rows if 'y_aux' in r[2:]] == ['aux_y2'], 'sole y consumer')
    require(defs['aux_y2'] == ['*', 'y_aux', 'y_aux'], 'literal y square')

    # A smaller independently selected cut interface: exactly eight actual
    # values, all independent of all four auxiliary coordinates. Recursively
    # expand every ancestor of the output until these paid values are reached.
    factors = ['norm_first', 'norm_main', 'norm_input', 'norm_index', 'norm_transport']
    cuts = ['A', 'R10a', 'r_lhs'] + factors
    require(all(not dependencies[c] & previous_omitted for c in cuts), 'cut independence')
    visited = set()
    def evaluate(y_value):
        env = {name: variable(name) for name in free + cuts}
        env['y_aux'] = y_value
        def value(name):
            if type(name) is int:
                return constant(name)
            if name in env:
                return env[name]
            op, a, b = defs[name]
            a, b = value(a), value(b)
            env[name] = times(a, b) if op == '*' else plus(a, b, 1 if op == '+' else -1)
            visited.add(name)
            return env[name]
        return value(packet['output'])
    D, c, R, i, f, T, y = map(variable, ['A', 'R10a', 'r_lhs', 'i', 'f', 'auxiliary_quotient', 'y_aux'])
    p5 = product(*(variable(n) for n in factors))
    V = plus(plus(product(c, T, f), c, -1), times(R, square(f)), -1)
    S2 = square(product(D, i, c, c))
    strong = plus(times(D, square(f)), S2, -1)
    norm = plus(times(S2, square(V)), times(plus(S2, constant(1), -1), square(y)), -1)
    expected = plus(product(p5, norm, strong), D, -1)
    positive = evaluate(y)
    require(positive == expected == evaluate(times(constant(-1), y)), 'literal all-ring evenness and full factor identity')
    zero = evaluate({})
    zero_expected = times(D, plus(product(square(D), square(i), c, c, c, c, square(V), p5,
                                        plus(square(f), product(D, square(i), c, c, c, c), -1)), constant(1), -1))
    require(zero == zero_expected, 'zero-y contraction')
    require(len(positive) == 17 and len(zero) == 13, 'coefficient counts')
    # The literal positive discriminant path does not use any norm equation.
    for name, value in {
        'q': ['+', 'repunit', 1], 'repunit': ['*', 'Bm1', 'Jrep'],
        'wn2': ['*', 'w', 'q'], 'sn2': ['*', 's', 'n2'],
        'n2': ['*', 'Lbig', 'q'], 'Lbig': ['*', 'q', 'q'],
        'UM': ['*', 'wn2', 'sn2'], 'R12': ['+', 'UM', 'sn2'],
        'a_square': ['*', 'R12', 'R12'], 'a4': ['*', 4, 'R12'],
        'a4m5': ['+', 'a4', 3], 'A': ['+', 'a_square', 'a4m5'],
        'gamma_sum': ['+', 'rho', 'sigma'],
        'odd_index': ['+', 'scaled_t', 'inner_bits'],
        'scaled_t': ['*', 'twice_cell_bits', 'x'],
    }.items():
        require(defs[name] == value, 'positive boundary ' + name)

    # Independent formal recurrence check over Z[A], not evaluations at A.
    A = variable('parameter'); one = constant(1); twoA = times(constant(2), A)
    psi = [{}, one]
    chi = [one, A]
    for n in range(2, 26):
        psi.append(plus(times(twoA, psi[-1]), psi[-2], -1))
        chi.append(plus(times(twoA, chi[-1]), chi[-2], -1))
    def odd_sequence(z):
        seq = [one, plus(times(constant(4), z), constant(3), -1)]
        for _ in range(2, 13):
            seq.append(plus(times(plus(times(constant(4), z), constant(2), -1), seq[-1]), seq[-2], -1))
        return seq
    negative = odd_sequence(plus(one, square(A), -1))
    positive_c = odd_sequence(square(A))
    for m in range(13):
        require(negative[m] == times(constant((-1) ** m), psi[2*m+1]), 'formal odd psi identity')
        require(times(A, positive_c[m]) == chi[2*m+1], 'formal odd chi quotient')
    z, w = variable('z'), variable('w'); disc = plus(square(A), one, -1)
    zp = plus(times(A, z), times(disc, w), -1)
    wp = plus(times(A, w), z, -1)
    require(plus(square(zp), times(disc, square(wp)), -1) == plus(square(z), times(disc, square(w)), -1), 'formal descent norm preservation')
    return {'status': 'PASS', 'source_sha256': digest(Path(__file__)), 'author_pins': AUTHOR,
            'dependency_pins': dependency_pins, 'full_source_rows': len(rows), 'computed': outside,
            'supplied': supplied, 'added_computed': added, 'source_cut_interface': cuts,
            'literal_expanded_rows': [r for r in rows if r[0] in visited],
            'full_polynomial_coefficients': serial(positive), 'zero_y_coefficients': serial(zero),
            'formal_odd_index_identities': 26, 'formal_descent_norm_identity': True,
            'scope': 'Inert source identities and exact finite symbolic corroboration; quantified inequalities reviewed in companion; no predecessor execution or compiler-zero fixtures'}

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--author-root', type=Path, required=True)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--output', type=Path)
    group.add_argument('--expect', type=Path)
    args = parser.parse_args()
    result = build(args.root, args.author_root)
    if args.output:
        with args.output.open('x') as stream:
            stream.write(json.dumps(result, sort_keys=True, indent=2) + '\n')
    else:
        require(canonical(result) == canonical(read(args.expect)), 'exact typed receipt replay')
    print('PASS: 84 source rows; 70+23 census; full 17-term/even and 13-term zero-y identities')

if __name__ == '__main__':
    main()
