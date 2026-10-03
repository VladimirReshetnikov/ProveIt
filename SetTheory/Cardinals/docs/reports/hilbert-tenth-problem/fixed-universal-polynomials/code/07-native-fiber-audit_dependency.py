#!/usr/bin/env python3
"""Portable independent audit of the pinned literal native block.

No upstream code is imported or executed. The input is JSON data only.
Default execution is read-only: it compares against DEPENDENCY-RECEIPT.json.
Use --write only to create or explicitly update that generated receipt.
All scientific checks remain active under Python's -O option.
"""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import sys
sys.dont_write_bytecode = True


class Polynomial:
    """Exact sparse multivariate Z-polynomial; monomials are sorted name tuples.

    Independent implementation for this release. No symbolic package is used.
    Zero coefficients are removed on every operation. Repeated variable names
    encode powers, so multiplication is concatenation followed by sorting.
    """
    __slots__ = ('terms',)

    def __init__(self, value=0):
        if isinstance(value, Polynomial):
            self.terms = value.terms.copy()
        elif type(value) is int:
            self.terms = {(): value} if value else {}
        elif type(value) is dict:
            self.terms = {m: c for m, c in value.items() if c}
        else:
            raise TypeError('polynomial coefficient must be an integer')

    @classmethod
    def variable(cls, name):
        return cls({(name,): 1})

    def __add__(self, other):
        out = self.terms.copy()
        for m, c in Polynomial(other).terms.items():
            out[m] = out.get(m, 0) + c
        return Polynomial(out)

    __radd__ = __add__

    def __neg__(self):
        return Polynomial({m: -c for m, c in self.terms.items()})

    def __sub__(self, other):
        return self + (-Polynomial(other))

    def __rsub__(self, other):
        return Polynomial(other) + (-self)

    def __mul__(self, other):
        out = {}
        for m, c in self.terms.items():
            for n, d in Polynomial(other).terms.items():
                monomial = tuple(sorted(m + n))
                out[monomial] = out.get(monomial, 0) + c*d
        return Polynomial(out)

    __rmul__ = __mul__

    def __pow__(self, exponent):
        if type(exponent) is not int or exponent < 0:
            raise ValueError('nonnegative integer exponent required')
        value, factor = Polynomial(1), self
        while exponent:
            if exponent & 1:
                value = value*factor
            factor = factor*factor
            exponent //= 2
        return value

    def __eq__(self, other):
        return self.terms == Polynomial(other).terms

    @property
    def free_symbols(self):
        return {v for monomial in self.terms for v in monomial}


def arithmetic_self_test():
    x, y = Polynomial.variable('x'), Polynomial.variable('y')
    require((x+y)**3 == x**3+3*x*x*y+3*x*y*y+y**3,
            'polynomial_engine', 'binomial cubic identity failed')
    require(((x-y)*(x+y)-x*x+y*y).terms == {},
            'polynomial_engine', 'exact zero cancellation failed')
    require((x-x+y).free_symbols == {'y'},
            'polynomial_engine', 'cancelled variable persisted')
    require((2*x*y+3*y*x).terms == {('x','y'):5},
            'polynomial_engine', 'commutative monomial merging failed')


ROOT = Path(__file__).resolve().parent
INPUT = ROOT / 'source' / 'native_blocks.json'
RECEIPT = ROOT / 'DEPENDENCY-RECEIPT.json'
PINNED_SHA256 = 'a3ef38c5a449040a817384d564da90a5b7a440d426997df8ae6acecc4d55d74f'
FREE = {'native__' + n for n in ('f', 'i', 'j', 'o', 'y_aux')}
SUPPLIED = {'native__' + n for n in (
    'F0', 'F1', 'F2', 'a', 'c', 'd', 'f', 'h', 'i', 'j', 'k', 'o',
    'r', 's', 'w', 'tau', 'eta', 'zeta', 'ga', 'y_aux', 'odd_half',
    'bound_beta',
)}
FIXTURES = ['incdec', 'zero3', 'nop', 'positive3']


class AuditError(RuntimeError):
    """A failed scientific, input-integrity, or replay check."""

    def __init__(self, code, message):
        super().__init__(message)
        self.code = code


def require(condition, code, message):
    # Intentionally not an assert: the audit must run with python -O too.
    if not condition:
        raise AuditError(code, message)


def audit_block(block):
    name = block['fixture']
    witness_list = block['auxiliaries']
    supplied = set(witness_list)
    require(len(witness_list) == len(supplied) == 22 and supplied == SUPPLIED,
            'witness_list', f'{name}: exact 22-coordinate supplied witness list mismatch')
    require(FREE <= supplied and len(supplied - FREE) == 17,
            'fixed_count', f'{name}: fixed/free coordinate partition mismatch')
    source = block['source']
    require(len(source) == 64, 'gate_count', f'{name}: expected exactly 64 gates')
    require(all(isinstance(g, list) and len(g) == 4 for g in source),
            'gate_shape', f'{name}: malformed source gate')
    require(all(isinstance(g[0], str) and g[1] in ('+', '-', '*') and
                all(isinstance(x, str) or type(x) is int for x in g[2:])
                for g in source), 'gate_type', f'{name}: invalid gate or operand type')
    outputs = {g[0] for g in source}
    require(len(outputs) == len(source), 'duplicate_output', f'{name}: duplicate gate output')
    require(not outputs & supplied, 'output_shadows_witness',
            f'{name}: a gate output shadows a supplied coordinate')
    # Declare every supplied coordinate even when a malformed source stops using it.
    # This keeps the independent expected formulas meaningful in mutation tests.
    leaves = {x for g in source for x in g[2:] if isinstance(x, str)} - outputs
    leaves |= supplied
    env = {v: Polynomial.variable(v) for v in leaves}
    deps = {v: {v} for v in leaves}
    seen = set(leaves)
    for target, op, lhs, rhs in source:
        require(target not in seen, 'duplicate_output', f'{name}: duplicate output {target}')
        require(all(not isinstance(x, str) or x in seen for x in (lhs, rhs)),
                'dag_order', f'{name}: DAG ordering failed at {target}')
        a, b = [env[x] if isinstance(x, str) else Polynomial(x) for x in (lhs, rhs)]
        if op == '+':
            env[target] = a + b
        elif op == '-':
            env[target] = a - b
        else:
            env[target] = a * b
        deps[target] = set().union(*(deps[x] if isinstance(x, str) else set()
                                    for x in (lhs, rhs)))
        seen.add(target)

    def e(symbol):
        return env['native__' + symbol]

    q, X, Y = e('q'), e('w') * e('q'), e('s') * e('q')
    E, delta = X * Y, e('a')**2 + 4 * e('a') + 3
    U = e('j') * e('c') - (2 * e('r') + 1)
    packed = e('F0') + q * e('F1') + q**2 * e('F2') + q**3 * e('F3')
    expected = [
        e('r') - packed,
        e('F0') + e('F1') + e('F2') + e('F3') + 1 - q,
        e('s') - (2 * e('odd_half') + 1),
        e('r') + e('bound_beta') - X,
        (E**2 + X) * (Y * e('k'))**2 - e('tau') * (e('tau') + 1),
        e('c') - Y * e('k') - e('eta'),
        e('k') - e('eta') - e('zeta'),
        e('k') - e('r') - 1 - e('h') * E,
        e('a') - Y * (X + 1),
        e('d') - X - e('a') * e('c') - e('ga') * (4 * e('a') + 3),
        e('d')**2 - 1 - delta * e('c')**2,
        (e('i') * e('c')**2)**2 - delta * (e('f')**2 - 1),
        (e('i') * e('c')**2)**2 * (U**2 - e('y_aux')**2) - (1 - e('y_aux')**2),
        U - (e('o') * e('f') - e('c')),
        e('F1') + e('F3') - e('padded_A'),
        e('F2') + e('F3') - e('padded_B'),
    ]
    comparisons = block['comparisons']
    require(len(expected) == len(comparisons) == 16,
            'comparison_count', f'{name}: expected exactly 16 comparisons')
    require(all(isinstance(pair, list) and len(pair) == 2 and
                all(isinstance(v, str) and v in env for v in pair)
                for pair in comparisons),
            'comparison_shape', f'{name}: malformed comparison or unknown register')
    incidence, audit_comparisons = {}, []
    for index, ((lhs, rhs), formula) in enumerate(zip(comparisons, expected), 1):
        literal = env[lhs] - env[rhs]
        require((literal - formula) == 0, 'residual_mismatch',
                f'{name}: comparison {index} residual mismatch')
        graph_free = (deps[lhs] | deps[rhs]) & FREE
        polynomial_free = {str(v) for v in literal.free_symbols} & FREE
        require(graph_free == polynomial_free, 'dependency_cancellation',
                f'{name}: comparison {index} graph/polynomial dependencies differ')
        incidence[index] = sorted(v.removeprefix('native__') for v in graph_free)
        audit_comparisons.append({
            'number': index, 'lhs': lhs, 'rhs': rhs,
            'free_five_dependencies': incidence[index],
            'expected_residual_verified': True,
        })
    expected_incidence = {n: [] for n in range(1, 17)}
    expected_incidence.update({12: ['f', 'i'], 13: ['i', 'j', 'y_aux'], 14: ['f', 'j', 'o']})
    require(incidence == expected_incidence, 'dependency_incidence',
            f'{name}: free-five comparison incidence mismatch')
    return {
        'fixture': name, 'gates': len(source),
        'positive_supplied_coordinates': len(supplied),
        'fixed_supplied_coordinates': sorted(v.removeprefix('native__') for v in supplied - FREE),
        'free_coordinates': sorted(v.removeprefix('native__') for v in FREE),
        'acyclic_single_assignment': True, 'comparisons': audit_comparisons,
    }


def mutation_self_tests(block):
    """Change only in-memory copies and require precise audit failures."""
    mutations = []

    wrong_norm = copy.deepcopy(block)
    for gate in wrong_norm['source']:
        if gate[0] == 'native__f_square_minus_one':
            gate[:] = ['native__f_square_minus_one', '*', 'native__A', 'native__L16']
        elif gate[0] == 'native__R16':
            gate[:] = ['native__R16', '-', 'native__f_square_minus_one', 1]
    mutations.append(('norm_parenthesis_Delta_f2_minus_1', wrong_norm,
                      'residual_mismatch', f"{block['fixture']}: comparison 12 residual mismatch"))

    missing_dependency = copy.deepcopy(block)
    for gate in missing_dependency['source']:
        if gate[0] == 'native__of':
            gate[2] = 1  # Replace o*f by 1*f, removing precisely the o dependence.
    mutations.append(('removed_o_dependency', missing_dependency,
                      'residual_mismatch', f"{block['fixture']}: comparison 14 residual mismatch"))

    wrong_witness = copy.deepcopy(block)
    wrong_witness['auxiliaries'][wrong_witness['auxiliaries'].index('native__ga')] = 'native__other'
    mutations.append(('changed_supplied_witness', wrong_witness,
                      'witness_list', f"{block['fixture']}: exact 22-coordinate supplied witness list mismatch"))

    results = []
    for label, changed, expected_code, expected_message in mutations:
        try:
            audit_block(changed)
        except AuditError as error:
            require(error.code == expected_code and str(error) == expected_message,
                    'mutation_wrong_failure', f'{label}: mutation failed for an unexpected reason: {error}')
            results.append({'mutation': label, 'rejected': True,
                            'failure_code': error.code, 'diagnostic': str(error)})
        else:
            raise AuditError('mutation_not_detected', f'{label}: changed source was incorrectly accepted')
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true',
                        help='explicitly create/update the generated receipt (default: read-only compare)')
    args = parser.parse_args()
    raw = INPUT.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    require(digest == PINNED_SHA256, 'input_hash', 'Pinned source/native_blocks.json SHA-256 mismatch')
    blocks = json.loads(raw)
    require(isinstance(blocks, list) and [b['fixture'] for b in blocks] == FIXTURES,
            'fixture_list', 'The four expected fixtures are missing, reordered, or changed')
    arithmetic_self_test()
    rows = [audit_block(block) for block in blocks]
    mutations = mutation_self_tests(blocks[0])
    result = {
        'status': 'PASS', 'receipt_version': 3,
        'method': 'Independent sparse integer-polynomial expansion and transitive dependency propagation from JSON data; Python standard library only; no author Python execution',
        'input': 'source/native_blocks.json', 'input_sha256': digest,
        'checks_active_under_python_optimization': True,
        'fixtures': rows, 'failure_mutation_self_tests': mutations,
    }
    if args.write:
        RECEIPT.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
        disposition = 'written (--write)'
    else:
        require(RECEIPT.is_file(), 'missing_receipt',
                'DEPENDENCY-RECEIPT.json is missing; use --write to create it explicitly')
        saved = json.loads(RECEIPT.read_text(encoding='utf-8'))
        require(saved == result, 'receipt_mismatch',
                'Computed audit differs from DEPENDENCY-RECEIPT.json; no file was changed')
        disposition = 'matched (read-only)'
    print(f'PASS: {len(rows)} fixtures; all 64 gates acyclic; all 16 residuals per fixture matched; '
          'exactly comparisons 12, 13, 14 vary; 17 fixed supplied coordinates.')
    print(f'PASS: {len(mutations)} in-memory failure mutations rejected as expected.')
    print(f'Receipt {disposition}: {RECEIPT.name}')
    return 0


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (AuditError, OSError, ValueError, KeyError, TypeError) as error:
        print(f'FAIL: {error}', file=sys.stderr)
        sys.exit(1)
