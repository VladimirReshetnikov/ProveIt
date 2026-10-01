"""Positive triangular elimination and a single-polynomial evaluation DAG.

The 75-operation certificate is not a 75-operation polynomial evaluation.
Eight positive definitions remove eight witnesses and comparisons before the
remaining residuals are squared.  No comparison is used by the final DAG.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import random

import complete75_half_binomial as baseline


# The selected definitions are positive on the entire retained positive grid.
# In particular k=eta+zeta keeps the substituted degree smaller than k=R11.
DEFINITIONS = {
    'C': 'marked_rhs', 'k': 'R10b', 'a': 'R12', 'c': 'R10a',
    'd': 'R14', 'kappa': 'index_rhs', 'mu': 'exponent_rhs',
}
DELETED_EQUALITIES = {0, 4, 6, 7, 9, 10, 15, 18}
ELIMINATED = {'q', *DEFINITIONS}
RETAINED = [name for name in baseline.prior.NAMES if name not in ELIMINATED]


def sources():
    """Reuse the symbolically audited baseline instructions, then rewire them."""
    audit = baseline.source_audit()
    original = [tuple(row) for row in audit['schedule']]
    nodes = {name: (op, left, right) for name, op, left, right in original}
    # Replace q-1 by a computed repunit, and define q=repunit+1.  This
    # replaces one addition by one addition, not an uncharged assignment.
    del nodes['qm1']
    nodes['q'] = ('+', 'repunit', 1)
    aliases = {**DEFINITIONS, 'qm1': 'repunit'}

    def alias(name):
        return aliases.get(name, name)

    free = set(RETAINED + baseline.prior.CONSTANTS + ['x'])
    free.update(('Bm1', 'Kconstant', 'twice_cell_bits'))
    ordered = []
    active = set()
    done = set(free)

    def visit(name):
        name = alias(name)
        if isinstance(name, int) or name in done:
            return name
        assert name not in active, ('cyclic definition', name)
        active.add(name)
        op, left, right = nodes[name]
        left, right = visit(left), visit(right)
        ordered.append((name, op, left, right))
        active.remove(name)
        done.add(name)
        return name

    equalities = []
    indices = []
    for index, (left, right) in enumerate(baseline.prior.EQUALITIES):
        if index not in DELETED_EQUALITIES:
            equalities.append((visit(left), visit(right)))
            indices.append(index)
    assert len(ordered) == 75
    assert len(equalities) == 11 and len(RETAINED) == 22
    return original, ordered, equalities, indices


def polynomial_schedule(certificate, equalities):
    """One output polynomial, no additional witnesses or comparisons."""
    result = list(certificate)
    squares = []
    for index, (left, right) in enumerate(equalities):
        residual, square = f'residual_{index}', f'square_{index}'
        result.extend(((residual, '-', left, right),
                       (square, '*', residual, residual)))
        squares.append(square)
    output = squares[0]
    for index, square in enumerate(squares[1:], 1):
        next_output = f'sum_{index}'
        result.append((next_output, '+', output, square))
        output = next_output
    return result, output


def verify_local_rewiring(original, certificate, equalities, indices):
    """Check exact local identities, hence rewiring for every assignment.

    This check does not sample values or assume any retained comparison.
    Topological induction on the certificate transfers each old register
    under the supplied aliases.  The one new gate q=repunit+1 gives
    q-1=repunit exactly, restoring the deleted repunit comparison.
    """
    old = {name: (op, left, right) for name, op, left, right in original}
    aliases = {**DEFINITIONS, 'qm1': 'repunit'}

    def rename(operand):
        return aliases.get(operand, operand)

    unchanged = new_q = 0
    for name, op, left, right in certificate:
        if name == 'q':
            assert (op, left, right) == ('+', 'repunit', 1)
            new_q += 1
        else:
            old_op, old_left, old_right = old[name]
            assert (op, left, right) == (old_op, rename(old_left), rename(old_right)), name
            unchanged += 1
    assert (unchanged, new_q) == (74, 1)
    for index in DELETED_EQUALITIES:
        left, right = baseline.prior.EQUALITIES[index]
        if index == 0:
            assert (left, right) == ('repunit', 'qm1')
        assert rename(left) == rename(right), (index, left, right)
    for index, (left, right) in zip(indices, equalities):
        old_left, old_right = baseline.prior.EQUALITIES[index]
        assert (left, right) == (rename(old_left), rename(old_right)), index
    assert len(indices) == len(equalities) == 11
    return dict(unchanged_gates_under_aliases=unchanged,
                new_repunit_successor_gates=new_q,
                deleted_comparisons_becoming_identities=len(DELETED_EQUALITIES),
                retained_comparisons_verified=len(equalities),
                scope='Exact local symbolic rewiring identities; holds on every assignment')


def run(schedule, inputs, modulus=None):
    env = dict(inputs)
    for name, op, left, right in schedule:
        assert name not in env, ('register overwritten', name)
        a = left if isinstance(left, int) else env[left]
        b = right if isinstance(right, int) else env[right]
        value = a+b if op == '+' else a-b if op == '-' else a*b
        env[name] = value if modulus is None else value % modulus
    return env


def fixed_inputs(values):
    result = baseline.prior.fixed_environment(values)
    result['MF'] = values['MF'] + values['B'] - 1
    return result


def degree_bounds(schedule):
    degrees = {name: 1 for name in RETAINED + ['x']}
    degrees.update({name: 0 for name in baseline.prior.CONSTANTS})
    degrees.update(Bm1=0, Kconstant=0, twice_cell_bits=0)
    for name, op, left, right in schedule:
        a = 0 if isinstance(left, int) else degrees[left]
        b = 0 if isinstance(right, int) else degrees[right]
        degrees[name] = a+b if op == '*' else max(a, b)
    return degrees


def verify():
    original, certificate, equalities, indices = sources()
    rewiring = verify_local_rewiring(original, certificate, equalities, indices)
    polynomial, output = polynomial_schedule(certificate, equalities)
    counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in polynomial)
    assert counts == {'M': 52, 'A': 55} and len(polynomial) == 107
    degrees = degree_bounds(polynomial)
    assert degrees[output] == 100  # Syntactic bound before norm cancellation.
    # Both norm residuals lose their leading a^2 coefficient.  The identity
    # below holds as an ordinary polynomial, with no source equation assumed.
    import sympy as sp
    aa, hh, vv, zz = sp.symbols('a H v z')
    assert sp.expand((aa*zz+vv)**2-(aa**2+hh)*zz**2-1
                     -(2*aa*zz*vv+vv**2-hh*zz**2-1)) == 0
    reduced_degrees = [degrees[f'residual_{i}'] for i in range(11)]
    reduced_degrees[5] = 22
    reduced_degrees[10] = 42
    assert 2*max(reduced_degrees) == 84
    # Check the degree-84 term independently: scale all varying coordinates
    # to t and use B=16, cell_bits=5, inner_bits=3, DC=DR=MC=MF=1.
    # A nonzero degree-84 specialization checks that this bound is sharp
    # for this fixed-parameter fixture; it is not a compiler instance.
    t = sp.Symbol('t')
    fixture = {name: sp.Poly(t, t) for name in RETAINED + ['x']}
    fixture.update(B=16, DC=1, DR=1, MC=1, MF=1, cell_bits=5, inner_bits=3)
    fixture_env = run(polynomial, fixed_inputs(fixture))
    fixture_poly = sp.Poly(fixture_env[output], t)
    assert fixture_poly.degree() == 84
    assert fixture_poly.LC() == 16*15**60
    # The final polynomial is a literal sum of squares of DAG residuals.
    # Replay forward/back substitutions with an independently executed old
    # schedule, and exercise all positive definition dependencies.  These
    # arbitrary assignments test identities, not genuine accepting tuples.
    rng = random.Random(750107)
    checked = 0
    max_bits = 0
    for _ in range(256):
        retained = {name: rng.randint(1, 9) for name in RETAINED + ['x']}
        constants = dict(B=rng.randint(2, 32), DC=3, DR=5, MC=7, MF=4,
                         cell_bits=5, inner_bits=3)
        env = run(polynomial, fixed_inputs({**retained, **constants}))
        recovered = {'q': env['q'],
                     **{name: env[register] for name, register in DEFINITIONS.items()}}
        assert all(value > 0 for value in recovered.values())
        full = {**retained, **recovered, **constants}
        old = run(original, fixed_inputs(full))
        old_residuals = [old[left]-old[right]
                         for left, right in baseline.prior.EQUALITIES]
        assert all(old_residuals[index] == 0 for index in DELETED_EQUALITIES)
        residuals = [env[left]-env[right] for left, right in equalities]
        assert residuals == [old_residuals[index] for index in indices]
        assert env[output] == sum(value*value for value in old_residuals)
        assert (env[output] == 0) == all(value == 0 for value in old_residuals)
        max_bits = max(max_bits, env[output].bit_length())
        checked += 1
    return dict(
        status='PASS_COMPLETE75_POSITIVE_ELIMINATION',
        retained_positive_witnesses=RETAINED,
        eliminated_positive_witnesses=sorted(ELIMINATED),
        certificate=dict(operations=75, multiplications=41,
                         additions_subtractions=34, equations=11, witnesses=22),
        single_polynomial=dict(operations=107, multiplications=52,
                               additions_subtractions=55, witnesses=22,
                               exact_degree_at_every_B_greater_than_one=84,
                               output_register=output),
        naive_30_witness_conversion=dict(operations=131, multiplications=60,
                                         additions_subtractions=71),
        retained_equality_indices=indices,
        retained_equalities=equalities,
        polynomial_schedule=polynomial,
        residual_degree_bounds=reduced_degrees,
        highest_homogeneous_term='16*(B-1)^60*delta^4*w^10*s^10*Jrep^60',
        degree_fixture=dict(constants=dict(B=16, DC=1, DR=1, MC=1, MF=1,
                                          cell_bits=5, inner_bits=3),
                            degree=fixture_poly.degree(),
                            leading_coefficient=str(fixture_poly.LC()),
                            scope='Positive arithmetic fixture, not a compiler instance'),
        identity_checks=checked, largest_polynomial_value_bits=max_bits,
        local_symbolic_rewiring=rewiring,
        limits='Equivalence is proved by positive triangular elimination; checks audit the DAG. '
               'The complete certificate operation bound remains75. '
               'Polynomial bound107 uses positive witnesses and fixed compiler numerals; '
               'not an optimality, publication, integer-domain or Lean claim.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = json.loads(json.dumps(verify()))
    receipt = Path(__file__).with_suffix('.json')
    if args.write:
        receipt.write_text(json.dumps(result, indent=2)+'\n')
    else:
        assert json.loads(receipt.read_text()) == result, 'receipt mismatch'
    print(result['status'], result['certificate'], result['single_polynomial'])
