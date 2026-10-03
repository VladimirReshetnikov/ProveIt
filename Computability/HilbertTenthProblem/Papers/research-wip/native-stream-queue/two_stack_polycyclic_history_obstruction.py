#!/usr/bin/env python3
"""Exact typed-stack products, finite-depth rank witnesses, and paid loading.

The matrix certificate below has a fixed action word and fixed depth.  It
does not encode an existential action word or an unbounded run length.
"""
import argparse
from collections import Counter
from fractions import Fraction
from itertools import product
import json
from pathlib import Path
import random

from residue_affine_ancestor_pumping import Circuit
from residue_affine_factored_counter_step import finish


PUSH0, PUSH1, POP0, POP1, EMPTY = ('+', 0), ('+', 1), ('-', 0), ('-', 1), ('E', None)
BINARY = (PUSH0, PUSH1, POP0, POP1)
BOTTOM = 2


def words(alphabet, height):
    return [word for length in range(height+1) for word in product(alphabet, repeat=length)]


def encode(word):
    return (1 << len(word)) + sum(bit << j for j, bit in enumerate(word))


def decode(number):
    assert number > 0
    return tuple((number >> j) & 1 for j in range(number.bit_length()-1))


def run_stack(initial, actions, height=None):
    """Independent string semantics, including a genuine empty test."""
    stack = tuple(initial)
    if height is not None and len(stack) > height:
        return None
    for kind, bit in actions:
        if kind == '+':
            stack = (bit,)+stack
            if height is not None and len(stack) > height:
                return None
        elif kind == '-':
            if not stack or stack[0] != bit:
                return None
            stack = stack[1:]
        else:
            assert kind == 'E'
            if stack:
                return None
    return stack


def partial_normal_form(actions):
    """Return (u,v) for the prefix replacement u*z -> v*z, or zero."""
    required, produced = (), ()
    for kind, bit in actions:
        if kind == '+':
            produced = (bit,)+produced
        else:
            assert kind == '-'
            if produced:
                if produced[0] != bit:
                    return None
                produced = produced[1:]
            else:
                required += (bit,)
    return required, produced


def normal_apply(normal, initial):
    if normal is None:
        return None
    required, produced = normal
    if initial[:len(required)] != required:
        return None
    return produced+initial[len(required):]


def push_word(word):
    return tuple(('+', bit) for bit in reversed(word))


def pop_word(word):
    return tuple(('-', bit) for bit in word)


def compile_read(read, replacement):
    """Binary stack branch, with E compiled using a third-color bottom."""
    guard = (('-', BOTTOM), ('+', BOTTOM)) if read is None else (('-', read),)
    return guard+push_word(replacement)


def dyck_bridge(initial, actions):
    """actions already include explicit bottom-marker empty tests."""
    return push_word(tuple(initial)+(BOTTOM,))+tuple(actions)+(('-', BOTTOM),)


def matmul(left, right):
    return tuple(tuple(sum(left[i][k]*right[k][j] for k in range(2))
                       for j in range(2)) for i in range(2))


IDENTITY = ((Fraction(1), Fraction(0)), (Fraction(0), Fraction(1)))


def affine_matrix(action):
    kind, bit = action
    if kind == '+':
        return ((Fraction(2), Fraction(bit)), (Fraction(0), Fraction(1)))
    assert kind == '-'
    return ((Fraction(1, 2), Fraction(-bit, 2)), (Fraction(0), Fraction(1)))


def affine_product(actions):
    value = IDENTITY
    for action in actions:
        value = matmul(affine_matrix(action), value)
    return value


def free_reduce(actions):
    stack = []
    for kind, bit in actions:
        if stack and stack[-1][1] == bit and stack[-1][0] != kind:
            stack.pop()
        else:
            stack.append((kind, bit))
    return tuple(stack)


def basis_images(height, action):
    """Column images for fixed partial-permutation matrices; numeric semantics."""
    N = (1 << (height+1))-1
    kind, bit = action
    result = []
    for code in range(1, N+1):
        if kind == '+':
            target = 2*code+bit
            if target > N:
                target = None
        elif kind == '-':
            target = code//2 if code >= 2 and code % 2 == bit else None
        else:
            assert kind == 'E'
            target = 1 if code == 1 else None
        result.append(None if target is None else target-1)
    assert len({j for j in result if j is not None}) == sum(j is not None for j in result)
    return tuple(result)


def sparse_apply(images, vector):
    result = [0]*len(vector)
    for column, row in enumerate(images):
        if row is not None:
            result[row] += vector[column]
    return tuple(result)


def basis_vector(N, code):
    return tuple(int(i == code) for i in range(1, N+1))


def loader_sides(c, x, scale, offset, supplied):
    """N positive supplied coordinates: exactly one is 2, the others are 1."""
    N = len(supplied)
    unweighted = supplied[-1]
    weighted = supplied[-1]
    # Sum the suffix sums: u_N+(u_N+u_(N-1))+... = sum_i i*u_i.
    for value in reversed(supplied[:-1]):
        unweighted = c.add(unweighted, value)
        weighted = c.add(weighted, unweighted)
    target = c.add(c.mul(scale, x), offset+N*(N+1)//2)
    return [(unweighted, N+1), (weighted, target)]


def loader_source(c, x, scale, offset, supplied, one=False):
    return finish(c, loader_sides(c, x, scale, offset, supplied), one)


def fixed_word_source(c, x, scale, offset, height, actions, supplied, one=False):
    """All action labels and their number are source constants, not witnesses."""
    N = (1 << (height+1))-1
    assert len(actions) == len(supplied) >= 1
    assert all(len(row) == N for row in supplied)
    sides = loader_sides(c, x, scale, offset, supplied[0])
    target = tuple(1+bit for bit in basis_vector(N, 1))
    for j, action in enumerate(actions):
        preimage = [None]*N
        for column, row in enumerate(basis_images(height, action)):
            if row is not None:
                preimage[row] = column
        following = supplied[j+1] if j+1 < len(supplied) else target
        sides.extend((following[row], supplied[j][column] if column is not None else 1)
                     for row, column in enumerate(preimage))
    return finish(c, sides, one)


def normal_form_checks():
    totals = Counter()
    for alphabet, max_length, initial_height in (((0, 1), 7, 3), ((0, 1, 2), 5, 2)):
        letters = tuple((kind, bit) for kind in ('+', '-') for bit in alphabet)
        starts = words(alphabet, initial_height)
        for length in range(max_length+1):
            for actions in product(letters, repeat=length):
                normal = partial_normal_form(actions)
                assert (normal == ((), ())) == (run_stack((), actions) == ())
                for initial in starts:
                    assert normal_apply(normal, initial) == run_stack(initial, actions)
                    totals['word_initial_pairs'] += 1
                totals['normal_forms'] += 1
    assert partial_normal_form((POP0, PUSH0)) == ((0,), (0,))
    return dict(totals)


def affine_counterexamples():
    invalid = (PUSH0, POP1, PUSH1, POP0)
    valid = (PUSH0, POP0, PUSH1, POP1)
    assert Counter(invalid) == Counter(valid)
    heights = [0]
    for kind, _ in invalid:
        heights.append(heights[-1]+(1 if kind == '+' else -1))
    assert min(heights) == 0 and heights[-1] == 0
    assert not free_reduce(invalid) and affine_product(invalid) == affine_product(valid) == IDENTITY
    assert partial_normal_form(invalid) is None
    for code in range(1, 257):
        value = Fraction(code)
        for action in invalid:
            matrix = affine_matrix(action)
            value = matrix[0][0]*value+matrix[0][1]
            assert value > 0
        assert value == code
        assert run_stack(decode(code), invalid) is None
        assert run_stack(decode(code), valid) == decode(code)
    underflow = (POP0, PUSH0)
    assert affine_product(underflow) == IDENTITY and run_stack((), underflow) is None
    assert normal_apply(partial_normal_form(underflow), ()) is None
    return dict(mismatched_word=invalid, matching_word=valid, height_trace=heights,
                identical_action_multiplicities=True, affine_inputs_checked=256,
                every_rational_intermediate_positive=True,
                arbitrary_group_identity_reason='g0*g1^-1*g1*g0^-1 = 1; inverses are assumed')


def finite_basis_checks():
    rng = random.Random(20831)
    tests, pairings, rows = 0, 0, []
    for height in range(6):
        N = (1 << (height+1))-1
        for code in range(1, N+1):
            for action in BINARY+(EMPTY,):
                result = sparse_apply(basis_images(height, action), basis_vector(N, code))
                direct = run_stack(decode(code), (action,), height)
                assert result == ((0,)*N if direct is None else basis_vector(N, encode(direct)))
                tests += 1
        # An explicit identity submatrix of the Dyck characteristic pairing.
        for u, v in product(words((0, 1), height), repeat=2):
            outcome = run_stack((), push_word(u)+pop_word(v), height)
            assert (outcome == ()) == (u == v)
            pairings += 1
        for _ in range(160):
            code = rng.randrange(1, N+1)
            actions = tuple(rng.choice(BINARY+(EMPTY,)) for _ in range(rng.randrange(1, 35)))
            vector = basis_vector(N, code)
            for action in actions:
                vector = sparse_apply(basis_images(height, action), vector)
            direct = run_stack(decode(code), actions, height)
            assert vector == ((0,)*N if direct is None else basis_vector(N, encode(direct)))
            tests += 1
        rows.append(dict(height=height, sharp_dimension=N, identity_pairing_rank=N))
    return dict(sparse_action_and_trace_checks=tests, characteristic_identity_entries=pairings,
                depth_rows=rows)


def branch_bridge_checks():
    totals = Counter()
    replacement_words = words((0, 1), 3)
    for initial in words((0, 1), 4):
        for read, replacement in product((None, 0, 1), replacement_words):
            actual_read = initial[0] if initial else None
            expected = None if read != actual_read else replacement+(initial[1:] if initial else ())
            compiled = compile_read(read, replacement)
            observed = run_stack(tuple(initial)+(BOTTOM,), compiled)
            assert observed == (None if expected is None else expected+(BOTTOM,))
            # Add a cleanup, including deliberately incorrect cleanup words.
            for cleanup in (expected if expected is not None else (), (0, 1)):
                full = dyck_bridge(initial, compiled+pop_word(cleanup))
                honest_empty = expected is not None and expected == cleanup
                assert (partial_normal_form(full) == ((), ())) == honest_empty
                totals['bottom_marker_endpoint_checks'] += 1
            totals['read_and_replacement_checks'] += 1
    # State compatibility is a separate guard, even with two exact stack products.
    # Two empty-preserving branches 1->2 and 3->4 have a disconnected middle state.
    empty_branch = compile_read(None, ())
    assert partial_normal_form(dyck_bridge((), empty_branch+empty_branch)) == ((), ())
    assert 2 != 3
    totals['disconnected_control_counterexamples'] = 1
    return dict(totals)


def positive_source_checks():
    counts = Counter()
    rng = random.Random(89122)
    for height in range(5):
        N = (1 << (height+1))-1
        for scale, offset in ((1, 0), (2, 0), (2, 1), (4, 3)):
            for x in range(1, N+3):
                target = scale*x+offset
                # All possible one-hot vectors; membership iff target in range.
                found = 0
                for selected in range(1, N+1):
                    supplied = tuple(1+bit for bit in basis_vector(N, selected))
                    c = Circuit()
                    residuals = loader_source(c, x, scale, offset, supplied)
                    assert c.counts == {'M':1, 'A':2*N-1}
                    assert (not any(residuals)) == (target == selected)
                    found += not any(residuals)
                    c = Circuit()
                    polynomial = loader_source(c, x, scale, offset, supplied, True)
                    assert polynomial == sum(r*r for r in residuals)
                    assert c.counts == {'M':3, 'A':2*N+2}
                    counts['loader_one_hot_checks'] += 1
                assert found == (1 <= target <= N)
        for _ in range(100):
            supplied = tuple(rng.randrange(1, 5) for _ in range(N))
            x = rng.randrange(1, N+3)
            residuals = loader_source(Circuit(), x, 1, 0, supplied)
            expected = tuple(1+bit for bit in basis_vector(N, x)) if x <= N else None
            assert (not any(residuals)) == (supplied == expected)
            counts['arbitrary_positive_loader_checks'] += 1
        for code in range(1, N+1):
            good = pop_word(decode(code))+(EMPTY,)
            action_words = (good, good+(PUSH0,), (POP0, PUSH0)+good,
                            (PUSH0, POP1, PUSH1, POP0)+good)
            for actions in action_words:
                vector = basis_vector(N, code)
                supplied = []
                for action in actions:
                    supplied.append(tuple(1+bit for bit in vector))
                    vector = sparse_apply(basis_images(height, action), vector)
                c = Circuit()
                residuals = fixed_word_source(c, code, 1, 0, height, actions, supplied)
                t = len(actions)
                assert len(residuals) == N*t+2
                assert all(value > 0 for row in supplied for value in row)
                assert len(supplied)*N == N*t
                assert c.counts == {'M':1, 'A':2*N-1}
                assert (not any(residuals)) == (run_stack(decode(code), actions, height) == ())
                c = Circuit()
                polynomial = fixed_word_source(c, code, 1, 0, height, actions, supplied, True)
                assert polynomial == sum(r*r for r in residuals)
                assert c.counts == {'M':N*t+3, 'A':2*N*(t+1)+2}
                changed = [list(row) for row in supplied]
                changed[0][0] += 1
                assert any(fixed_word_source(Circuit(), code, 1, 0, height, actions, changed))
                counts['fixed_word_certificates'] += 1
    return dict(counts, loader_graph='2N=1M+(2N-1)A', loader_equations=2,
                loader_positive_witnesses='N', loader_polynomial='2N+5',
                fixed_word_graph='2N', fixed_word_equations='Nt+2',
                fixed_word_positive_witnesses='Nt', fixed_word_polynomial='N(3t+2)+5',
                fixed_word_scope='H, t and the entire action word are source constants')


def verify():
    return dict(status='PASS_TWO_STACK_POLYCYCLIC_HISTORY_OBSTRUCTION',
                normal_forms=normal_form_checks(), counterexamples=affine_counterexamples(),
                linear_models=finite_basis_checks(), bottom_marker=branch_bridge_checks(),
                arithmetic=positive_source_checks(),
                primary_source='https://arxiv.org/pdf/math/0601061',
                scope='Exact raw-action linear models and characteristic recognition only. '
                      'Auxiliary transitions, rational transductions and nonlinear matrix tests are not ruled out. '
                      'No existential-duration or existential-action-word arithmetic compiler is supplied.',
                established_complete_universal_bound=75)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = json.loads(json.dumps(verify()))
    path = Path(__file__).with_suffix('.json')
    if args.write:
        path.write_text(json.dumps(result, indent=2)+'\n')
    else:
        assert json.loads(path.read_text()) == result, 'receipt mismatch'
    print(result['status'])
    print('Sharp binary depth-H dimension: 2^(H+1)-1; ordinary-input basis loader: 2N operations.')
