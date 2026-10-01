#!/usr/bin/env python3
"""A complete positive local merge for externally typed binary prefix maps.

Input length-power typing and an existential word/tree compiler are not
provided by these seven equations.
"""
import argparse
from itertools import product
import json
from pathlib import Path
import random

from residue_affine_ancestor_pumping import Circuit
from residue_affine_factored_counter_step import finish
from two_stack_polycyclic_history_obstruction import encode, words, normal_apply


def descriptor(normal):
    u, v = normal
    return encode(u), 1 << len(u), encode(v), 1 << len(v)


def compose(first, second):
    """Independent string composition: apply first, then second."""
    if first is None or second is None:
        return None
    u, v = first
    a, b = second
    if v[:len(a)] == a:
        return u, b+v[len(a):]
    if a[:len(v)] == v:
        return u+a[len(v):], b
    return None


def witnesses(first, second):
    if first is None or second is None:
        return []
    _, v = first
    a, _ = second
    result = []
    if v[:len(a)] == a:
        tail = v[len(a):]
        result.append((1, 2, encode(tail), 1 << len(tail)))
    if a[:len(v)] == v:
        tail = a[len(v):]
        result.append((2, 1, encode(tail), 1 << len(tail)))
    return result


def source(c, first, second, output, supplied, one=False):
    U, Lu, V, Lv = first
    A, La, B, Lb = second
    C, Lc, D, Ld = output
    theta, theta_bar, T, S = supplied
    sides = [(c.add(theta, theta_bar), 3)]
    e = c.sub(theta, 1)
    g, s = c.sub(T, 1), c.sub(S, 1)
    f, h = c.mul(e, g), c.mul(e, s)
    J = c.add(La, Lv)
    remaining_code, remaining_scale = c.sub(g, f), c.sub(s, h)
    sides += [(V, c.sub(c.add(A, c.mul(La, g)), c.mul(J, f))),
              (Lv, c.sub(c.add(La, c.mul(La, s)), c.mul(J, h))),
              (C, c.add(U, c.mul(Lu, f))),
              (D, c.add(B, c.mul(Lb, remaining_code))),
              (Lc, c.add(Lu, c.mul(Lu, h))),
              (Ld, c.add(Lb, c.mul(Lb, remaining_scale)))]
    return finish(c, sides, one)


def manual_residuals(first, second, output, supplied):
    U, Lu, V, Lv = first
    A, La, B, Lb = second
    C, Lc, D, Ld = output
    theta, bar, T, S = supplied
    e = theta-1
    return (theta+bar-3,
            V-A-La*(T-1)+(La+Lv)*e*(T-1),
            Lv-La-La*(S-1)+(La+Lv)*e*(S-1),
            C-U-Lu*e*(T-1),
            D-B-Lb*(1-e)*(T-1),
            Lc-Lu-Lu*e*(S-1),
            Ld-Lb-Lb*(1-e)*(S-1))


def scalar_checks():
    alphabet_words = words((0, 1), 3)
    guards = successful_guards = compositions = equality_branches = 0
    for v, a in product(alphabet_words, repeat=2):
        first, second = ((1,), v), (a, (1, 0))
        expected = witnesses(first, second)
        observed = []
        for theta, T, S in product((1, 2), range(1, 16), range(1, 16)):
            U, Lu, V, Lv = descriptor(first)
            A, La, B, Lb = descriptor(second)
            e = theta-1
            output = (U+Lu*e*(T-1), Lu+Lu*e*(S-1),
                      B+Lb*(1-e)*(T-1), Lb+Lb*(1-e)*(S-1))
            supplied = theta, 3-theta, T, S
            c = Circuit()
            residuals = source(c, descriptor(first), descriptor(second), output, supplied)
            assert c.counts == {'M':10, 'A':15}
            if not any(residuals):
                observed.append(supplied)
                assert output == descriptor(compose(first, second))
                assert S & (S-1) == 0 and S <= T < 2*S
            guards += 1
        assert sorted(observed) == sorted(expected)
        successful_guards += len(observed)
    for u, v, a, b in product(alphabet_words, repeat=4):
        first, second = (u, v), (a, b)
        merged = compose(first, second)
        supplied_options = witnesses(first, second)
        assert bool(supplied_options) == (merged is not None)
        for supplied in supplied_options:
            out = descriptor(merged)
            for one in (False, True):
                c = Circuit()
                value = source(c, descriptor(first), descriptor(second), out, supplied, one)
                assert value == (0 if one else (0,)*7)
                assert c.counts == {'M':10+7*one, 'A':15+13*one}
            # Every individual output coordinate is constrained.
            for coordinate in range(4):
                wrong = list(out)
                wrong[coordinate] += 1
                assert any(source(Circuit(), descriptor(first), descriptor(second), wrong, supplied))
            compositions += 1
            equality_branches += v == a
    return dict(orientation_tail_guard_cases=guards, successful_guard_assignments=successful_guards,
                legal_string_merge_witnesses=compositions, empty_tail_witnesses=equality_branches,
                independently_corrupted_output_coordinates=4*compositions)


def semantic_checks():
    rng = random.Random(251045)
    cases = arbitrary = 0
    for _ in range(4000):
        u, a, b, tail = [tuple(rng.randrange(2) for _ in range(rng.randrange(10))) for _ in range(4)]
        if rng.randrange(2):
            first, second = (u, a+tail), (a, b)
        else:
            first, second = (u, a), (a+tail, b)
        merged = compose(first, second)
        out = descriptor(merged)
        for supplied in witnesses(first, second):
            assert not any(source(Circuit(), descriptor(first), descriptor(second), out, supplied))
        initial = merged[0]+tuple(rng.randrange(2) for _ in range(rng.randrange(8)))
        assert normal_apply(second, normal_apply(first, initial)) == normal_apply(merged, initial)
        # A separate arbitrary initial word tests domain exclusion too.
        initial = tuple(rng.randrange(2) for _ in range(rng.randrange(12)))
        middle = normal_apply(first, initial)
        sequential = None if middle is None else normal_apply(second, middle)
        assert sequential == normal_apply(merged, initial)
        cases += 1
    for _ in range(512):
        first, second, out, supplied = [tuple(rng.randrange(1, 100) for _ in range(4)) for _ in range(4)]
        expected = manual_residuals(first, second, out, supplied)
        c = Circuit()
        assert source(c, first, second, out, supplied) == expected
        assert c.counts == {'M':10, 'A':15}
        c = Circuit()
        assert source(c, first, second, out, supplied, True) == sum(r*r for r in expected)
        assert c.counts == {'M':17, 'A':28}
        arbitrary += 1
    # Input scale typing is necessary. This is an exact zero with nonpowers3,6.
    first, second = (1, 1, 6, 6), (3, 3, 1, 1)
    out, supplied = (1, 1, 2, 2), (1, 2, 2, 2)
    assert not any(source(Circuit(), first, second, out, supplied))
    assert 3 & (3-1) and 6 & (6-1)
    # Even honest powers do not replace the code/length bounds: A=4 is
    # outside [La,2La) for La=2, and the decoded prefixes are incomparable.
    first, second = (1, 1, 6, 4), (4, 2, 1, 1)
    assert not any(source(Circuit(), first, second, out, supplied))
    return dict(random_word_and_domain_cases=cases, arbitrary_positive_residual_audits=arbitrary,
                external_power_typing_counterexample=True,
                external_code_bound_counterexample=True)


def tree_shape(size, style):
    if size == 1:
        return None
    split = 1 if style == 'right' else size-1 if style == 'left' else size//2
    return tree_shape(split, style), tree_shape(size-split, style)


def compile_tree(shape, leaves, cursor=0):
    """Postorder records; leaf and geometry choices are fixed source data."""
    if shape is None:
        return leaves[cursor], [], cursor+1
    first, left, cursor = compile_tree(shape[0], leaves, cursor)
    second, right, cursor = compile_tree(shape[1], leaves, cursor)
    merged = compose(first, second)
    if merged is None:
        return None, left+right, cursor
    return merged, left+right+[(descriptor(first), descriptor(second), descriptor(merged),
                               witnesses(first, second)[0])], cursor


def tree_source(c, shape, leaves, root, internal, supplied, one=False):
    """Reuse each supplied internal coordinate tuple at its parent input."""
    leaf_cursor, node_cursor = 0, 0
    outputs, values = list(internal)+[root], []

    def visit(subtree):
        nonlocal leaf_cursor, node_cursor
        if subtree is None:
            value = leaves[leaf_cursor]
            leaf_cursor += 1
            return value
        first, second = visit(subtree[0]), visit(subtree[1])
        target, local = outputs[node_cursor], supplied[node_cursor]
        node_cursor += 1
        values.append(source(c, first, second, target, local, one))
        return target

    assert visit(shape) == root
    assert leaf_cursor == len(leaves) and node_cursor == len(outputs) == len(supplied)
    if not one:
        return tuple(r for row in values for r in row)
    result = values[0]
    for value in values[1:]:
        result = c.add(result, value)
    return result


def tree_checks():
    rng = random.Random(127045)
    successful = zeros = 0
    small = words((0, 1), 2)
    for t in range(2, 17):
        for trial in range(40):
            if trial % 2:
                # Arbitrary consecutive boundary words yield compatible maps.
                boundaries = [rng.choice(small) for _ in range(t+1)]
                leaves = list(zip(boundaries, boundaries[1:]))
            else:
                leaves = [(rng.choice(small), rng.choice(small)) for _ in range(t)]
            expected = leaves[0]
            for following in leaves[1:]:
                expected = compose(expected, following)
            for style in ('left', 'right', 'balanced'):
                merged, records, cursor = compile_tree(tree_shape(t, style), leaves)
                assert cursor == t and merged == expected
                if merged is None:
                    zeros += 1
                    continue
                m = t-1
                assert len(records) == m
                shape = tree_shape(t, style)
                root = records[-1][2]
                internal = [row[2] for row in records[:-1]]
                supplied = [row[3] for row in records]
                typed_leaves = [descriptor(leaf) for leaf in leaves]
                c = Circuit()
                residuals = tree_source(c, shape, typed_leaves, root, internal, supplied)
                assert not any(residuals) and len(residuals) == 7*m
                assert c.counts == {'M':10*m, 'A':15*m}
                assert 4*(m-1)+4*m == 8*t-12
                c = Circuit()
                value = tree_source(c, shape, typed_leaves, root, internal, supplied, True)
                assert value == 0 and c.counts == {'M':17*m, 'A':29*m-1}
                wrong_root = list(root)
                wrong_root[0] += 1
                assert any(tree_source(Circuit(), shape, typed_leaves, wrong_root, internal, supplied))
                if internal:
                    wrong_internal = [list(row) for row in internal]
                    wrong_internal[0][1] += 1
                    assert any(tree_source(Circuit(), shape, typed_leaves, root, wrong_internal, supplied))
                successful += 1
    return dict(nonzero_fixed_tree_certificates=successful, zero_compositions_rejected=zeros,
                shapes=['left', 'right', 'balanced'], leaf_counts=list(range(2, 17)),
                graph='25(t-1)', equations='7(t-1)', positive_internal_witnesses='8t-12',
                single_polynomial='46t-47',
                scope='Fixed typed leaves, fixed tree, four supplied root coordinates; no word selector')


def verify():
    return dict(status='PASS_TYPED_PREFIX_NORMAL_FORM_MERGE25',
                graph=dict(operations=25, multiplications=10, additions=15,
                           positive_auxiliary_witnesses=4, equations=7),
                polynomial=dict(operations=45, multiplications=17, additions=28),
                scalar=scalar_checks(), semantics=semantic_checks(), fixed_tree=tree_checks(),
                limits='Four input length powers and their code bounds are external typing assumptions. '
                       'Output typing is proved. Empty tests, input loading, control, and uniform word/tree '
                       'geometry are not supplied. No new complete universal bound.')


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
    print('25=10M+15A; 4 positive auxiliary witnesses, 7 equations; typed input powers remain external.')
