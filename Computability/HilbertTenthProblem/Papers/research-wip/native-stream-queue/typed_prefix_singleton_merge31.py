#!/usr/bin/env python3
"""Positive prefix-cone/singleton composition, empty tests and paid endpoints.

Finite leaves and tree geometry remain source data.  There is no uniform
selected-word, control-path, or variable-size-tree arithmetic compiler.
"""
import argparse
from itertools import product
import json
from pathlib import Path
import random

from residue_affine_ancestor_pumping import Circuit
from residue_affine_factored_counter_step import finish
from two_stack_polycyclic_history_obstruction import encode, decode, words, run_stack
import typed_prefix_normal_form_merge25 as cone


def descriptor(normal):
    u, v, singleton = normal
    return encode(u), 1 << len(u), encode(v), 1 << len(v), 1+singleton


def apply(normal, initial):
    if normal is None:
        return None
    u, v, singleton = normal
    if singleton:
        return v if initial == u else None
    return v+initial[len(u):] if initial[:len(u)] == u else None


def compose(first, second):
    """Independent domain-first composition, rather than selector algebra."""
    if first is None or second is None:
        return None
    u, v, F = first
    a, b, G = second
    if F:
        target = apply(second, v)
        return None if target is None else (u, target, 1)
    if G:
        return (u+a[len(v):], b, 1) if a[:len(v)] == v else None
    merged = cone.compose((u, v), (a, b))
    return None if merged is None else (*merged, 0)


def witnesses(first, second):
    result = []
    for supplied in cone.witnesses(first[:2], second[:2]):
        theta, _, T, _ = supplied
        if first[2] and theta == 2 and T != 1:
            continue
        if second[2] and theta == 1 and T != 1:
            continue
        result.append(supplied)
    return result


def merge_sides(c, first, second, output, supplied):
    U, Lu, V, Lv = first[:4]
    A, La, B, Lb = second[:4]
    C, Lc, D, Ld = output[:4]
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
    return sides, f, remaining_code


def source(c, first, second, output, supplied, one=False, omit_output_flag=False):
    sigma, tau = first[4], second[4]
    sides, f, remaining_code = merge_sides(c, first, second, output, supplied)
    sides += [(c.mul(sigma, f), f), (c.mul(tau, remaining_code), remaining_code)]
    if not omit_output_flag:
        first_cone, second_cone = c.sub(2, sigma), c.sub(2, tau)
        sides.append((output[4], c.sub(2, c.mul(first_cone, second_cone))))
    return finish(c, sides, one)


def static_source(c, first, second, output, supplied, one=False):
    """Input flags are fixed source numerals, not free relation arguments."""
    assert first[4] in (1, 2) and second[4] in (1, 2)
    sides, f, remaining_code = merge_sides(c, first, second, output, supplied)
    if first[4] == 2:
        sides.append((f, 0))
    if second[4] == 2:
        sides.append((remaining_code, 0))
    return finish(c, sides, one)


def manual_residuals(first, second, output, supplied, omit_output_flag=False):
    base = cone.manual_residuals(first[:4], second[:4], output[:4], supplied)
    e, g = supplied[0]-1, supplied[2]-1
    sigma, tau = first[4], second[4]
    guards = ((sigma-1)*e*g, (tau-1)*(1-e)*g)
    flag = () if omit_output_flag else (output[4]-2+(2-sigma)*(2-tau),)
    return base+guards+flag


def scalar_checks():
    short = words((0, 1), 2)
    guards = legal = mutations = 0
    for v, a, F, G in product(words((0, 1), 3), words((0, 1), 3), (0, 1), (0, 1)):
        first, second = ((1,), v, F), (a, (1, 0), G)
        expected = witnesses(first, second)
        observed = []
        for theta, T, S in product((1, 2), range(1, 16), range(1, 16)):
            U, Lu, V, Lv, sigma = descriptor(first)
            A, La, B, Lb, tau = descriptor(second)
            e = theta-1
            output = (U+Lu*e*(T-1), Lu+Lu*e*(S-1),
                      B+Lb*(1-e)*(T-1), Lb+Lb*(1-e)*(S-1), 1+(F or G))
            supplied = theta, 3-theta, T, S
            c = Circuit()
            residuals = source(c, descriptor(first), descriptor(second), output, supplied)
            assert c.counts == {'M':13, 'A':18}
            if not any(residuals):
                observed.append(supplied)
                assert output == descriptor(compose(first, second))
                assert S & (S-1) == 0 and S <= T < 2*S
            guards += 1
        assert sorted(observed) == sorted(expected)
        assert bool(observed) == (compose(first, second) is not None)
    for u, v, a, b, F, G in product(short, short, short, short, (0, 1), (0, 1)):
        first, second = (u, v, F), (a, b, G)
        merged = compose(first, second)
        options = witnesses(first, second)
        assert bool(options) == (merged is not None)
        for supplied in options:
            output = descriptor(merged)
            for one in (False, True):
                c = Circuit()
                actual = source(c, descriptor(first), descriptor(second), output, supplied, one)
                assert actual == (0 if one else (0,)*10)
                assert c.counts == {'M':13+10*one, 'A':18+19*one}
            for index in range(5):
                wrong = list(output)
                wrong[index] += 1
                assert source(Circuit(), descriptor(first), descriptor(second), wrong, supplied, True) == 1
                mutations += 1
            legal += 1
    return dict(bounded_orientation_tail_cases=guards, legal_string_merge_witnesses=legal,
                output_coordinate_mutations=mutations)


def domain_and_identity_checks():
    rng = random.Random(311060)
    domains = zero = arbitrary = 0
    for _ in range(5000):
        u, v, a, b = [tuple(rng.randrange(2) for _ in range(rng.randrange(8))) for _ in range(4)]
        first, second = (u, v, rng.randrange(2)), (a, b, rng.randrange(2))
        merged = compose(first, second)
        options = witnesses(first, second)
        assert bool(options) == (merged is not None)
        inputs = [u, u+(0,), u+(1,), tuple(rng.randrange(2) for _ in range(rng.randrange(10)))]
        if merged is not None:
            inputs += [merged[0], merged[0]+(0,), merged[0]+(1,)]
            for supplied in options:
                assert not any(source(Circuit(), descriptor(first), descriptor(second),
                                      descriptor(merged), supplied))
        else:
            zero += 1
        for initial in inputs:
            middle = apply(first, initial)
            sequential = None if middle is None else apply(second, middle)
            assert sequential == apply(merged, initial)
            domains += 1
    for _ in range(512):
        first, second, output = [tuple(rng.randrange(1, 50) for _ in range(5)) for _ in range(3)]
        supplied = tuple(rng.randrange(1, 50) for _ in range(4))
        for omitted in (False, True):
            expected = manual_residuals(first, second, output, supplied, omitted)
            c = Circuit()
            assert source(c, first, second, output, supplied, omit_output_flag=omitted) == expected
            assert c.counts == {'M':13-int(omitted), 'A':18-3*int(omitted)}
            c = Circuit()
            actual = source(c, first, second, output, supplied, True, omitted)
            assert actual == sum(r*r for r in expected)
            assert c.counts == {'M':23-2*int(omitted), 'A':37-5*int(omitted)}
            arbitrary += 1
    # Each new guard is indispensable even with perfectly typed input words.
    guard_failures = [(((), (), 1), ((0,), (), 0)),
                      (((), (0,), 0), ((), (), 1))]
    for index, (first, second) in enumerate(guard_failures):
        base_output = cone.compose(first[:2], second[:2])
        supplied = cone.witnesses(first[:2], second[:2])[0]
        output = (*cone.descriptor(base_output), 2)
        residuals = source(Circuit(), descriptor(first), descriptor(second), output, supplied)
        assert compose(first, second) is None
        assert all(value == 0 for j, value in enumerate(residuals) if j != 7+index)
        assert residuals[7+index] > 0
    # The source does not bound its input flags: their typing is external.
    untyped = (1, 1, 1, 1, 3)
    assert not any(source(Circuit(), untyped, untyped, (1, 1, 1, 1, 1), (1, 2, 1, 1)))
    return dict(random_partial_domain_checks=domains, random_zero_products=zero,
                arbitrary_positive_residual_audits=arbitrary,
                independently_required_singleton_guards=2, external_flag_typing_counterexample=True)


def action_normal(action):
    kind, bit = action
    if kind == '+':
        return (), (bit,), 0
    if kind == '-':
        return (bit,), (), 0
    assert kind == 'E'
    return (), (), 1


def action_checks():
    letters = (('+', 0), ('+', 1), ('-', 0), ('-', 1), ('E', None))
    cases = 0
    for length in range(6):
        for actions in product(letters, repeat=length):
            merged = ((), (), 0)
            for action in actions:
                merged = compose(merged, action_normal(action))
            for initial in words((0, 1), 3):
                assert apply(merged, initial) == run_stack(initial, actions)
                cases += 1
    return dict(empty_test_and_push_pop_trace_inputs=cases,
                alphabet=['push0', 'push1', 'pop0', 'pop1', 'empty-test'])


def compile_tree(shape, leaves, cursor=0):
    if shape is None:
        return leaves[cursor], [], cursor+1
    first, left, cursor = compile_tree(shape[0], leaves, cursor)
    second, right, cursor = compile_tree(shape[1], leaves, cursor)
    merged = compose(first, second)
    if merged is None:
        return None, left+right, cursor
    return merged, left+right+[(descriptor(merged), witnesses(first, second)[0])], cursor


def tree_source(c, shape, leaves, root, internal, supplied, one=False, omit_root_flag=False):
    leaf_cursor, node_cursor = 0, 0
    targets, values = list(internal)+[root], []

    def visit(node):
        nonlocal leaf_cursor, node_cursor
        if node is None:
            value = leaves[leaf_cursor]
            leaf_cursor += 1
            return value
        first, second = visit(node[0]), visit(node[1])
        target, local = targets[node_cursor], supplied[node_cursor]
        is_root = node_cursor+1 == len(targets)
        node_cursor += 1
        values.append(source(c, first, second, target, local, one, is_root and omit_root_flag))
        return target

    assert visit(shape) == root
    assert leaf_cursor == len(leaves) and node_cursor == len(targets) == len(supplied)
    if not one:
        return tuple(r for row in values for r in row)
    value = values[0]
    for following in values[1:]:
        value = c.add(value, following)
    return value


def accept_source(c, x, scale, offset, shape, leaves, input_power, internal, supplied, one=False):
    root = (c.add(c.mul(scale, x), offset), input_power, 1, 1)
    return tree_source(c, shape, leaves, root, internal, supplied, one, True)


def two_stack_accept_source(c, x, scale, offset, shape, left, right, one=False):
    code = c.add(c.mul(scale, x), offset)
    results = []
    left_leaves, left_internal, left_supplied = left
    right_leaves, right_input_power, right_internal, right_supplied = right
    for start_code, input_power, leaves, internal, supplied in (
            (1, 1, left_leaves, left_internal, left_supplied),
            (code, right_input_power, right_leaves, right_internal, right_supplied)):
        root = start_code, input_power, 1, 1
        results.append(tree_source(c, shape, leaves, root, internal, supplied, one, True))
    return c.add(*results) if one else results[0]+results[1]


def static_flags(shape, leaves):
    """Compile source-known flags and count singleton-child edges."""
    cursor = 0

    def visit(node):
        nonlocal cursor
        if node is None:
            sigma = leaves[cursor][4]
            cursor += 1
            assert sigma in (1, 2)
            return sigma, 0
        sigma, first_count = visit(node[0])
        tau, second_count = visit(node[1])
        return max(sigma, tau), first_count+second_count+(sigma == 2)+(tau == 2)

    flag, count = visit(shape)
    assert cursor == len(leaves)
    return flag, count


def static_tree_source(c, shape, leaves, root, internal, supplied, one=False):
    """Only source-known flags control equation generation; vectors have4 coordinates."""
    leaf_cursor, node_cursor = 0, 0
    targets, values = list(internal)+[root], []

    def visit(node):
        nonlocal leaf_cursor, node_cursor
        if node is None:
            value = leaves[leaf_cursor]
            leaf_cursor += 1
            return value
        first, second = visit(node[0]), visit(node[1])
        target, local = targets[node_cursor], supplied[node_cursor]
        node_cursor += 1
        values.append(static_source(c, first, second, target, local, one))
        return tuple(target)+(max(first[4], second[4]),)

    assert visit(shape)[:4] == tuple(root)
    assert leaf_cursor == len(leaves) and node_cursor == len(targets) == len(supplied)
    if not one:
        return tuple(r for row in values for r in row)
    value = values[0]
    for following in values[1:]:
        value = c.add(value, following)
    return value


def static_accept_source(c, x, scale, offset, shape, leaves, input_power, internal, supplied, one=False):
    root = c.add(c.mul(scale, x), offset), input_power, 1, 1
    return static_tree_source(c, shape, leaves, root, internal, supplied, one)


def static_two_stack_accept_source(c, x, scale, offset, shape, left, right, one=False):
    code = c.add(c.mul(scale, x), offset)
    left_leaves, left_internal, left_supplied = left
    right_leaves, right_power, right_internal, right_supplied = right
    first = static_tree_source(c, shape, left_leaves, (1, 1, 1, 1),
                               left_internal, left_supplied, one)
    second = static_tree_source(c, shape, right_leaves, (code, right_power, 1, 1),
                                right_internal, right_supplied, one)
    return c.add(first, second) if one else first+second


def tree_checks():
    rng = random.Random(613114)
    small = words((0, 1), 2)
    nonzero = zero = 0
    for t in range(2, 15):
        for trial in range(36):
            if trial % 2:
                boundaries = [rng.choice(small) for _ in range(t+1)]
                leaves = [(boundaries[i], boundaries[i+1], rng.randrange(2)) for i in range(t)]
            else:
                leaves = [(rng.choice(small), rng.choice(small), rng.randrange(2)) for _ in range(t)]
            expected = ((), (), 0)
            for following in leaves:
                expected = compose(expected, following)
            for style in ('left', 'right', 'balanced'):
                shape = cone.tree_shape(t, style)
                merged, records, cursor = compile_tree(shape, leaves)
                assert cursor == t and merged == expected
                if merged is None:
                    zero += 1
                    continue
                m = t-1
                root = records[-1][0]
                internal = [row[0] for row in records[:-1]]
                supplied = [row[1] for row in records]
                typed_leaves = [descriptor(leaf) for leaf in leaves]
                for one in (False, True):
                    c = Circuit()
                    value = tree_source(c, shape, typed_leaves, root, internal, supplied, one)
                    assert value == (0 if one else (0,)*(10*m))
                    assert c.counts == {'M':(13+10*one)*m, 'A':(18+20*one)*m-int(one)}
                assert 5*(t-2)+4*(t-1) == 9*t-14
                wrong_root = list(root)
                wrong_root[4] = 3-wrong_root[4]
                assert any(tree_source(Circuit(), shape, typed_leaves, wrong_root, internal, supplied))
                if internal:
                    changed = [list(row) for row in internal]
                    changed[0][4] = 3-changed[0][4]
                    assert any(tree_source(Circuit(), shape, typed_leaves, root, changed, supplied))
                _, K = static_flags(shape, typed_leaves)
                static_internal = [row[:4] for row in internal]
                for one in (False, True):
                    c = Circuit()
                    value = static_tree_source(c, shape, typed_leaves, root[:4],
                                               static_internal, supplied, one)
                    assert value == (0 if one else (0,)*(7*m+K))
                    assert c.counts == {'M':(10+7*one)*m+K*one,
                                       'A':(15+14*one)*m+(2*K-1)*one}
                assert 4*(t-2)+4*(t-1) == 8*t-12
                if static_internal:
                    changed = [list(row) for row in static_internal]
                    changed[0][0] += 1
                    assert any(static_tree_source(Circuit(), shape, typed_leaves, root[:4], changed, supplied))
                nonzero += 1
    return dict(nonzero_fixed_trees=nonzero, zero_products=zero, shapes=['left', 'right', 'balanced'],
                graph='31(t-1)', equations='10(t-1)', positive_internal_witnesses='9t-14',
                polynomial='61t-62', scope='Fixed typed leaves and tree; five supplied root coordinates',
                compiled_flags=dict(graph='25(t-1)', equations='7(t-1)+K',
                                    positive_internal_witnesses='8t-12', polynomial='46(t-1)+3K-1',
                                    K='number of singleton-child edges in the fixed tree'))


def endpoint_checks():
    cases = pairs = binding_checks = 0
    # Include both cone and singleton endpoints, and all prefix boundary bits.
    for scale, offset in ((1, 0), (2, 0), (2, 1), (4, 3), (8, 7)):
        for x in range(1, 65):
            initial = decode(scale*x+offset)
            for use_empty_test in (False, True):
                right_leaves = [((bit,), (), 0) for bit in initial]
                right_leaves.append(((), (), int(use_empty_test)))
                if len(right_leaves) == 1:
                    right_leaves.append(((), (), 0))
                t, m = len(right_leaves), len(right_leaves)-1
                shape = cone.tree_shape(t, 'balanced')
                merged, records, _ = compile_tree(shape, right_leaves)
                assert merged == (initial, (), int(use_empty_test))
                typed_leaves = [descriptor(leaf) for leaf in right_leaves]
                internal = [row[0] for row in records[:-1]]
                supplied = [row[1] for row in records]
                input_power = 1 << len(initial)
                for candidate in (x, x+1):
                    c = Circuit()
                    residuals = accept_source(c, candidate, scale, offset, shape, typed_leaves,
                                              input_power, internal, supplied)
                    assert (not any(residuals)) == (candidate == x)
                    assert len(residuals) == 10*m-1 and c.counts == {'M':13*m, 'A':18*m-2}
                    c = Circuit()
                    value = accept_source(c, candidate, scale, offset, shape, typed_leaves,
                                          input_power, internal, supplied, True)
                    assert value == sum(r*r for r in residuals)
                    assert c.counts == {'M':23*m-1, 'A':38*m-5}
                    binding_checks += 1
                assert 5*(t-2)+4*(t-1)+1 == 9*t-13
                left_leaves = [((), (), int(use_empty_test)) for _ in range(t)]
                left_merged, left_records, _ = compile_tree(shape, left_leaves)
                assert left_merged[:2] == ((), ())
                left = ([descriptor(leaf) for leaf in left_leaves],
                        [row[0] for row in left_records[:-1]], [row[1] for row in left_records])
                right = (typed_leaves, input_power, internal, supplied)
                for one in (False, True):
                    c = Circuit()
                    value = two_stack_accept_source(c, x, scale, offset, shape, left, right, one)
                    assert value == (0 if one else (0,)*(20*m-2))
                    assert c.counts == {'M':(26+20*one)*m-1-2*one,
                                        'A':(36+40*one)*m-5-5*one}
                assert 2*(5*(t-2)+4*(t-1))+1 == 18*t-27
                static_left = left[0], [row[:4] for row in left[1]], left[2]
                static_right = right[0], right[1], [row[:4] for row in right[2]], right[3]
                _, Kl = static_flags(shape, static_left[0])
                _, Kr = static_flags(shape, static_right[0])
                for one in (False, True):
                    c = Circuit()
                    value = static_accept_source(c, x, scale, offset, shape, typed_leaves, input_power,
                                                 static_right[2], supplied, one)
                    assert value == (0 if one else (0,)*(7*m+Kr))
                    assert c.counts == {'M':(10+7*one)*m+1+Kr*one,
                                       'A':(15+14*one)*m+1+(2*Kr-1)*one}
                    c = Circuit()
                    value = static_two_stack_accept_source(c, x, scale, offset, shape,
                                                           static_left, static_right, one)
                    K = Kl+Kr
                    assert value == (0 if one else (0,)*(14*m+K))
                    assert c.counts == {'M':(20+14*one)*m+1+K*one,
                                       'A':(30+28*one)*m+1+(2*K-1)*one}
                assert 4*(t-2)+4*(t-1)+1 == 8*t-11
                assert 2*(4*(t-2)+4*(t-1))+1 == 16*t-23
                assert any(static_two_stack_accept_source(Circuit(), x+1, scale, offset, shape,
                                                         static_left, static_right))
                pairs += 1
                cases += 1
    # Nonempty image cannot give an empty endpoint even when the input matches.
    shape = cone.tree_shape(2, 'balanced')
    leaves = [((), (0,), 0), ((), (), 0)]
    merged, records, _ = compile_tree(shape, leaves)
    assert merged == ((), (0,), 0)
    assert any(accept_source(Circuit(), 1, 1, 0, shape, [descriptor(leaf) for leaf in leaves],
                             1, [], [records[0][1]]))
    return dict(one_stack_endpoint_cases=cases, input_binding_checks=binding_checks,
                paired_endpoint_cases=pairs, nonempty_image_rejected=True,
                one_stack=dict(graph='31t-33', equations='10t-11', positive_witnesses='9t-13',
                               polynomial='61t-67'),
                two_stack=dict(graph='62t-68', equations='20t-22', positive_witnesses='18t-27',
                               polynomial='122t-135'),
                compiled_flags_one_stack=dict(graph='25(t-1)+2', equations='7(t-1)+K',
                                              positive_witnesses='8t-11', polynomial='46(t-1)+3K+1'),
                compiled_flags_two_stack=dict(graph='50(t-1)+2', equations='14(t-1)+K',
                                              positive_witnesses='16t-23', polynomial='92(t-1)+3K+1'),
                scope='t>=2, fixed words/tree; affine ordinary-input loader included, state control not included')


def verify():
    return dict(status='PASS_TYPED_PREFIX_SINGLETON_MERGE31',
                graph=dict(operations=31, multiplications=13, additions=18,
                           positive_auxiliary_witnesses=4, equations=10),
                polynomial=dict(operations=60, multiplications=23, additions=37),
                scalar=scalar_checks(), domains=domain_and_identity_checks(),
                actions=action_checks(), trees=tree_checks(), endpoints=endpoint_checks(),
                limits='Input descriptor powers, code bounds and flags are external typing. '
                       'Output typing and exact singleton/cone domains are proved. '
                       'Fixed-word endpoint certificates include ordinary input. '
                       'Uniform selected-word/control/tree arithmetic remains unpaid; no complete bound improvement.')


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
    print('31=13M+18A; 4 positive auxiliaries, 10 equations; polynomial60; fixed-word ordinary endpoints paid.')
