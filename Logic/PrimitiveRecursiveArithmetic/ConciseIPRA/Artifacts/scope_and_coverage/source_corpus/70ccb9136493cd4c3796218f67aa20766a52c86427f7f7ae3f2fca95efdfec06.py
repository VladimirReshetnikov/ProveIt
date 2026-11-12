"""Generate and check R certificates; kernel.py never imports this file."""
import ast
import copy
import hashlib
import json
import pathlib
import platform
import random
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor

from producer import (Z, V, S, R, W, J, Eq, Q, D, Proof, fresh, num, same,
                      encode, hyp, computation, refl, congruence, symmetry,
                      trans, di, de, qe, closure, prove_instance, j_zero,
                      j_successor, packet, evaluate)

ROOT = pathlib.Path(__file__).resolve().parent


def load_kernel(path):
    tree = ast.parse(path.read_text())
    tree.body = [n for n in tree.body if isinstance(n, (
        ast.Import, ast.ImportFrom, ast.Assign, ast.FunctionDef))]
    env = {}
    exec(compile(ast.fix_missing_locations(tree), str(path), 'exec'), env)
    return env


def check(env, data):
    env['k'] = 0
    try:
        env['q'] = copy.deepcopy(data).pop
        return bool(env['c'](env['q'](), []))
    except Exception:
        return False


def identity_body(seed, n):
    return Eq(R(n, seed, lambda u, v: v), S(seed))


def identity_step(seed, z):
    return trans(computation(R(S(z), seed, lambda u, v: v)),
                 hyp(identity_body(seed, z)))


def identity_closure(seed):
    y = fresh('n')
    return closure(y, identity_body(seed, V(y)),
                   lambda z: identity_step(seed, z))


def false_base_step(z):
    # From 0=1, transport the counter of R(_,z;0).
    bad = hyp(Eq(Z, num(1)))
    f = lambda n: R(n, z, lambda u, v: Z)
    middle = congruence(bad, f)
    left = symmetry(computation(f(Z)))
    right = computation(f(num(1)))
    return trans(trans(trans(left, middle), right), bad)


def main():
    kernel = load_kernel(ROOT / 'kernel.py')
    reference = load_kernel(ROOT / 'kernel_unpacked.py')
    cases, semantics = [], []

    def add(name, proof, meaning):
        data = packet(proof)
        cases.append({'name': name, 'packet': data, 'accept': True, 'meaning': meaning})
        if proof.goal[0] == 'eq':
            left, right = (evaluate(t) for t in proof.goal[1:])
            assert left == right, (name, left, right)
            semantics.append({'name': name, 'left': left, 'right': right})
        return data

    def raw(name, data, accept, meaning):
        cases.append({'name': name, 'packet': data, 'accept': accept, 'meaning': meaning})
        return data

    def primitive(name, n, seed, body, meaning):
        return add(name, computation(R(n, seed, body)), meaning)

    primitive('zero_seed_successor', Z, Z, lambda u, v: Z,
              'R(0,0;0)=1: the numerical base is successor seeded.')
    primitive('zero_arbitrary_seed', Z, num(4), lambda u, v: u,
              'R(0,4;u)=5, independently of the update body.')
    primitive('counter_slot', num(3), num(7), lambda u, v: u,
              'The predecessor counter is 2, distinct from the seed and previous state.')
    primitive('state_slot', num(3), num(7), lambda u, v: v,
              'The state slot is the earlier R value, not the predecessor counter.')
    primitive('counter_below_successor', num(3), num(7), lambda u, v: S(u),
              'Opening a counter occurrence under an additional numerical binder.')
    primitive('state_below_successor', num(3), num(7), lambda u, v: S(v),
              'Opening a previous-state occurrence under an additional binder.')
    both_body = lambda u, v: R(v, u, lambda j, w: w)
    both = primitive('both_slots_nested', num(1), num(2), both_body,
                     'Nested R uses outer state as counter and outer counter as seed.')
    counter_alias = copy.deepcopy(cases[2]['packet'])
    counter_alias[-1][0][2] = 4
    raw('counter_even_alias', counter_alias, True, 'Coordinates 3 and 4 alias the counter.')
    state_alias = copy.deepcopy(cases[3]['packet'])
    state_alias[-1][0][2] = 2
    state_alias[-1][1][2] = 2
    raw('state_even_alias', state_alias, True, 'Coordinates 1 and 2 alias the previous state.')
    wrong = copy.deepcopy(both)
    wrong[-1][1][0], wrong[-1][1][1] = wrong[-1][1][1], wrong[-1][1][0]
    raw('swapped_counter_state', wrong, False,
        'Swapping the two substitutions would assert a false ground equation.')

    cumulative = lambda u, v: R(v, u, lambda j, w: S(w))
    retained = primitive('original_update_retained', num(3), num(2), cumulative,
                         'The recursive state keeps the original update, including its counter binder.')
    frozen = lambda u, v: cumulative(num(2), v)
    bad_rhs = cumulative(num(2), R(num(2), num(2), frozen))
    bad = copy.deepcopy(retained)
    bad[-1][1] = encode(bad_rhs)
    assert evaluate(bad_rhs) == 12
    raw('frozen_counter_in_recursive_state', bad, False,
        'Freezing the update counter inside the recursive state would falsely identify 9 and 12.')

    add('bouncing_predecessor_zero', computation(W(Z)), 'W(0)=1.')
    add('bouncing_predecessor_successor', computation(W(num(5))), 'W(5)=4 directly.')
    add('derived_reflexivity', refl(num(4)), 'Reflexivity follows from W(Sa)=a and transport.')
    add('transported_successor_congruence', congruence(computation(W(num(5))), S),
        'Equality transport under a successor context.')
    h = lambda u, v: R(v, u, lambda j, w: S(w))
    add('ordinary_recursion_base', j_zero(num(3), h), 'Expanded proof of J_h(0,3)=3.')
    add('ordinary_recursion_step', j_successor(num(2), num(3), h),
        'Expanded proof of J_h(3,3)=h(2,J_h(2,3)); h uses both inputs.')

    y = fresh('n')
    identity = prove_instance(y, identity_body(num(2), V(y)),
                             computation(R(Z, num(2), lambda u, v: v)),
                             lambda z: identity_step(num(2), z), num(4))
    identity_data = add('genuine_equation_induction', identity,
                        'DI/DE/QE plus a genuinely used equation induction hypothesis.')
    wrong_mode = copy.deepcopy(identity_data)
    chosen = next(i for i, cell in enumerate(wrong_mode[:-1])
                  if cell == [0, [0]])
    wrong_mode[chosen][0] = []
    raw('induction_with_wrong_case_mode', wrong_mode, False,
        'The same proof requires the IH and fails with only the zero base.')

    y = fresh('y')
    false_closure = closure(y, Eq(V(y), num(1)), false_base_step, induction=False)
    false_data = add('conditional_false_base', false_closure,
                     'Q_y(y=1) retains its conditional-universal meaning by Case introduction.')
    case_location = next(i for i, cell in enumerate(false_data[:-1])
                         if cell == [[], [0]])
    bad = copy.deepcopy(false_data)
    bad[case_location][0] = 0
    raw('false_base_wrong_induction_mode', bad, False,
        'A progression assumption does not supply the required false zero base.')
    for label, marker in [('null', None), ('empty_object', {}), ('empty_string', '')]:
        alias = copy.deepcopy(false_data)
        alias[case_location][0] = marker
        raw('case_annotation_' + label, alias, True,
            'This falsy marker is an instruction annotation, not numerical syntax.')

    # An outer compound case keeps an arbitrary numerical parameter passive
    # while an inner equation induction introduces a different counter.
    a, n = fresh('a'), fresh('n')
    body = Q(n, identity_body(V(a), V(n)))
    double = closure(a, body, lambda z: identity_closure(S(z)), induction=False)
    double_data = add('nested_parameter_and_counter', double,
                      'Outer Case and inner Ind preserve a captured initializer and counter.')
    capture = copy.deepcopy(double_data)
    captured = False
    for cell in capture[:-1]:
        if (isinstance(cell, list) and len(cell) == 2 and isinstance(cell[0], list)
                and len(cell[0]) == 2 and isinstance(cell[0][0], list)
                and len(cell[0][0]) == 3 and cell[0][0][0] == -2):
            cell[0][0][0] = -1
            captured = True
            break
    assert captured
    raw('captured_inner_counter', capture, False,
        'The inner counter has been replaced by the distinct outer parameter.')

    # The explicit witness coordinate is used, so malformed witness images
    # cannot disappear merely because the coordinate happens to be vacuous.
    x, n, z = fresh('x'), fresh('n'), fresh('eigen')
    direct_formula = D(x, n, identity_body(V(x), V(n)))
    direct = di(direct_formula, num(2), z, identity_step(num(2), V(z)))
    direct_data = add('nonvacuous_paired_witness', direct,
                      'The selected existential witness becomes the recursion initializer.')
    location = next(i for i, cell in enumerate(direct_data[:-1]) if cell == [0, [[0]]])
    for name, image in [('free_positive_witness', 1), ('future_negative_witness', -1)]:
        bad = copy.deepcopy(direct_data)
        bad[location][1] = image
        raw(name, bad, False, 'A used witness must be valid at numerical root before insertion.')

    # The passive parameter appears under a nested R update.
    y = fresh('parameter')
    f = lambda p: R(num(1), Z, lambda u, v: R(v, p, lambda j, w: w))
    b = computation(f(V(y))).goal
    nested = prove_instance(y, b, computation(f(Z)),
                            lambda z: computation(f(S(z))), num(4))
    add('nested_update_passive_parameter', nested,
        'A passive parameter survives two local R binders, DI, DE and QE.')
    y = fresh('counter')
    b = j_successor(V(y), num(3), h).goal
    j_bound = prove_instance(y, b, j_successor(Z, num(3), h),
                             lambda z: j_successor(S(z), num(3), h), num(2))
    add('ordinary_recursion_bound_counter', j_bound,
        'The general J successor derivation is closed by DI/DE and specialized by QE.')

    true_goal = [[0, 0, 0], [0]]
    false_major = [[0, 0, 0], 0]
    raw('failed_major_cannot_fall_through', [[0, 0], [false_major, 0], true_goal], False,
        'The failed major cannot become a successful computation fallback.')
    raw('canonical_false', [[0, 0], [0, [0]]], False, 'Zero is not successor zero.')
    raw('wrong_old_base', [[0, 0], [[0, 0, 0], 0]], False,
        'The old zero-seeded computation equation is not an axiom of R.')
    raw('four_child_goal', [[0, 0], [0, 0, 0, 0]], False, 'Malformed formula arity.')
    raw('free_negative_goal', [[0, 0], [-1, -1]], False, 'The public goal must be closed.')
    raw('two_child_counter', [[0, 0], [[[0, 0], 0, 0], 0]], False,
        'The starred fixed-arity call independently rejects a non-singleton counter.')
    raw('three_child_counter', [[0, 0], [[[0, 0, 0], 0, 0], 0]], False,
        'A nested R counter is not a literal successor redex.')
    raw('free_update_coordinate', [[0, 0], [[[0], 0, 5], 0]], False,
        'A body has exactly two local numerical slots, plus actual outer parameters.')
    raw('object_in_syntax', [[0, 0], [[0, {}, 0], [{}]]], False,
        'Unlike the separate implementation experiment, this kernel has strict list syntax.')

    failures = []
    for case in cases:
        for name, env in [('starred', kernel), ('unpacked', reference)]:
            got = check(env, case['packet'])
            if got != case['accept']:
                failures.append({'name': case['name'], 'kernel': name, 'got': got})
    assert not failures, failures

    # Independent finite arithmetic check of the compiler, not a metatheorem.
    numerical = 0
    for seed in range(6):
        for steps in range(7):
            for update in [lambda u, v: u, lambda u, v: v,
                           lambda u, v: S(v), h]:
                state = seed
                for k in range(steps):
                    state = evaluate(update(num(k), num(state)))
                assert evaluate(J(num(steps), num(seed), update)) == state
                numerical += 1

    # Starred arity fusion is compared with the explicit-unpack reference on
    # deterministic malformed proof/term mutations.
    def positions(t, p=()):
        yield p
        if isinstance(t, list):
            for i, v in enumerate(t): yield from positions(v, p + (i,))
    def replace(t, p, value):
        if not p: return value
        out = copy.deepcopy(t)
        node = out
        for i in p[:-1]: node = node[i]
        node[p[-1]] = value
        return out
    rng = random.Random(20261109)
    atoms = [0, 1, -1, -2, 5, [], [0], [0, 0], [0, 0, 0], [0, 0, 0, 0],
             None, True, False, 0.5, {}, {'bad': 0}, '', 'a']
    mutations = 0
    for case in cases:
        ps = list(positions(case['packet']))
        for _ in range(35):
            mutated = replace(case['packet'], rng.choice(ps), copy.deepcopy(rng.choice(atoms)))
            assert check(kernel, mutated) == check(reference, mutated), (case['name'], mutated)
            mutations += 1

    def cli(job):
        case, optimize = job
        cmd = [sys.executable] + (['-O'] if optimize else []) + [str(ROOT / 'kernel.py')]
        result = subprocess.run(cmd, input=json.dumps(case['packet']), text=True,
                                capture_output=True, timeout=15)
        expected = 'ACCEPT' if case['accept'] else 'REJECT'
        assert result.stdout.strip() == expected, (case['name'], optimize, result.stdout, result.stderr)
        assert (result.returncode == 0) == case['accept'], (case['name'], optimize)
        return 1
    with ThreadPoolExecutor(max_workers=4) as pool:
        cli_runs = sum(pool.map(cli, [(c, o) for c in cases for o in (False, True)]))

    (ROOT / 'certificates.json').write_text(json.dumps({'cases': cases}, indent=2) + '\n')
    results = {
        'python': platform.python_version(), 'kernel_sha256': hashlib.sha256((ROOT / 'kernel.py').read_bytes()).hexdigest(),
        'fixtures': len(cases), 'positive': sum(c['accept'] for c in cases),
        'negative': sum(not c['accept'] for c in cases), 'in_process_checks': 2 * len(cases),
        'normal_and_optimized_cli_runs': cli_runs, 'differential_mutations': mutations,
        'finite_compiler_examples': numerical, 'ground_equation_semantics': semantics,
        'failures': failures,
        'limits': 'Finite regression evidence, not a formal proof of universal soundness or bi-interpretability.'}
    (ROOT / 'validation.json').write_text(json.dumps(results, indent=2) + '\n')
    print(json.dumps(results, indent=2))


if __name__ == '__main__':
    main()
