"""Exact sequential evaluator, conditional12 transports, finite-prefix lemma."""
from itertools import product
from pathlib import Path
import json
import sympy as sp


ALPHABET = (1, 2)
BASE = 3
OUTPUTS = ((1,), (2,), (1, 1), (1, 2), (2, 1), (2, 2),
           (1, 1, 1), (1, 2, 1), (2, 1, 2), (2, 2, 2))
SCHEDULE = [
    ('trim', '-', 'N', 'A'), ('append', '+', 'trim', 'U'),
    ('content_left', '*', 'R', 'append'),
    ('start', '-', 'N', 'n0'), ('end', '*', 'nh', 'Q'),
    ('content_inner', '+', 'start', 'end'),
    ('content_right', '*', 'b', 'content_inner'),
    ('length_left', '*', 'R', 'W'), ('length_start', '-', 'Z', 'L0'),
    ('length_end', '*', 'Lh', 'Q'),
    ('length_right', '+', 'length_start', 'length_end'),
    ('phase_left', '*', 'R', 'F')]
EQUALITIES = [('content_left', 'content_right'), ('length_left', 'length_right'),
              ('phase_left', 'S')]
PREFIX_SCHEDULE = [('input_tail', '*', 'Ls', 'V'), ('input_rhs', '+', 'Ns', 'input_tail'),
                   ('output_tail', '*', 'L', 'T'), ('output_rhs', '+', 'N', 'output_tail')]


def words(maximum):
    return [w for length in range(maximum+1) for w in product(ALPHABET, repeat=length)]


def code(word):
    return sum(a*BASE**i for i, a in enumerate(word))


def apply(images, word):
    return tuple(child for i, a in enumerate(word) for child in images[i % len(images)][a])


def run(schedule, values):
    env = dict(values)
    for name, op, left, right in schedule:
        assert name not in env
        a, b = env[left], env[right]
        env[name] = a*b if op == '*' else a+b if op == '+' else a-b
    return env


def source_check():
    names = 'R Q N A U Z W S F n0 nh L0 Lh b Ns Ls O L V T'.split()
    sym = dict(zip(names, sp.symbols(' '.join(names))))
    R, Q, N, A, U, Z, W, S, F, n0, nh, L0, Lh, b = [sym[n] for n in names[:14]]
    source = [R*(N-A+U)-b*(N-n0+nh*Q), R*W-Z+L0-Lh*Q, R*F-S]
    env = run(SCHEDULE, sym)
    for (a, b), residual in zip(EQUALITIES, source):
        assert sp.expand(env[a]-env[b]-residual) == 0
    assert len(SCHEDULE) == 12
    assert sum(op == '*' for _, op, _, _ in SCHEDULE) == 6
    prefix = run(PREFIX_SCHEDULE, sym)
    assert sp.expand(prefix['input_rhs']-sym['N']-(sym['Ns']+sym['Ls']*sym['V']-sym['N'])) == 0
    assert sp.expand(prefix['output_rhs']-sym['O']-(sym['N']+sym['L']*sym['T']-sym['O'])) == 0
    return dict(operations=12, multiplications=6, additions=6, schedule=SCHEDULE,
                equalities=EQUALITIES, source=[sp.sstr(x) for x in source],
                prefix_gluing=dict(operations=4, multiplications=2, additions=2,
                                   schedule=PREFIX_SCHEDULE),
                scope='Only transport/phase and conditional prefix gluing; all table and mask costs excluded.')


def families():
    for p in (1, 2, 3):
        for offset, slope in product(range(len(OUTPUTS)), (1, 3, 7)):
            images = [{a: OUTPUTS[(offset+2*r+slope*(a-1)) % len(OUTPUTS)]
                       for a in ALPHABET} for r in range(p)]
            for seed in words(3):
                first = apply(images, seed)
                if seed and len(first) > len(seed) and first[:len(seed)] == seed:
                    yield images, seed


def direct_prefix(images, seed, length):
    word = seed
    while len(word) < length:
        nxt = apply(images, word)
        assert nxt[:len(word)] == word and len(nxt) > len(word)
        word = nxt
    return word[:length]


def packed_check(images, seed, rows, final_queue):
    p, shift = len(images), len(seed) % len(images)
    h = len(rows)
    assert p >= 2 and h > 0 and h % p == 0
    first_queue = apply(images, seed)[len(seed):]
    terms = []
    for i, (queue, after, output) in enumerate(rows):
        phase, nxt = i % p, (i+1) % p
        assert output == images[(shift+phase) % p][queue[0]]
        n, nn = code(queue), code(after)
        L, LL = BASE**len(queue), BASE**len(after)
        u, lam = code(output), BASE**(len(output)-1)
        assert BASE*nn == n-queue[0]+u*L and LL == lam*L
        terms.append((n, queue[0], u*L, L, lam*L, phase, nxt))
    largest = max([BASE**len(first_queue), BASE**len(final_queue), p]
                  + [value for row in terms for value in row])
    R = BASE
    while R <= 8*largest:
        R *= BASE
    values = dict(R=R, Q=R**h, b=BASE, n0=code(first_queue), nh=code(final_queue),
                  L0=BASE**len(first_queue), Lh=BASE**len(final_queue))
    for j, name in enumerate(('N', 'A', 'U', 'Z', 'W', 'S', 'F')):
        values[name] = sum(row[j]*R**i for i, row in enumerate(terms))
    env = run(SCHEDULE, values)
    assert all(env[a] == env[b] for a, b in EQUALITIES)
    assert all(values[name] > 0 for name in ('N', 'A', 'U', 'Z', 'W', 'S', 'F'))
    selected = []
    for phase, a in product(range(p), ALPHABET):
        positions = [i for i, row in enumerate(rows) if i % p == phase and row[0][0] == a]
        D = sum(R**i for i in positions)
        T = sum(BASE**len(rows[i][0])*R**i for i in positions)
        output = images[(shift+phase) % p][a]
        selected.append((phase, a, D, T, code(output), BASE**(len(output)-1)))
    assert sum(D for r, a, D, T, u, lam in selected) == sum(R**i for i in range(h))
    assert sum(a*D for r, a, D, T, u, lam in selected) == values['A']
    assert sum(r*D for r, a, D, T, u, lam in selected) == values['S']
    assert sum(((r+1) % p)*D for r, a, D, T, u, lam in selected) == values['F']
    assert sum(T for r, a, D, T, u, lam in selected) == values['Z']
    assert sum(u*T for r, a, D, T, u, lam in selected) == values['U']
    assert sum(lam*T for r, a, D, T, u, lam in selected) == values['W']
    cycle = sum(R**(p*j) for j in range(h//p))
    for phase in range(p):
        assert sum(D for r, a, D, T, u, lam in selected if r == phase) == R**phase*cycle
    return values['Q'].bit_length(), p


def evaluator_checks():
    cases = steps = invariant_checks = packed = phase_masks = 0
    seed_targets = later_targets = bounded_absent = padded = variable_length = 0
    scalar_rule_tests = wrong_read_rejections = 0
    max_bits = 0
    for images, seed in families():
        p = len(images)
        h = 6*p
        queue = apply(images, seed)[len(seed):]
        consumed, rows = (), []
        target_first = {}
        for i in range(h):
            assert queue
            output = images[(len(seed)+i) % p][queue[0]]
            after = queue[1:]+output
            for proposed in ALPHABET:
                alternative = images[(len(seed)+i) % p][proposed]
                numerator = code(queue)-proposed+code(alternative)*BASE**len(queue)
                assert (numerator % BASE == 0) == (proposed == queue[0])
                scalar_rule_tests += 1
                if proposed != queue[0]:
                    wrong_read_rejections += 1
                else:
                    assert numerator//BASE == code(after)
            target_first.setdefault(queue[0], i)
            rows.append((queue, after, output))
            consumed += queue[:1]
            queue = after
            assert apply(images, seed+consumed) == seed+consumed+queue
            invariant_checks += 1
        expected = direct_prefix(images, seed, len(seed)+h+len(queue))
        assert expected == seed+consumed+queue
        assert expected[len(seed):len(seed)+h] == consumed
        cases += 1
        steps += h
        variable_length += any(len({len(m[a]) for a in ALPHABET}) > 1 for m in images)
        for target in ALPHABET:
            if target in seed:
                seed_targets += 1
            elif target in consumed:
                later_targets += 1
                first = target_first[target]+1
                end = ((first+p-1)//p)*p
                assert target in tuple(row[0][0] for row in rows[:end])
                assert end % p == 0 and end <= h
                padded += end > first
                if p >= 2:
                    bits, masks = packed_check(images, seed, rows[:end], rows[end-1][1])
                    max_bits = max(max_bits, bits)
                    phase_masks += masks
                    packed += 1
            else:
                bounded_absent += 1
        if p >= 2:
            bits, masks = packed_check(images, seed, rows, queue)
            max_bits = max(max_bits, bits)
            phase_masks += masks
            packed += 1
    assert min(seed_targets, later_targets, bounded_absent, padded, variable_length) > 0
    return dict(productive_seed_cases=cases, fifo_steps=steps, invariant_checks=invariant_checks,
                scalar_selected_rule_tests=scalar_rule_tests,
                wrong_read_digit_rejections=wrong_read_rejections,
                symbol_dependent_image_length_cases=variable_length,
                packed_whole_cycle_tuples=packed, periodic_phase_masks_checked=phase_masks,
                joint_selector_form_checks=7*packed, immediate_seed_targets=seed_targets,
                witnessed_later_targets=later_targets, cycle_extensions_after_target=padded,
                bounded_unobserved_targets=bounded_absent, largest_time_power_bits=max_bits,
                scope='Bounded nonobservations are not negative occurrence decisions.')


def prefix_checks():
    candidates = accepted = rejected = initial_occurrences = gluing = 0
    for images, seed in families():
        for suffix in words(4):
            w = seed+suffix
            image = apply(images, w)
            prolongable = image[:len(w)] == w
            expected = direct_prefix(images, seed, len(w))
            candidates += 1
            if not prolongable:
                rejected += 1
                continue
            assert w == expected
            assert len(image) > len(w)
            accepted += 1
            for marker in ALPHABET:
                if marker in w:
                    assert marker in expected
                    initial_occurrences += marker in seed
                    if marker not in seed:
                        Ns, Ls, N, L, O = code(seed), BASE**len(seed), code(w), BASE**len(w), code(image)
                        V, T = code(suffix), code(image[len(w):])
                        assert min(V, T) > 0
                        env = run(PREFIX_SCHEDULE, dict(Ns=Ns, Ls=Ls, N=N, L=L, O=O, V=V, T=T))
                        assert env['input_rhs'] == N and env['output_rhs'] == O
                        gluing += 1
        # Every directly generated prefix is self-extending, not only full generations.
        prefix = direct_prefix(images, seed, len(seed)+8)
        for end in range(len(seed), len(prefix)+1):
            w = prefix[:end]
            assert apply(images, w)[:len(w)] == w
    assert min(accepted, rejected, gluing, initial_occurrences) > 0
    return dict(candidate_words=candidates, accepted_self_extending=accepted,
                rejected_nonprolongable=rejected, initial_seed_marker_checks=initial_occurrences,
                positive_prefix_gluings=gluing,
                scope='Finite checks of both implications; the unbounded proof is in the note.')


def verify():
    return dict(status='PASS_FIFO_PD0L_CONDITIONAL_TRANSPORT12', source=source_check(),
                evaluator=evaluator_checks(), finite_prefix=prefix_checks(),
                proof='../1980/EXPLORATION_FIFO_PD0L.md',
                review='Author and two independent complete scoped proof/source reviews and fresh receipt checks PASS.',
                scope='Exact evaluator and finite-prefix equivalences. Conditional12 transport/phase '
                      'or4 prefix-gluing operations; all joint selection, weighting, geometry, bounds, '
                      'mask/kernel, adapters and raw-input obligations remain unpaid.')


if __name__ == '__main__':
    result = verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(result['status'])
    print(result['evaluator'])
    print(result['finite_prefix'])
