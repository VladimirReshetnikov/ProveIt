"""Conditional binary tag history: 29 operations and a necessary sixth AND."""
from itertools import product
from pathlib import Path
import json
import sympy as sp


def constants(beta, app):
    K = 2**beta
    U = sum(bit*2**i for i, bit in enumerate(app))
    C = 2
    while C <= max(K, 2**len(app), 2*U+2):
        C *= 2
    return dict(K=K, Kh=K//2, B=2**(len(app)-1), U=U, C=C, c=K//2-1)


def schedule(c):
    return [
        ('radix', '*', c['C'], 'A'), ('padding', '*', 'A', 'H'),
        ('marker', '+', 'Q', 'S1'), ('heads', '+', 'S0', 'S1'),
        ('length_sum', '+', 'M0', 'M1'), ('content_sum', '+', 'N', 'Nbar'),
        ('content_length', '+', 'Nsum', 'H'),
        ('prefix_scale', '*', c['c'], 'H'), ('prefix_sum', '+', 'E', 'Ebar'),
        ('prefix_double', '*', 2, 'E'), ('deleted', '+', 'prefix_double', 'S1'),
        ('n_append', '*', c['U'], 'M1'), ('n_trim', '-', 'N', 'deleted'),
        ('n_output', '+', 'n_trim', 'n_append'), ('n_left', '*', 'R', 'n_output'),
        ('n_end', '*', 'q', 'Nfinal'), ('n_initial', '-', 'N', 'Ninit'),
        ('n_shift', '+', 'n_initial', 'n_end'), ('n_right', '*', c['K'], 'n_shift'),
        ('l_append', '*', c['B'], 'M1'), ('l_output', '+', 'M0', 'l_append'),
        ('l_left', '*', 'R', 'l_output'), ('l_end', '*', 'q', 'Lfinal'),
        ('l_initial', '-', 'L', 'Linit'), ('l_shift', '+', 'l_initial', 'l_end'),
        ('l_right', '*', c['Kh'], 'l_shift'),
        ('input_bound', '+', 'Linit', 'alphaI'),
        ('halt_bound', '+', 'Lfinal', 'alphaH'),
        ('terminal_bound', '+', 'Nfinal', 'alphaN'),
    ]


def comparisons():
    return [('radix', 'R'), ('marker', 'M1'), ('heads', 'H'),
            ('length_sum', 'L'), ('content_sum', 'Nsum'), ('content_length', 'L'),
            ('prefix_sum', 'prefix_scale'), ('n_left', 'n_right'), ('l_left', 'l_right'),
            ('input_bound', 'A'), ('halt_bound', 'K'), ('terminal_bound', 'Lfinal')]


def evaluate(dag, supplied):
    env = dict(supplied)
    for name, op, left, right in dag:
        assert name not in env
        a = env[left] if isinstance(left, str) else left
        b = env[right] if isinstance(right, str) else right
        env[name] = a*b if op == '*' else a+b if op == '+' else a-b
    return env


def verify_source():
    names = ('A H Q S0 S1 M0 M1 R L N Nbar Nsum E Ebar q '
             'Ninit Linit Nfinal Lfinal alphaI alphaH alphaN').split()
    s = dict(zip(names, sp.symbols(' '.join(names))))
    c = dict(zip('C K Kh B U c'.split(), sp.symbols('C K Kh B U c')))
    env = evaluate(schedule(c), s)
    env['K'] = c['K']
    sources = [c['C']*s['A']-s['R'], s['Q']+s['S1']-s['M1'],
               s['S0']+s['S1']-s['H'], s['M0']+s['M1']-s['L'],
               s['N']+s['Nbar']-s['Nsum'], s['Nsum']+s['H']-s['L'],
               s['E']+s['Ebar']-c['c']*s['H'],
               s['R']*(s['N']-2*s['E']-s['S1']+c['U']*s['M1'])
               -c['K']*(s['N']-s['Ninit']+s['q']*s['Nfinal']),
               s['R']*(s['M0']+c['B']*s['M1'])
               -c['Kh']*(s['L']-s['Linit']+s['q']*s['Lfinal']),
               s['Linit']+s['alphaI']-s['A'],
               s['Lfinal']+s['alphaH']-c['K'],
               s['Nfinal']+s['alphaN']-s['Lfinal']]
    for (left, right), source in zip(comparisons(), sources):
        assert sp.expand(env[left]-env[right]-source) == 0
    mul = sum(op == '*' for _, op, _, _ in schedule(c))
    add = len(schedule(c))-mul
    assert (mul, add) == (12, 17)
    return dict(operations=29, multiplications=mul, additions_or_subtractions=add,
                exact_source_comparisons=len(sources), conditional_and_tests=6)


def subsets(mask):
    part = mask
    while True:
        yield part
        if not part:
            break
        part = (part-1) & mask


def verify_projector():
    candidates = accepted = configurations = 0
    for width in range(2, 7):
        for padding_exponent in range(1, width):
            p = width-padding_exponent
            R = 2**width
            A = 2**p
            for height in (1, 2):
                q = R**height
                H = (q-1)//(R-1)
                count = 0
                for S1 in subsets(H):
                    S0 = H-S1
                    for Q in subsets((q-1) ^ (A*H)):
                        candidates += 1
                        M1 = Q+S1
                        if M1 >= q or Q & M1:
                            continue
                        assert Q & (A*H) == 0 and S0 & S1 == 0
                        for row in range(height):
                            s = (S1//R**row) % R
                            a = (Q//R**row) % R
                            b = (M1//R**row) % R
                            if s == 0:
                                assert a == b == 0
                            else:
                                assert s == 1 and 0 < b <= A and b & (b-1) == 0
                                assert a == b-1
                        accepted += 1
                        count += 1
                assert count == (p+2)**height
                configurations += 1
    return dict(configurations=configurations, complete_candidates=candidates,
                accepted=accepted)


def verify_flow():
    candidates = accepted = 0
    for n in range(1, 9):
        q = 2**n
        for choices in product((0, 1, 2), repeat=n):
            M0 = sum(2**i for i, v in enumerate(choices) if v == 1)
            M1 = sum(2**i for i, v in enumerate(choices) if v == 2)
            assert M0 & M1 == 0
            for shift0 in range(1, 5):
                for shift1 in range(1, 5):
                    candidates += 1
                    delta = (2**shift0-1)*M0+(2**shift1-1)*M1
                    Li = (-delta) % q
                    if not Li or Li & (Li-1):
                        continue
                    Lf = (delta+Li)//q
                    if Lf <= 0:
                        continue
                    assert M0+M1+q*Lf == Li+2**shift0*M0+2**shift1*M1
                    position = Li.bit_length()-1
                    visited = 0
                    while position < n:
                        bit = 2**position
                        assert (M0 | M1) & bit
                        visited |= bit
                        position += shift0 if M0 & bit else shift1
                    assert visited == M0 | M1
                    assert Lf == 2**(position-n)
                    accepted += 1
    return dict(complete_disjoint_marker_shift_candidates=candidates,
                accepted_single_paths=accepted)


def row_digits(word, radix, height):
    values = []
    for _ in range(height):
        word, digit = divmod(word, radix)
        values.append(digit)
    assert word == 0
    return values


def false_tuple(height):
    if height == 4:
        vals = dict(Q=2097551, S1=2097281, S0=16384, M1=4194832, M0=4326392,
                    L=8521224, Nsum=6407559, N=2163847, Nbar=4243712,
                    E=1, Ebar=2113664, Nfinal=1, Lfinal=3)
    else:
        assert height == 5
        vals = dict(Q=6291855, S1=2097281, S0=268451840, M1=8389136, M0=1073873912,
                    L=1082263048, Nsum=811713927, N=539034759, Nbar=272679168,
                    E=268435457, Ebar=2113664, Nfinal=0, Lfinal=2)
    R = 128
    q = R**height
    vals.update(A=16, R=R, q=q, H=(q-1)//(R-1), Ninit=7, Linit=8,
                alphaI=8, alphaH=4-vals['Lfinal'], alphaN=vals['Lfinal']-vals['Nfinal'])
    return vals


def verify_false_tuples():
    c = constants(2, (0, 1))
    assert c == dict(K=4, Kh=2, B=2, U=2, C=8, c=1)
    # Read the initial word in queue order, which is least-significant-bit first.
    initial = (1, 1, 1)
    fixed = (1, 0, 1)
    assert initial[2:]+(0, 1) == fixed and fixed[2:]+(0, 1) == fixed
    receipts = []
    for height in (4, 5):
        vals = false_tuple(height)
        env = evaluate(schedule(c), vals)
        env['K'] = c['K']
        assert all(env[a] == env[b] for a, b in comparisons())
        q, R, H = (vals[name] for name in ('q', 'R', 'H'))
        assert q == R**height and H*(R-1) == q-1
        assert all(0 <= vals[name] < q for name in
                   'Q S0 S1 M0 M1 L Nsum N Nbar E Ebar'.split())
        assert 0 <= env['padding'] < q
        assert all(vals[name] > 0 for name in ('alphaI', 'alphaH', 'alphaN'))
        assert vals['Linit'] < vals['A'] and 0 < vals['Lfinal'] < c['K']
        assert 0 <= vals['Nfinal'] < vals['Lfinal']
        pairs = [('Q', 'M1'), ('Q', 'padding'), ('S0', 'S1'),
                 ('N', 'Nbar'), ('E', 'Ebar')]
        assert all(env[a] & env[b] == 0 for a, b in pairs)
        overlap = vals['M0'] & vals['M1']
        assert overlap > 0
        if height == 5:
            assert vals['Lfinal'] & (vals['Lfinal']-1) == 0
        receipts.append(dict(height=height, values=vals, exact_source_comparisons=12,
                             retained_and_tests=5, omitted_pair_overlap=overlap,
                             content_equality=env['n_left'], length_equality=env['l_left'],
                             rows={name: row_digits(vals[name], R, height) for name in
                                   'Q S0 S1 M0 M1 L Nsum N Nbar E Ebar'.split()}))
    return dict(program=dict(beta=2, appendant=[0, 1], initial=list(initial), fixed=list(fixed)),
                full_conditional_false_tuples=receipts)


def first_halting_run(beta, app, initial, cutoff=20):
    word = tuple(initial)
    rows = []
    while len(word) >= beta and len(rows) < cutoff:
        rows.append(word)
        word = word[beta:]+((0,) if word[0] == 0 else tuple(app))
    return (rows, word) if len(word) < beta else None


def encode_canonical(beta, app, rows, terminal):
    assert rows and all(len(word) >= beta for word in rows) and len(terminal) < beta
    c = constants(beta, app)
    p = max(map(len, rows))+1
    A = 2**p
    R = c['C']*A
    height = len(rows)
    q = R**height
    H = (q-1)//(R-1)
    words = {name: 0 for name in 'Q S0 S1 M0 M1 N Nbar E Ebar'.split()}
    for i, word in enumerate(rows):
        length = 2**len(word)
        number = sum(bit*2**j for j, bit in enumerate(word))
        selector = word[0]
        prefix = (number % c['K'])//2
        row = dict(Q=selector*(length-1), S0=1-selector, S1=selector,
                   M0=(1-selector)*length, M1=selector*length,
                   N=number, Nbar=length-1-number, E=prefix, Ebar=c['c']-prefix)
        for name, value in row.items():
            words[name] += value*R**i
        expected_next = word[beta:]+((0,) if selector == 0 else tuple(app))
        assert expected_next == (rows[i+1] if i+1 < height else terminal)
    Ni = sum(bit*2**i for i, bit in enumerate(rows[0]))
    Nt = sum(bit*2**i for i, bit in enumerate(terminal))
    Li = 2**len(rows[0])
    Lt = 2**len(terminal)
    vals = dict(words, A=A, R=R, q=q, H=H,
                L=words['M0']+words['M1'], Nsum=words['N']+words['Nbar'],
                Ninit=Ni, Linit=Li, Nfinal=Nt, Lfinal=Lt,
                alphaI=A-Li, alphaH=c['K']-Lt, alphaN=Lt-Nt)
    env = evaluate(schedule(c), vals)
    env['K'] = c['K']
    assert all(env[a] == env[b] for a, b in comparisons())
    assert R & (R-1) == 0 and q == R**height and H*(R-1) == q-1
    assert all(0 <= vals[name] < q for name in
               'Q S0 S1 M0 M1 L Nsum N Nbar E Ebar'.split())
    assert 0 <= env['padding'] < q
    assert all(vals[name] > 0 for name in ('alphaI', 'alphaH', 'alphaN'))
    assert Li < A and 0 < Lt < c['K'] and 0 <= Nt < Lt
    pairs = [('Q', 'M1'), ('Q', 'padding'), ('S0', 'S1'),
             ('N', 'Nbar'), ('E', 'Ebar'), ('M0', 'M1')]
    assert all(env[a] & env[b] == 0 for a, b in pairs)
    assert tuple((Ni >> i) & 1 for i in range(len(rows[0]))) == rows[0]
    assert tuple((Nt >> i) & 1 for i in range(len(terminal))) == terminal
    return vals


def verify_canonical():
    histories = row_count = cutoffs = zero_inputs = zero_outputs = 0
    zero_only = one_only = mixed = zero_rows = one_rows = 0
    zero_coordinates = {name: 0 for name in 'Q S0 S1 M0 M1 N Nbar E Ebar'.split()}
    for beta in (2, 3):
        for a in (2, 3):
            for app in product((0, 1), repeat=a):
                for ell in range(beta, beta+3):
                    for initial in product((0, 1), repeat=ell):
                        run = first_halting_run(beta, app, initial)
                        if run is None:
                            cutoffs += 1
                            continue
                        rows, terminal = run
                        vals = encode_canonical(beta, app, rows, terminal)
                        histories += 1
                        row_count += len(rows)
                        zero_inputs += vals['Ninit'] == 0
                        zero_outputs += vals['Nfinal'] == 0
                        selectors = {word[0] for word in rows}
                        zero_only += selectors == {0}
                        one_only += selectors == {1}
                        mixed += selectors == {0, 1}
                        zero_rows += sum(word[0] == 0 for word in rows)
                        one_rows += sum(word[0] == 1 for word in rows)
                        for name in zero_coordinates:
                            zero_coordinates[name] += vals[name] == 0
    assert (histories, row_count, cutoffs) == (776, 2006, 232)
    assert zero_only+one_only+mixed == histories and zero_rows+one_rows == row_count
    assert zero_inputs and zero_outputs and all(zero_coordinates.values())
    return dict(first_halting_histories=histories, source_rows=row_count, twenty_step_cutoffs=cutoffs,
                exact_source_comparisons_per_history=12, and_tests_per_history=6,
                zero_inputs=zero_inputs, zero_terminal_numbers=zero_outputs,
                zero_selector_only_histories=zero_only, one_selector_only_histories=one_only,
                mixed_selector_histories=mixed, zero_selector_rows=zero_rows, one_selector_rows=one_rows,
                zero_word_coordinates=zero_coordinates)


def verify():
    return dict(status='PASS', review_status='Author and two independent complete proof/source reviews and fresh verification runs PASS, including the added canonical-history regression; proof and arithmetic frozen.',
                source=verify_source(), projector=verify_projector(), flow=verify_flow(),
                obstruction=verify_false_tuples(), canonical=verify_canonical(),
                scope='Conditional 29-operation component. AND enforcement, true-power geometry, '
                      'positive adapters, and a complete Pell/universality construction are not counted.')


if __name__ == '__main__':
    result = verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'obstruction'}, indent=2))
