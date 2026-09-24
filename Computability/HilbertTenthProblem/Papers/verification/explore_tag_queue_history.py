"""A conditional 33-operation encoded-word tag-halting interface."""
from itertools import product
from pathlib import Path
import json
import sympy as sp
import explore_joint_row_marker_selection as joint


def value(word):
    return sum(d*3**i for i, d in enumerate(word))


def constants(beta, appendant):
    K = 3**beta
    B = 3**(len(appendant)-1)
    U = value(appendant)
    C = 3
    while C <= K*K+U+B+1:
        C *= 3
    return dict(K=K, Khalf=K//3, B=B, U=U, c=(K//3-1)//2, C=C)


def schedule(c):
    return joint.schedule(c['C']) + [
        ('content_sum', '+', 'N', 'Nbar'),
        ('prefix_scale', '*', c['c'], 'H'),
        ('prefix_sum', '+', 'E', 'Ebar'),
        ('prefix_tail', '*', 3, 'E'), ('d', '+', 'prefix_tail', 'S1'),
        ('n_append', '*', c['U'], 'M1'), ('n_trim', '-', 'N', 'd'),
        ('n_output', '+', 'n_trim', 'n_append'),
        ('n_left', '*', 'R', 'n_output'),
        ('n_end', '*', 'q', 'Nfinal'), ('n_initial', '-', 'N', 'Ninit'),
        ('n_shift', '+', 'n_initial', 'n_end'),
        ('n_right', '*', c['K'], 'n_shift'),
        ('l_append', '*', c['B'], 'M1'),
        ('l_output', '+', 'M0', 'l_append'),
        ('l_left', '*', 'R', 'l_output'),
        ('l_end', '*', 'q', 'Lfinal'), ('l_initial', '-', 'L', 'Linit'),
        ('l_shift', '+', 'l_initial', 'l_end'),
        ('l_right', '*', c['Khalf'], 'l_shift'),
        ('initial_bound', '+', 'Linit', 'alphaI'),
        ('halt_bound', '+', 'Lfinal', 'alphaH'),
        ('content_bound', '+', 'Nfinal', 'alphaN')]


def evaluate(dag, values):
    env = dict(values)
    for name, op, left, right in dag:
        x = env[left] if isinstance(left, str) else left
        y = env[right] if isinstance(right, str) else right
        assert name not in env
        env[name] = x*y if op == '*' else x+y if op == '+' else x-y
    return env


def comparisons():
    return [('radix', 'R'), ('headsum', 'H'), ('marker0', 'M0'),
            ('marker1', 'M1'), ('lengthsum', 'L'),
            ('content_sum', 'Qsum'), ('prefix_sum', 'prefix_scale'),
            ('n_left', 'n_right'), ('l_left', 'l_right'),
            ('initial_bound', 'A'), ('halt_bound', 'K'),
            ('content_bound', 'Lfinal')]


def verify_source():
    names = ('A H Q0 Q1 S0 S1 M0 M1 R L N Nbar E Ebar q '
             'Ninit Linit Nfinal Lfinal alphaI alphaH alphaN').split()
    s = dict(zip(names, sp.symbols(' '.join(names))))
    c = dict(zip('C K Khalf B U c'.split(), sp.symbols('C K Khalf B U c')))
    env = evaluate(schedule(c), s)
    env['K'] = c['K']
    src = [c['C']*s['A']-s['R'], s['S0']+s['S1']-s['H'],
           2*s['Q0']+s['S0']-s['M0'], 2*s['Q1']+s['S1']-s['M1'],
           s['M0']+s['M1']-s['L'],
           s['N']+s['Nbar']-s['Q0']-s['Q1'],
           s['E']+s['Ebar']-c['c']*s['H'],
           s['R']*(s['N']-3*s['E']-s['S1']+c['U']*s['M1'])
               -c['K']*(s['N']-s['Ninit']+s['q']*s['Nfinal']),
           s['R']*(s['M0']+c['B']*s['M1'])
               -c['Khalf']*(s['L']-s['Linit']+s['q']*s['Lfinal']),
           s['Linit']+s['alphaI']-s['A'],
           s['Lfinal']+s['alphaH']-c['K'],
           s['Nfinal']+s['alphaN']-s['Lfinal']]
    for (left, right), residual in zip(comparisons(), src):
        assert sp.expand(env[left]-env[right]-residual) == 0
    dag = schedule(constants(2, (1, 0, 0)))
    assert len(dag) == 33 and sum(op == '*' for _, op, _, _ in dag) == 14
    return dict(operations=33, multiplications=14, additions=19,
                source_comparisons=len(src), Boolean_fields=11, dag=dag,
                arithmetic_without_three_boundary_sums=30)


def witness(beta, appendant, initial, source_words, selectors, prefixes, final):
    c = constants(beta, appendant)
    A = 3**(1+max([len(initial)] + [len(w) for w in source_words]))
    R = c['C']*A
    t = len(source_words)
    assert t >= 1 and len(initial) >= beta
    q = R**t
    H = (q-1)//(R-1)
    names = 'Q0 Q1 S0 S1 M0 M1 N Nbar E Ebar'.split()
    env = dict.fromkeys(names, 0)
    for j, (word, selected, prefix) in enumerate(zip(source_words, selectors, prefixes)):
        length, n = 3**len(word), value(word)
        interval = (length-1)//2
        w = R**j
        env['Q'+str(selected)] += interval*w
        env['S'+str(selected)] += w
        env['M'+str(selected)] += length*w
        env['N'] += n*w
        env['Nbar'] += (interval-n)*w
        assert 0 <= prefix < c['K'] and prefix % 3 == selected
        e = (prefix-selected)//3
        env['E'] += e*w
        env['Ebar'] += (c['c']-e)*w
    env.update(A=A, R=R, q=q, H=H, L=env['M0']+env['M1'],
               Ninit=value(initial), Linit=3**len(initial),
               Nfinal=value(final), Lfinal=3**len(final))
    env.update(alphaI=A-env['Linit'], alphaH=c['K']-env['Lfinal'],
               alphaN=env['Lfinal']-env['Nfinal'])
    assert min(env['alphaI'], env['alphaH'], env['alphaN']) > 0
    result = evaluate(schedule(c), env)
    result['K'] = c['K']
    assert all(result[a] == result[b] for a, b in comparisons())
    assert all(0 <= result[name] < q and joint.boolean(result[name])
               for name in names + ['Qguard'])
    assert result['Qguard'] % 3 == 1
    assert c['C'] > c['K']**2+c['U']+c['B']+1
    # Independently compare the original nonnegative coefficient equations.
    rows_n = [value(word) for word in source_words] + [value(final)]
    rows_l = [3**len(word) for word in source_words] + [3**len(final)]
    for j, selected in enumerate(selectors):
        mark = selected*rows_l[j]
        assert rows_n[j]+c['U']*mark == prefixes[j]+c['K']*rows_n[j+1]
        assert rows_l[j]+(c['B']-1)*mark == c['Khalf']*rows_l[j+1]
        assert rows_n[j]+c['U']*mark < R
        assert prefixes[j]+c['K']*rows_n[j+1] < R
        assert rows_l[j]+(c['B']-1)*mark < R
        assert c['Khalf']*rows_l[j+1] < R
    return dict(rows=t, all_comparisons=12,
                all_Boolean_fields=11, unit_guard_digit=1)


def verify_histories():
    cases = rows = unresolved = 0
    for beta in (1, 2, 3):
        for a in (1, 2, 3):
            for appendant in product((0, 1), repeat=a):
                for length in range(beta, beta+3):
                    for initial in product((0, 1), repeat=length):
                        current = tuple(initial)
                        words, selectors, prefixes = [], [], []
                        for _ in range(20):
                            if len(current) < beta:
                                break
                            words.append(current)
                            selectors.append(current[0])
                            prefixes.append(value(current[:beta]))
                            current = current[beta:] + (appendant if current[0] else (0,))
                        if len(current) >= beta:
                            unresolved += 1
                            continue
                        result = witness(beta, appendant, initial, words, selectors, prefixes, current)
                        cases += 1
                        rows += result['rows']
    # A valid arithmetic suffix after the real one-step halt.
    noncausal = witness(2, (1, 0, 0), (0, 0),
                        [(0, 0), (0,), ()], [0, 0, 1], [0, 0, 1], (0,))
    assert noncausal['rows'] == 3
    return dict(fully_checked_halting_histories=cases, checked_source_rows=rows,
                longer_runs_unclassified=unresolved, regression_step_limit=20,
                post_halt_witness_rows=3, post_halt_actual_halting_time=1,
                scope='Only directly observed halts are classified; step-cutoff runs are left unresolved. Every observed halt receives all twelve source and eleven mask checks.')


def verify():
    return dict(status='PASS_CONDITIONAL_TAG_QUEUE_HISTORY', source=verify_source(),
                histories=verify_histories(),
                proof='../1980/EXPLORATION_TAG_QUEUE_HISTORY.md',
                scope='Exact conditional encoded-word halting equivalence over nonnegative words. Boolean-mask realization, power geometry, positive adapters and raw numerical input conversion are excluded; no universal operation bound.')


if __name__ == '__main__':
    receipt = verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(receipt, indent=2)+'\n', encoding='utf-8')
    print(receipt['status'])
    print(receipt['histories'])
