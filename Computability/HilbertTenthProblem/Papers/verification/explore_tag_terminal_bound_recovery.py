"""The 31-operation successor: recover the terminal slack algebraically."""
from itertools import product
from pathlib import Path
import json
import sympy as sp
import explore_single_projector_tag_history as old


def schedule(c):
    return old.schedule(c)[:-1]


def comparisons():
    return old.comparisons()[:-1]


def verify_source():
    names = ('A H Q S0 S1 M0 M1 R L N Nbar E Ebar q '
             'Ninit Linit Nfinal Lfinal alphaI alphaH').split()
    s = dict(zip(names, sp.symbols(' '.join(names))))
    c = dict(zip('C K Khalf B U c'.split(), sp.symbols('C K Khalf B U c')))
    env = old.evaluate(schedule(c), s)
    env['K'] = c['K']
    src = [c['C']*s['A']-s['R'], s['S0']+s['S1']-s['H'],
           2*s['Q']+s['S1']-s['M1'], s['M0']+s['M1']-s['L'],
           2*(s['N']+s['Nbar'])+s['H']-s['L'],
           s['E']+s['Ebar']-c['c']*s['H'],
           s['R']*(s['N']-3*s['E']-s['S1']+c['U']*s['M1'])
               -c['K']*(s['N']-s['Ninit']+s['q']*s['Nfinal']),
           s['R']*(s['M0']+c['B']*s['M1'])
               -c['Khalf']*(s['L']-s['Linit']+s['q']*s['Lfinal']),
           s['Linit']+s['alphaI']-s['A'],
           s['Lfinal']+s['alphaH']-c['K']]
    assert len(src) == len(comparisons())
    for (left, right), residual in zip(comparisons(), src):
        assert sp.expand(env[left]-env[right]-residual) == 0
    assert schedule(c) == old.schedule(c)[:-1]
    assert comparisons() == old.comparisons()[:-1]
    # Exact positive-remainder identity, before any power or carry decoding.
    R, K, Af, U, N, Nb, M0, M1, L, H, q, Nt, Lt, Ni, Li, d = sp.symbols(
        'R K Af U N Nb M0 M1 L H q Nt Lt Ni Li d')
    content = R*(N-d+U*M1)-K*(N-Ni+q*Nt)
    length = R*(3*M0+Af*M1)-K*(L-Li+q*Lt)
    containment = 2*(N+Nb)+H-L
    length_sum = M0+M1-L
    positive = (2*R*M0+R*(Af-2*U-1)*M1+(R-K)*H
                +2*(R-K)*Nb+K*(Li-2*Ni)+2*R*d)
    identity = K*q*(Lt-2*Nt)-positive
    assert sp.expand(identity-(2*content-length-(R-K)*containment+R*length_sum)) == 0
    dag = schedule(old.constants(2, (1, 0, 0)))
    assert len(dag) == 31 and sum(op == '*' for _, op, _, _ in dag) == 14
    return dict(operations=31, multiplications=14, additions=17,
                source_comparisons=10, Boolean_fields=10,
                deleted_coordinate='alphaN', deleted_comparison='Nfinal+alphaN=Lfinal',
                inherited_arithmetic_without_boundary_sums=29,
                positive_remainder_identity=sp.sstr(positive), dag=dag)


def check_bound(v, c):
    d = 3*v['E']+v['S1']
    rhs = (2*v['R']*v['M0']+v['R']*(c['Af']-2*c['U']-1)*v['M1']
           +(v['R']-c['K'])*v['H']+2*(v['R']-c['K'])*v['Nbar']
           +c['K']*(v['Linit']-2*v['Ninit'])+2*v['R']*d)
    assert rhs == c['K']*v['q']*(v['Lfinal']-2*v['Nfinal'])
    assert rhs > 0 and 0 <= 2*v['Nfinal'] < v['Lfinal']
    assert v['Lfinal']-v['Nfinal'] > 0


def witness(beta, appendant, initial, source_words, selectors, prefixes, final):
    c = old.constants(beta, appendant)
    A = 3**(1+max([len(initial)] + [len(w) for w in source_words]))
    R, t = c['C']*A, len(source_words)
    q = R**t
    H = (q-1)//(R-1)
    env = dict.fromkeys([f for f in old.FIELDS if f != 'G'], 0)
    for j, (word, selected, prefix) in enumerate(zip(source_words, selectors, prefixes)):
        length, n, weight = 3**len(word), old.value(word), R**j
        interval = (length-1)//2
        env['Q'] += selected*interval*weight
        env['S'+str(selected)] += weight
        env['M'+str(selected)] += length*weight
        env['N'] += n*weight
        env['Nbar'] += (interval-n)*weight
        e = (prefix-selected)//3
        env['E'] += e*weight
        env['Ebar'] += (c['c']-e)*weight
    env.update(A=A, R=R, q=q, H=H, L=env['M0']+env['M1'],
               Ninit=old.value(initial), Linit=3**len(initial),
               Nfinal=old.value(final), Lfinal=3**len(final))
    env.update(alphaI=A-env['Linit'], alphaH=c['K']-env['Lfinal'])
    assert min(env['alphaI'], env['alphaH']) > 0
    out = old.evaluate(schedule(c), env)
    out['K'] = c['K']
    assert all(out[a] == out[b] for a, b in comparisons())
    assert all(0 <= out[f] < q and old.boolean(out[f]) for f in old.FIELDS)
    check_bound(out, c)
    # Restore the deleted positive coordinate and the actual predecessor DAG.
    restored = dict(env, alphaN=env['Lfinal']-env['Nfinal'])
    before = old.evaluate(old.schedule(c), restored)
    before['K'] = c['K']
    assert all(before[a] == before[b] for a, b in old.comparisons())
    return t


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
                            prefixes.append(old.value(current[:beta]))
                            current = current[beta:] + (appendant if current[0] else (0,))
                        if len(current) >= beta:
                            unresolved += 1
                            continue
                        rows += witness(beta, appendant, initial, words, selectors, prefixes, current)
                        cases += 1
    witness(2, (1, 0, 0), (0, 0), [(0, 0), (0,), ()],
            [0, 0, 1], [0, 0, 1], (0,))
    return dict(fully_checked_halting_histories=cases, checked_source_rows=rows,
                longer_runs_unclassified=unresolved, regression_step_limit=20,
                new_comparisons_per_witness=10, restored_predecessor_comparisons=11,
                post_halt_witness_rows=3, post_halt_actual_halting_time=1)


def verify_unbounded_terminal_candidates():
    reports = []
    for m, t, a in [(6, 2, 1), (6, 2, 2), (6, 3, 2),
                    (7, 2, 1), (7, 2, 2), (7, 2, 3), (8, 2, 3)]:
        beta, appendant = 2, (1,)+(0,)*(a-1)
        c = old.constants(beta, appendant)
        R, K = 3**m, c['K']
        A, q = R//c['C'], R**t
        H = (q-1)//(R-1)
        counts = dict(projector_candidates=0, accepted_length_words=0,
                      full_content_candidates=0, integral_terminal_solutions=0,
                      negative_terminals=0, accepted_full_certificates=0,
                      failed_recovered_bound=0)
        for Q in old.subsets((q-1)//2-A*H):
            for S1 in old.subsets(H):
                counts['projector_candidates'] += 1
                M1 = 2*Q+S1
                if M1 >= q or not old.boolean(M1):
                    continue
                for exponent in range(beta, len(old.trits(A))-1):
                    Linit = 3**exponent
                    for Lfinal in range(1, K):
                        numerator = K*q*Lfinal-K*Linit-(3*R*c['B']-K)*M1
                        M0, rem = divmod(numerator, 3*R-K)
                        if rem or not 0 <= M0 < q or not old.boolean(M0):
                            continue
                        counts['accepted_length_words'] += 1
                        L = M0+M1
                        if L < H or (L-H) % 2:
                            continue
                        for N in old.splits((L-H)//2):
                            Nbar = (L-H)//2-N
                            if max(N, Nbar) >= q:
                                continue
                            Ninit = N % (R//K)
                            if Ninit >= Linit or not old.boolean(Ninit):
                                continue
                            for E in old.subsets(c['c']*H):
                                counts['full_content_candidates'] += 1
                                d = 3*E+S1
                                Nfinal, rem_n = divmod(R*(N-d+c['U']*M1)-K*(N-Ninit), K*q)
                                if rem_n:
                                    continue
                                counts['integral_terminal_solutions'] += 1
                                counts['negative_terminals'] += Nfinal < 0
                                if Nfinal < 0:
                                    continue
                                # Crucially no terminal upper-bound filter.
                                counts['accepted_full_certificates'] += 1
                                counts['failed_recovered_bound'] += 2*Nfinal >= Lfinal
                                env = dict(A=A, H=H, Q=Q, S0=H-S1, S1=S1,
                                           M0=M0, M1=M1, L=L, N=N, Nbar=Nbar,
                                           E=E, Ebar=c['c']*H-E, R=R, q=q,
                                           Ninit=Ninit, Linit=Linit, Nfinal=Nfinal,
                                           Lfinal=Lfinal, alphaI=A-Linit, alphaH=K-Lfinal)
                                out = old.evaluate(schedule(c), env)
                                out['K'] = K
                                assert all(out[x] == out[y] for x, y in comparisons())
                                assert all(0 <= out[f] < q and old.boolean(out[f]) for f in old.FIELDS)
                                check_bound(out, c)
                                first_short, _ = old.audit_flow(out, beta, a)
                                word = tuple((Ninit//3**i) % 3 for i in range(exponent))
                                for _ in range(first_short):
                                    assert len(word) >= beta
                                    word = word[beta:] + (appendant if word[0] else (0,))
                                assert len(word) < beta
        assert counts['failed_recovered_bound'] == 0
        reports.append(dict(radix_exponent=m, rows=t, beta=beta,
                            appendant=list(appendant), **counts))
    assert sum(r['accepted_full_certificates'] for r in reports) == 30
    return reports


def verify():
    return dict(status='PASS_CONDITIONAL_TAG_TERMINAL_BOUND_RECOVERY',
                source=verify_source(), histories=verify_histories(),
                unbounded_terminal_candidates=verify_unbounded_terminal_candidates(),
                proof='../1980/EXPLORATION_TAG_TERMINAL_BOUND_RECOVERY.md',
                scope='Exact positive-slack extension to the conditional32 interface. No terminal upper-bound filter is used in the new candidate gate. Boolean masks, power geometry, positive word adapters and raw numerical input encoding remain unpaid; no universal arithmetic bound.')


if __name__ == '__main__':
    receipt = verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(receipt, indent=2)+'\n', encoding='utf-8')
    print(receipt['status'])
    print(receipt['source']['operations'], receipt['histories'])
    print(receipt['unbounded_terminal_candidates'])
