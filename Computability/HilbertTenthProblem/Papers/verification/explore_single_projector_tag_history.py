"""A conditional 32-operation / ten-mask encoded-word tag-halting interface."""
from itertools import product
from pathlib import Path
import json
import sympy as sp
import explore_tag_queue_history as safe


value = safe.value
evaluate = safe.evaluate
boolean = safe.joint.boolean
FIELDS = 'Q S0 S1 M0 M1 G N Nbar E Ebar'.split()


def constants(beta, appendant):
    c = safe.constants(beta, appendant)
    c['Af'] = 3**len(appendant)
    c['C'] = 3
    while c['C'] <= max(c['K'], c['Af'], 2*c['U']+3):
        c['C'] *= 3
    return c


def schedule(c):
    return [
        ('radix', '*', c['C'], 'A'), ('padding', '*', 'A', 'H'),
        ('G', '+', 'Q', 'padding'), ('headsum', '+', 'S0', 'S1'),
        ('twice_Q', '*', 2, 'Q'), ('marker1', '+', 'twice_Q', 'S1'),
        ('lengthsum', '+', 'M0', 'M1'),
        ('content_sum', '+', 'N', 'Nbar'),
        ('twice_content', '*', 2, 'content_sum'),
        ('content_length', '+', 'twice_content', 'H'),
    ] + safe.schedule(c)[11:]


def comparisons():
    return [('radix', 'R'), ('headsum', 'H'), ('marker1', 'M1'),
            ('lengthsum', 'L'), ('content_length', 'L'),
            ('prefix_sum', 'prefix_scale'), ('n_left', 'n_right'),
            ('l_left', 'l_right'), ('initial_bound', 'A'),
            ('halt_bound', 'K'), ('content_bound', 'Lfinal')]


def verify_source():
    names = ('A H Q S0 S1 M0 M1 R L N Nbar E Ebar q '
             'Ninit Linit Nfinal Lfinal alphaI alphaH alphaN').split()
    s = dict(zip(names, sp.symbols(' '.join(names))))
    c = dict(zip('C K Khalf B U c'.split(), sp.symbols('C K Khalf B U c')))
    env = evaluate(schedule(c), s)
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
           s['Lfinal']+s['alphaH']-c['K'],
           s['Nfinal']+s['alphaN']-s['Lfinal']]
    assert len(src) == len(comparisons())
    for (left, right), residual in zip(comparisons(), src):
        assert sp.expand(env[left]-env[right]-residual) == 0
    dag = schedule(constants(2, (1, 0, 0)))
    assert len(dag) == 32 and sum(op == '*' for _, op, _, _ in dag) == 14
    # The marker-flow identity is an exact consequence of the length source.
    assert sp.expand(s['R']*(s['M0']+c['B']*s['M1'])
                     -c['Khalf']*(s['M0']+s['M1']-s['Linit']+s['q']*s['Lfinal'])
                     -src[7]+c['Khalf']*src[3]) == 0
    return dict(operations=32, multiplications=14, additions=18,
                arithmetic_without_three_boundary_sums=29,
                source_comparisons=11, Boolean_fields=10, dag=dag)


def witness(beta, appendant, initial, source_words, selectors, prefixes, final):
    c = constants(beta, appendant)
    A = 3**(1+max([len(initial)] + [len(w) for w in source_words]))
    R = c['C']*A
    t = len(source_words)
    q = R**t
    H = (q-1)//(R-1)
    env = dict.fromkeys([f for f in FIELDS if f != 'G'], 0)
    for j, (word, selected, prefix) in enumerate(zip(source_words, selectors, prefixes)):
        length, n, w = 3**len(word), value(word), R**j
        interval = (length-1)//2
        env['Q'] += selected*interval*w
        env['S'+str(selected)] += w
        env['M'+str(selected)] += length*w
        env['N'] += n*w
        env['Nbar'] += (interval-n)*w
        e = (prefix-selected)//3
        assert prefix == 3*e+selected and 0 <= e <= c['c']
        env['E'] += e*w
        env['Ebar'] += (c['c']-e)*w
    env.update(A=A, R=R, q=q, H=H, L=env['M0']+env['M1'],
               Ninit=value(initial), Linit=3**len(initial),
               Nfinal=value(final), Lfinal=3**len(final))
    env.update(alphaI=A-env['Linit'], alphaH=c['K']-env['Lfinal'],
               alphaN=env['Lfinal']-env['Nfinal'])
    assert min(env['alphaI'], env['alphaH'], env['alphaN']) > 0
    out = evaluate(schedule(c), env)
    out['K'] = c['K']
    assert all(out[a] == out[b] for a, b in comparisons())
    assert all(0 <= out[f] < q and boolean(out[f]) for f in FIELDS)
    assert c['C'] > max(c['K'], c['Af'], 2*c['U']+3)
    audit_flow(out, beta, len(appendant))
    return dict(rows=t, all_comparisons=11, all_Boolean_fields=10)


def trits(n):
    out = []
    while n:
        n, d = divmod(n, 3)
        out.append(d)
    return out


def audit_flow(v, beta, a):
    """Read the exact increasing unit path; do not assume rowwise causality."""
    R, q, K = v['R'], v['q'], 3**beta
    m = len(trits(R))-1
    shifts = (m-beta+1, m-beta+a)
    edges = {}
    for mode in (0, 1):
        for e, d in enumerate(trits(v['M'+str(mode)])):
            if d:
                edges.setdefault(e, []).append(mode)
    assert all(len(modes) == 1 for modes in edges.values())
    assert sum(d != 0 for d in trits(v['Lfinal'])) == 1
    assert boolean(v['Lfinal'])
    pos = len(trits(v['Linit']))-1
    target = len(trits(q*v['Lfinal']))-1
    visited = []
    while pos in edges:
        mode = edges[pos][0]
        visited.append((pos, mode))
        pos += shifts[mode]
    assert pos == target and len(visited) == len(edges)
    # Only the prefix before the first undersize marker is a real time row.
    first_short = None
    for i, (position, mode) in enumerate(visited):
        row, length = divmod(position, m)
        if length < beta:
            first_short = i
            break
        assert row == i and K*3**length < R
        assert (v['L']//R**row) % R == 3**length
        assert (v['S1']//R**row) % R == mode
    if first_short is None:
        first_short = len(visited)
        assert target//m == first_short and target % m < beta
    assert first_short >= 1
    return first_short, len(visited)


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
    witness(2, (1, 0, 0), (0, 0), [(0, 0), (0,), ()],
            [0, 0, 1], [0, 0, 1], (0,))
    return dict(fully_checked_halting_histories=cases, checked_source_rows=rows,
                longer_runs_unclassified=unresolved, regression_step_limit=20,
                post_halt_witness_rows=3, post_halt_actual_halting_time=1)


def subsets(word):
    out = [0]
    for i, d in enumerate(trits(word)):
        assert d <= 1
        if d:
            out += [x+3**i for x in out]
    return out


def splits(word):
    """All ordered Boolean sums, including forced 1+1 at trit 2."""
    base = sum(3**i for i, d in enumerate(trits(word)) if d == 2)
    optional = sum(3**i for i, d in enumerate(trits(word)) if d == 1)
    return [base+x for x in subsets(optional)]


def verify_complete_length_candidates():
    reports = []
    for m, t, a in [(6, 2, 1), (6, 2, 2), (6, 3, 2),
                    (7, 2, 1), (7, 2, 2), (7, 2, 3), (8, 2, 3)]:
        beta, appendant = 2, (1,)+(0,)*(a-1)
        c = constants(beta, appendant)
        R, K = 3**m, c['K']
        A, q = R//c['C'], R**t
        H = (q-1)//(R-1)
        # Enumerate every Q compatible with its exact Boolean guard. Every
        # other Q is rejected independently by the two-summand guard.
        maxword = (q-1)//2
        qs = subsets(maxword-A*H)
        counts = dict(projector_candidates=0, valid_projectors=0,
                      endpoint_trials=0, accepted_length_words=0,
                      nonmarker_terminal_trials=0, full_content_candidates=0,
                      accepted_full_certificates=0, post_halt_certificates=0)
        for Q in qs:
            for S1 in subsets(H):
                counts['projector_candidates'] += 1
                M1 = 2*Q+S1
                if M1 >= q or not boolean(M1):
                    continue
                counts['valid_projectors'] += 1
                for exponent in range(beta, len(trits(A))-1):
                    Linit = 3**exponent
                    for Lfinal in range(1, K):
                        counts['endpoint_trials'] += 1
                        counts['nonmarker_terminal_trials'] += not (
                            boolean(Lfinal) and sum(trits(Lfinal)) == 1)
                        numerator = K*q*Lfinal-K*Linit-(3*R*c['B']-K)*M1
                        M0, rem = divmod(numerator, 3*R-K)
                        if rem or not 0 <= M0 < q or not boolean(M0):
                            continue
                        counts['accepted_length_words'] += 1
                        L = M0+M1
                        v = dict(R=R, q=q, M0=M0, M1=M1, S1=S1,
                                 L=L, Linit=Linit, Lfinal=Lfinal)
                        first_short, events = audit_flow(v, beta, a)
                        if L < H or (L-H) % 2:
                            continue
                        content_sum = (L-H)//2
                        for N in splits(content_sum):
                            Nbar = content_sum-N
                            if max(N, Nbar) >= q:
                                continue
                            Ninit = N % (R//K)
                            if Ninit >= Linit or not boolean(Ninit):
                                continue
                            for E in subsets(c['c']*H):
                                counts['full_content_candidates'] += 1
                                d = 3*E+S1
                                numerator_n = R*(N-d+c['U']*M1)-K*(N-Ninit)
                                Nfinal, rem_n = divmod(numerator_n, K*q)
                                if rem_n or not 0 <= Nfinal < Lfinal:
                                    continue
                                counts['accepted_full_certificates'] += 1
                                counts['post_halt_certificates'] += first_short < t
                                env = dict(A=A, H=H, Q=Q, S0=H-S1, S1=S1,
                                           M0=M0, M1=M1, L=L, N=N, Nbar=Nbar,
                                           E=E, Ebar=c['c']*H-E, R=R, q=q,
                                           Ninit=Ninit, Linit=Linit, Nfinal=Nfinal,
                                           Lfinal=Lfinal, alphaI=A-Linit,
                                           alphaH=K-Lfinal, alphaN=Lfinal-Nfinal)
                                out = evaluate(schedule(c), env)
                                out['K'] = K
                                assert all(out[x] == out[y] for x, y in comparisons())
                                assert all(0 <= out[f] < q and boolean(out[f]) for f in FIELDS)
                                word = tuple((Ninit//3**i) % 3 for i in range(exponent))
                                for _ in range(first_short):
                                    assert len(word) >= beta
                                    word = word[beta:] + (appendant if word[0] else (0,))
                                assert len(word) < beta
        reports.append(dict(radix_exponent=m, rows=t, beta=beta,
                            appendant=list(appendant), **counts))
    assert sum(r['accepted_full_certificates'] for r in reports) > 0
    assert sum(r['post_halt_certificates'] for r in reports) > 0
    return reports


def verify():
    return dict(status='PASS_CONDITIONAL_SINGLE_PROJECTOR_TAG_HISTORY',
                full_review_gates=['author', 'root', 'independent_affine'],
                source=verify_source(), histories=verify_histories(),
                complete_candidates=verify_complete_length_candidates(),
                proof='../1980/EXPLORATION_SINGLE_PROJECTOR_TAG_HISTORY.md',
                scope='Conditional encoded-word halting equivalence. Nonnegative Boolean words, power geometry, and valid encoded input are interface hypotheses. Their Diophantine realization, positive adapters, and raw numerical input conversion are not counted. No universal arithmetic bound.')


if __name__ == '__main__':
    receipt = verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(receipt, indent=2)+'\n', encoding='utf-8')
    print(receipt['status'])
    print(receipt['source']['operations'], receipt['histories'])
    print(receipt['complete_candidates'])
