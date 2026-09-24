"""Shared transport scale: a generic accounting tie and a zero-leading105."""
from itertools import product
from pathlib import Path
import json
import sympy as sp

import explore_shared_marker_low_packing as previous

old = previous.old
tag = previous.tag
FIELDS = previous.FIELDS
PARAMETERS = previous.PARAMETERS
POSITIVE = ['F_T' if x == 'F_N' else x for x in previous.POSITIVE]


def extended(c):
    d = dict(c)
    if isinstance(c['C'], int):
        assert c['C'] % c['Khalf'] == 0 and c['U'] % 3 == 0
        d.update(Cbar=c['C']//c['Khalf'], Uthird=c['U']//3)
    return d


def prefix(c):
    c = extended(c)
    rows = []
    for name, op, a, b in previous.prefix(c)[0]:
        if name == 'N':
            rows += [('Tcontent', '-', 'F_T', 1),
                     ('three_T', '*', 3, 'Tcontent'), ('N', '+', 'three_T', 'S1')]
        elif name == 'radix':
            rows += [('transport_scale', '*', c['Cbar'], 'A'),
                     ('radix', '*', c['Khalf'], 'transport_scale')]
        elif name in ('prefix_tail', 'd', 'n_right', 'l_right'):
            continue
        elif name == 'n_trim':
            rows.append((name, '-', 'Tcontent', 'E'))
        elif name == 'n_append':
            rows.append((name, '*', c['Uthird'], 'M1'))
        elif name in ('n_left', 'l_left'):
            rows.append((name, '*', 'transport_scale', b))
        else:
            rows.append((name, op, a, b))
    return rows, previous.prefix(c)[1]


def schedule(c):
    return prefix(c)[0] + [(old.rename(n), op, old.rename(a), old.rename(b))
                           for n, op, a, b in old.kernel.SCHEDULE]


def outer_comparisons():
    return [(a, 'n_shift' if b == 'n_right' else 'l_shift' if b == 'l_right' else b)
            for a, b in previous.outer_comparisons()]


def comparisons():
    return outer_comparisons()+[(old.rename(a), old.rename(b))
                                for a, b in old.kernel.EQUALITIES]


def sources(c, s):
    T, S1 = s['F_T']-1, s['F_S1']-1
    N, E = 3*T+S1, s['F_E']-1
    M1 = 2*(s['F_Q']-1)+S1
    former = dict(s, F_N=N+1)
    src = previous.sources(c, former)
    src[2] = c['Cbar']*s['A']*(T-E+c['Uthird']*M1) - (
        N-s['Ninit']+s['q']*(s['F_Nfinal']-1))
    src[3] = c['Cbar']*s['A']*(s['L']+(c['B']-1)*M1) - (
        s['L']-s['Linit']+s['q']*s['Lfinal'])
    return src


def generic_scaled_tie(c):
    """No N reparameterization: the extra factor3 gives exactly106 again."""
    rows = []
    for name, op, a, b in previous.prefix(c)[0]:
        if name == 'radix':
            rows += [('transport_scale', '*', c['C']//c['Khalf'], 'A'),
                     ('radix', '*', c['Khalf'], 'transport_scale')]
        elif name in ('n_left', 'l_left'):
            rows.append((name, '*', 'transport_scale', b))
        elif name == 'n_right':
            rows.append((name, '*', 3, b))
        elif name == 'l_right':
            continue
        else:
            rows.append((name, op, a, b))
    return rows + [(old.rename(n), op, old.rename(a), old.rename(b))
                   for n, op, a, b in old.kernel.SCHEDULE]


def verify_source():
    s = dict(zip(POSITIVE+PARAMETERS, sp.symbols(' '.join(POSITIVE+PARAMETERS))))
    Cbar, Kh, Ut, B, cc = sp.symbols('Cbar Khalf Uthird B c')
    c = dict(Cbar=Cbar, Khalf=Kh, Uthird=Ut, B=B, c=cc,
             C=Kh*Cbar, K=3*Kh, U=3*Ut)
    env = old.run(schedule(c), s)
    env['K'] = c['K']
    src = sources(c, s)
    sub = {old.kernel.SYM[k]: s['q']**10 if k == 'D0' else s[old.rename(k)]
           for k in old.kernel.SYM}
    core = [sp.expand(p.subs(sub, simultaneous=True))
            for p in old.kernel.source_residuals()]
    src += core
    records = []
    assert len(src) == len(comparisons()) == 21
    for i, ((a, b), p) in enumerate(zip(comparisons(), src)):
        correction = core[7]*(s['pell_u']**2-s['pell_y_aux']**2) if i == 18 else 0
        assert sp.expand(env[a]-env[b]-p-correction) == 0, i
        records.append(dict(index=i, equality=[a, b], source=sp.sstr(p),
                            correction=sp.sstr(correction)))
    former = dict(s, F_N=3*s['F_T']+s['F_S1']-3)
    before = old.run(previous.prefix(c)[0], former)
    oldsrc = previous.sources(c, former)
    assert sp.expand(oldsrc[2]-3*Kh*src[2]+3*src[0]*env['n_output']) == 0
    assert sp.expand(oldsrc[3]-Kh*src[3]+src[0]*env['l_output']) == 0
    for i in set(range(10))-{2, 3}:
        assert sp.expand(oldsrc[i]-src[i]) == 0, i
    for name in ('N', 'radix', prefix(c)[1], 'index_rhs', 'packed_bound'):
        assert sp.expand(env[name]-before[name]) == 0, name
    for removed in ('F_N', 'prefix_tail', 'd', 'n_right', 'l_right'):
        assert all(removed not in (n, a, b) for n, _, a, b in prefix(c)[0])
    dag = schedule(tag.constants(2, (0, 1)))
    assert old.counts(dag) == dict(operations=105, multiplications=53, additions=52)
    tie = old.counts(generic_scaled_tie(tag.constants(2, (1, 0))))
    assert tie == dict(operations=106, multiplications=54, additions=52)
    assert len(POSITIVE) == len(set(POSITIVE)) == 34
    return dict(**old.counts(dag), positive_unknowns=34, equations=21,
                positive_coordinates=POSITIVE, parameters=PARAMETERS, fields=FIELDS,
                dag=dag, sources=records, generic_rescaling_tie=tie,
                original_coordinate='F_N=3F_T+F_S1-3',
                content_residual_identity='old_content=3Kh*new_content-3*radix_source*new_output',
                length_residual_identity='old_length=Kh*new_length-radix_source*length_output',
                scope='Exact105 only for length>=2 binary appendants beginning with0. New solutions embed106; canonical106 histories extend. No bijection of arbitrary post-halt tuples is asserted.')


def finite_identities():
    cases = negative_outputs = 0
    for Kh in (1, 3, 9):
        for Cbar in (3, 9):
            for A, R in ((5, 14), (9, Kh*Cbar*9)):
                for T, S1, E, M1 in product((0, 1, 4), (0, 2), (0, 3), (0, 5)):
                    for Ut in (0, 1, 4):
                        q, Ninit, Nt, L, Linit, Lt, B = 17, 2, 1, 7, 9, 3, 9
                        D = Cbar*A; N = 3*T+S1
                        out = T-E+Ut*M1
                        delta = N-Ninit+q*Nt
                        oldC = R*(N-3*E-S1+3*Ut*M1)-3*Kh*delta
                        newC = D*out-delta
                        outL = L+(B-1)*M1
                        oldL = R*outL-Kh*(L-Linit+q*Lt)
                        newL = D*outL-(L-Linit+q*Lt)
                        radix = Kh*D-R
                        assert oldC == 3*Kh*newC-3*radix*out
                        assert oldL == Kh*newL-radix*outL
                        cases += 1; negative_outputs += out < 0
    return dict(off_shell_cases=cases, negative_small_content_outputs=negative_outputs,
                scope='Includes failed radix geometry, nonpower q, zero raw coordinates and signed outputs; these are polynomial identities, not whole source solutions.')


def witness(beta, app, initial, words, ss, ds, final):
    assert len(app) >= 2 and app[0] == 0
    c = tag.constants(beta, app)
    A = 3**(1+max([len(initial)]+[len(w) for w in words]))
    R = c['C']*A; t = len(words); q = R**t; H = (q-1)//(R-1)
    raw = dict.fromkeys(old.RAW, 0)
    for j, (w, sel, d) in enumerate(zip(words, ss, ds)):
        wt = R**j; mark = 3**len(w); n = tag.value(w); ns = (mark-1)//2
        assert n >= sel and (n-sel) % 3 == 0
        raw['Q'] += sel*ns*wt; raw['S'+str(sel)] += wt
        raw['M'+str(sel)] += mark*wt
        raw['N'] += n*wt; raw['Nbar'] += (ns-n)*wt
        E = (d-sel)//3; raw['E'] += E*wt; raw['Ebar'] += (c['c']-E)*wt
    assert raw['N'] >= raw['S1'] and (raw['N']-raw['S1']) % 3 == 0
    T = (raw['N']-raw['S1'])//3
    env = {'F_'+x: raw[x]+1 for x in previous.RAW if x != 'N'}
    env.update(F_T=T+1, Nsum=raw['N']+raw['Nbar'], F_Nfinal=tag.value(final)+1,
               A=A, R=R, q=q, H=H, L=raw['M0']+raw['M1'], Lfinal=3**len(final),
               Ninit=tag.value(initial), Linit=3**len(initial),
               alphaI=A-3**len(initial), alphaH=c['K']-3**len(final), v=q//R)
    first = old.run(prefix(c)[0][:-3], env); P = first[prefix(c)[1]]
    scale = q**10; r = P+(scale-1)//2
    env.update(r=r, betaP=scale-r)
    out = old.run(prefix(c)[0], env); out.update(K=c['K'], pell_tr1=2*r+1)
    assert all(x > 0 for k, x in env.items() if k not in PARAMETERS)
    assert all(out[a] == out[b] for a, b in outer_comparisons())
    former = dict(env, F_N=raw['N']+1); del former['F_T']
    before = old.run(previous.prefix(c)[0], former)
    before.update(K=c['K'], pell_tr1=2*r+1)
    assert all(before[a] == before[b] for a, b in previous.outer_comparisons())
    for name in ('N', 'radix', prefix(c)[1], 'index_rhs', 'packed_bound'):
        assert out[name] == before[name]
    conceptual = dict(out, S0=H-out['S1'], Gstar=out['Q']+A*H+H-out['S1'],
                      M0=out['L']-out['M1'], Ebar=c['c']*H-out['E'],
                      Nbar=out['Nsum']-out['N'])
    assert all(0 <= conceptual[f] < q and tag.boolean(conceptual[f]) for f in FIELDS)
    assert P == sum(conceptual[f]*q**i for i, f in enumerate(FIELDS))
    exponent = len(tag.trits(scale))-1
    assert old.unit.mask_expected(r, exponent) and old.unit.valuation(r) == exponent
    assert 27 <= r < scale and scale < r*r
    return dict(rows=t, T_zero=T == 0, zero_terminal=tag.value(final) == 0,
                index_parity=r % 2)


def histories():
    cases = rows = zeros = zero_final = unresolved = 0
    parities = [0, 0]
    for beta in (1, 2, 3):
        for a in (2, 3):
            for tail in product((0, 1), repeat=a-1):
                app = (0,)+tail
                for length in range(beta, beta+3):
                    for initial in product((0, 1), repeat=length):
                        w = tuple(initial); words = []; ss = []; ds = []
                        for _ in range(20):
                            if len(w) < beta:
                                break
                            words.append(w); ss.append(w[0]); ds.append(tag.value(w[:beta]))
                            w = w[beta:]+(app if w[0] else (0,))
                        if len(w) >= beta:
                            unresolved += 1; continue
                        v = witness(beta, app, initial, words, ss, ds, w)
                        cases += 1; rows += v['rows']; zeros += v['T_zero']
                        zero_final += v['zero_terminal']; parities[v['index_parity']] += 1
    assert cases and zeros and zero_final and min(parities) > 0
    return dict(canonical_histories=cases, rows=rows, T_zero_histories=zeros,
                zero_terminal_histories=zero_final, kernel_index_parities=parities,
                cutoff_unclassified=unresolved, preserved_indices=cases,
                outer_comparisons_per_version=10, conceptual_masks=10,
                scope='Fresh complete105 and106 outer tuples on actual histories stopping at their first halt. Packed integers, indices and all kernel parameters coincide; enormous Pell auxiliaries are supplied by the preserved converse.')


def verify():
    return dict(status='PASS_ZERO_LEADING_JOINT_TRANSPORT_105', source=verify_source(),
                identities=finite_identities(), histories=histories(),
                proof='../1980/EXPLORATION_JOINT_SCALED_TAG_TRANSPORT.md',
                review='Author and two independent complete proof/source reviews and fresh verification runs PASS; construction and arithmetic frozen.')


if __name__ == '__main__':
    result = verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(result['status'])
    print({k: result['source'][k] for k in ('operations', 'multiplications', 'additions', 'positive_unknowns', 'equations')})
    print(result['identities']); print(result['histories'])
