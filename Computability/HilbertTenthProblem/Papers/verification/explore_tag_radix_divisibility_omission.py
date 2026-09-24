"""Deleting q=Rv: exact104 source and a full positive nonpower-R family.

The fixed input actually halts. This disproves implicit radix recovery,
not the weakened source's halting semantics.
"""
from pathlib import Path
import json
import sympy as sp

import explore_general_scaled_tag_transport as previous

old = previous.old
tag = previous.tag
POSITIVE = [x for x in previous.POSITIVE if x != 'v']
PARAMETERS = previous.PARAMETERS


def prefix(c):
    before, last = previous.prefix(c)
    assert [row for row in before if row[0] == 'radix_product'] == [
        ('radix_product', '*', 'R', 'v')]
    return [row for row in before if row[0] != 'radix_product'], last


def schedule(c):
    return prefix(c)[0]+[(old.rename(n), op, old.rename(a), old.rename(b))
                         for n, op, a, b in old.kernel.SCHEDULE]


def outer_comparisons():
    return [p for p in previous.outer_comparisons() if p != ('radix_product', 'q')]


def comparisons():
    return outer_comparisons()+[(old.rename(a), old.rename(b))
                                for a, b in old.kernel.EQUALITIES]


def verify_source(leading):
    s = dict(zip(POSITIVE+PARAMETERS, sp.symbols(' '.join(POSITIVE+PARAMETERS))))
    Cbar, Kh, Ut, B, cc = sp.symbols('Cbar Khalf Uthird B c')
    c = dict(Cbar=Cbar, Khalf=Kh, Uthird=Ut, B=B, c=cc, C=Kh*Cbar,
             K=3*Kh, U=3*Ut+leading, leading=leading)
    env = old.run(schedule(c), s); env['K'] = c['K']
    fresh = previous.sources(c, dict(s, v=sp.Symbol('discarded_v')))
    assert previous.outer_comparisons()[7] == ('radix_product', 'q')
    source = fresh[:7]+fresh[8:]
    assert all(sp.Symbol('discarded_v') not in p.free_symbols for p in source)
    sub = {old.kernel.SYM[k]: s['q']**10 if k == 'D0' else s[old.rename(k)]
           for k in old.kernel.SYM}
    core = [sp.expand(p.subs(sub, simultaneous=True))
            for p in old.kernel.source_residuals()]
    source += core
    records = []
    assert len(source) == len(comparisons()) == 20
    for index, ((a, b), p) in enumerate(zip(comparisons(), source)):
        correction = core[7]*(s['pell_u']**2-s['pell_y_aux']**2) if index == 17 else 0
        assert sp.expand(env[a]-env[b]-p-correction) == 0, index
        records.append(dict(index=index, equality=[a, b], source=sp.sstr(p),
                            correction=sp.sstr(correction)))
    assert all('v' not in (n, a, b) and 'radix_product' not in (n, a, b)
               for n, _, a, b in prefix(c)[0])
    dag = schedule(tag.constants(3, (leading, 1, 0)))
    assert old.counts(dag) == dict(operations=104, multiplications=52, additions=52)
    assert len(POSITIVE) == len(set(POSITIVE)) == 33
    return dict(**old.counts(dag), leading=leading, positive_unknowns=33,
                equations=20, outer_equations=9, kernel_equations=11,
                positive_coordinates=POSITIVE, parameters=PARAMETERS, dag=dag,
                source_checks=records, semantic_status='OPEN',
                deleted_instruction=['radix_product', '*', 'R', 'v'])


def family(k):
    assert k >= 5
    beta, app = 3, (0, 1, 0)
    c = tag.constants(beta, app)
    assert c['C'] == 81 and c['K'] == 27 and c['Khalf'] == 9
    h = 3**k; q = h**4; R = h**3-h*h+h; H = 1+h; A = R//81
    Q, S1 = 4*h, h
    raw = dict(Gstar=1+4*h+3**(4*k-4)+3**(k-4), Q=Q, S0=1, S1=S1,
               M0=81, M1=9*h, Ebar=4*H, E=0, Nbar=13+3*h, N=27+h)
    Nsum, L, T = 40+4*h, 81+9*h, 9
    assert R % 81 == 0 and H*(R-1) == q-1 and A > 81
    factor = h*h-h+1
    assert R == h*factor and factor > 1 and factor % 3 == 1
    assert q % R != 0
    assert Q+A*H+1 == raw['Gstar']
    assert 2*Q+S1 == raw['M1'] and 2*Nsum+H == L
    assert raw['N']+raw['Nbar'] == Nsum and raw['Ebar'] == c['c']*H
    assert all(0 <= raw[f] < q and tag.boolean(raw[f]) for f in previous.FIELDS)
    assert raw['Gstar'] % 3 == 1
    env = dict(F_Q=Q+1, F_S1=S1+1, F_T=T+1, F_E=1, F_Nfinal=2,
               Nsum=Nsum, A=A, H=H, R=R, L=L, q=q, Lfinal=9,
               alphaI=A-81, alphaH=18, Ninit=27, Linit=81)
    first = old.run(prefix(c)[0][:-3], env); P = first[prefix(c)[1]]
    scale = q**10; r = P+(scale-1)//2
    env.update(r=r, betaP=scale-r)
    actual = old.run(prefix(c)[0], env)
    actual.update(K=c['K'], pell_tr1=2*r+1)
    assert all(actual[a] == actual[b] for a, b in outer_comparisons())
    assert all(value > 0 for name, value in env.items() if name not in PARAMETERS)
    assert P == sum(raw[f]*q**j for j, f in enumerate(previous.FIELDS))
    assert 0 < P <= (scale-1)//2 and 27 <= r < scale and scale < r*r
    assert old.unit.mask_expected(r, 40*k) and old.unit.valuation(r) == 40*k
    assert A > 81 and q >= R and R > c['K']**2
    assert R*(raw['N']-S1+c['U']*raw['M1']) == c['K']*(raw['N']-27+q)
    assert R*(L+(c['B']-1)*raw['M1']) == c['Khalf']*(L-81+9*q)
    # The actual specified input stops after one legal step.
    initial = (0, 0, 0, 1)
    final = initial[beta:]+(app if initial[0] else (0,))
    assert final == (1, 0) and len(final) < beta
    return dict(k=k, A=A, R=R, q=q, H=H, initial=[27, 81], terminal=[1, 9],
                raw_fields=raw, content_sum=Nsum, length_sum=L, T=T,
                outer_comparisons=9, conceptual_masks=10, q_mod_R=q % R,
                packed_bits=P.bit_length(), index_bits=r.bit_length(),
                exact_valuation=40*k, positive_kernel_hypotheses=True,
                actual_halting_steps=1)


def verify():
    return dict(status='PASS_NONPOWER_TAG_RADIX_OBSTRUCTION',
                sources=[verify_source(e) for e in (0, 1)],
                family=[family(k) for k in (5, 6, 7, 8, 12, 16, 24, 32)],
                proof='../1980/EXPLORATION_TAG_RADIX_DIVISIBILITY_OMISSION.md',
                review='Author and two independent complete proof/source reviews and fresh verification runs PASS; proof and arithmetic frozen; halting semantics OPEN.',
                scope=('A full positive solution family of the weakened104 source exists with '
                       'nonpower R and R not dividing q. The actual fixed input halts after one '
                       'step, so this is not a false positive for halting. It rules out implicit '
                       'recovery or same-coordinate embedding into105. Nine actual outer '
                       'comparisons, all masks and the valuation are materialized; the generic '
                       '44-operation converse supplies all positive Pell auxiliaries. Their '
                       'enormous values are not materialized. The104 halting semantics remain open.'))


if __name__ == '__main__':
    result = verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(result['status'])
    print([{k: s[k] for k in ('leading', 'operations', 'multiplications', 'additions', 'positive_unknowns', 'equations')}
           for s in result['sources']])
    print('full outer families', len(result['family']), 'valuations', [v['exact_valuation'] for v in result['family']])
