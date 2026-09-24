"""Full positive counterexamples to either single prefix-mask deletion.

The rejected eight-field sources have102 and100 operations respectively.
The valid nine-field104 source is imported unchanged.
"""
from pathlib import Path
import json
import sympy as sp
import explore_single_content_guard_tag as previous

old = previous.old
MODES = ('E', 'Ebar')


def fields(omitted):
    assert omitted in MODES
    return [f for f in previous.FIELDS if f != omitted]


def prefix(c, omitted):
    assert omitted in MODES
    removed = {'scale', 'prefix_scaled'}
    if omitted == 'Ebar':
        removed.update(('prefix_scale', 'prefix_pair'))
    rows = []
    for name, op, a, b in previous.prefix(c)[0]:
        if name in removed:
            continue
        if name == 'q8':
            rows.append(('scale', '*', 'q4', 'q4'))
        elif name == 'prefix_pair':
            rows.append((name, '-', 'prefix_scale', 'E'))
        elif name == 'content_shifted':
            rows.append((name, '*', 'q', 'pack_add0'))
        elif name == 'pack_add2' and omitted == 'Ebar':
            rows.append((name, '+', 'E', 'content_shifted'))
        else:
            rows.append((name, op, a, b))
    return rows, previous.prefix(c)[1]


def schedule(c, omitted):
    return prefix(c, omitted)[0]+[(old.rename(n), op, old.rename(a), old.rename(b))
                                  for n, op, a, b in old.kernel.SCHEDULE]


def verify_source(omitted, leading):
    names = previous.POSITIVE+previous.PARAMETERS
    s = dict(zip(names, sp.symbols(' '.join(names))))
    Cbar, Kh, Ut, B, cc, j = sp.symbols('Cbar Khalf Uthird B c jguard')
    c = dict(Cbar=Cbar, Khalf=Kh, Uthird=Ut, B=B, c=cc, C=Kh*Cbar, K=3*Kh,
             U=3*Ut+leading, leading=leading, guard_coefficient=j)
    env = old.run(schedule(c, omitted), s)
    env['K'] = c['K']
    raw = previous.conceptual(c, s)
    P = sum(raw[f]*s['q']**i for i, f in enumerate(fields(omitted)))
    src = previous.sources(c, s)[:7]+[
        2*s['r']+1-s['q']**8-2*P, s['r']+s['betaP']-s['q']**8]
    sub = {old.kernel.SYM[k]: s['q']**8 if k == 'D0' else s[old.rename(k)]
           for k in old.kernel.SYM}
    core = [sp.expand(p.subs(sub, simultaneous=True)) for p in old.kernel.source_residuals()]
    src += core
    assert len(src) == len(previous.comparisons()) == 20
    records = []
    for i, ((a, b), polynomial) in enumerate(zip(previous.comparisons(), src)):
        correction = core[7]*(s['pell_u']**2-s['pell_y_aux']**2) if i == 17 else 0
        assert sp.expand(env[a]-env[b]-polynomial-correction) == 0, i
        records.append(dict(index=i, equality=[a, b], source=sp.sstr(polynomial),
                            correction=sp.sstr(correction)))
    assert sp.expand(env[prefix(c, omitted)[1]]-P) == 0
    count = old.counts(schedule(previous.constants(2, (leading, 1)), omitted))
    expected = dict(operations=102, multiplications=51, additions=51) if omitted == 'E' else \
        dict(operations=100, multiplications=50, additions=50)
    assert count == expected
    return dict(omitted=omitted, leading=leading, **count,
                positive_unknowns=len(previous.POSITIVE), exact_source_comparisons=len(src),
                fields=fields(omitted), positive_coordinates=previous.POSITIVE,
                parameters=previous.PARAMETERS, dag=schedule(previous.constants(2, (leading, 1)), omitted),
                sources=records)


def example_rows(omitted):
    if omitted == 'E':
        return dict(content=[13, 91, 28, 12, 1, 3], length_markers=[27, 27, 27, 27, 9, 9],
                    prefix_rows=[-242, -27, 0, 1, 0, 1], sparse_extras=[81, 9, 0, 0, 0, 0])
    assert omitted == 'Ebar'
    return dict(content=[13, 9, 1, 3], length_markers=[27, 27, 9, 9],
                prefix_rows=[4, 0, 0, 1], sparse_extras=None)


def witness(omitted):
    c = previous.constants(2, (0, 1))
    assert c['K'] == 9 and c['U'] == 3 and c['C'] == 2187 and c['c'] == 1
    rows = example_rows(omitted)
    numbers, markers, prefixes = (rows[name] for name in ('content', 'length_markers', 'prefix_rows'))
    selectors = [n % 3 for n in numbers]
    deleted = [3*e+s for e, s in zip(prefixes, selectors)]
    for i, (number, marker, selector, d) in enumerate(zip(numbers, markers, selectors, deleted)):
        assert selector in (0, 1)
        output = number-d+c['U']*selector*marker
        assert output >= 0 and output % c['K'] == 0
        assert output//c['K'] == (numbers[i+1] if i+1 < len(numbers) else 0)
        assert marker*(9 if selector else 3)//c['K'] == (markers[i+1] if i+1 < len(markers) else 3)
        assert previous.tag.boolean(number)
        if omitted == 'E':
            extra = rows['sparse_extras'][i]
            assert previous.tag.boolean(extra)
            assert d == number % c['K']-c['K']*extra
            assert previous.tag.boolean(c['c']-prefixes[i])
        else:
            assert previous.tag.boolean(prefixes[i])
    A = 81
    R = c['C']*A
    height = len(numbers)
    q = R**height
    H = (q-1)//(R-1)
    pack = lambda values: sum(v*R**i for i, v in enumerate(values))
    N, E, S1 = pack(numbers), pack(prefixes), pack(selectors)
    Q = pack([s*(marker-1)//2 for s, marker in zip(selectors, markers)])
    M1 = pack([s*marker for s, marker in zip(selectors, markers)])
    M0 = pack([(1-s)*marker for s, marker in zip(selectors, markers)])
    assert (N-S1) % 3 == 0
    T = (N-S1)//3
    assert E > 0 and T >= 0
    supplied = dict(F_Q=Q+1, F_S1=S1+1, F_T=T+1, F_E=E+1, F_Nfinal=1,
                    A=A, R=R, q=q, H=H, L=M0+M1, Lfinal=3, Ninit=13, Linit=27,
                    alphaI=A-27, alphaH=c['K']-3, v=q//R)
    raw = previous.conceptual(c, supplied)
    assert raw['Ebar'] == pack([c['c']-e for e in prefixes])
    assert raw['E'] > 0 and raw['Ebar'] > 0
    assert not previous.tag.boolean(raw[omitted])
    assert all(0 <= raw[f] < q and previous.tag.boolean(raw[f]) for f in fields(omitted))
    assert raw['Gstar'] % 3 == 1
    P = sum(raw[f]*q**i for i, f in enumerate(fields(omitted)))
    scale = q**8
    index = P+(scale-1)//2
    supplied.update(r=index, betaP=scale-index)
    env = old.run(prefix(c, omitted)[0], supplied)
    env.update(K=c['K'], pell_tr1=2*index+1)
    assert all(env[a] == env[b] for a, b in previous.outer_comparisons())
    assert env[prefix(c, omitted)[1]] == P
    assert all(value > 0 for name, value in supplied.items() if name not in previous.PARAMETERS)
    exponent = 8*(len(previous.tag.trits(q))-1)
    assert exponent == (528 if omitted == 'E' else 352)
    assert old.unit.mask_expected(index, exponent) and old.unit.valuation(index) == exponent
    assert 27 <= index < scale and scale < index*index
    actual, fixed = (1, 1, 1), (1, 0, 1)
    assert actual[2:]+(0, 1) == fixed and fixed[2:]+(0, 1) == fixed
    return dict(omitted=omitted, constants=c, positive_outer_coordinates=supplied, raw_fields=raw,
                source_rows=dict(**rows, selectors=selectors, deleted_prefixes=deleted,
                                 complement_prefixes=[c['c']-e for e in prefixes]),
                scale=scale, packed_word=P, index=index, index_parity=index % 2,
                exact_central_valuation=exponent,
                exact_outer_comparisons=len(previous.outer_comparisons()), masked_fields=len(fields(omitted)),
                actual_nonhalting=dict(initial=actual, fixed=fixed),
                scope='Complete positive outer tuple and all eight individual fields. The established '
                      'parity-free44 converse supplies fresh positive Pell auxiliaries; enormous '
                      'auxiliaries are not materialized.')


def verify():
    return dict(status='PASS_PREFIX_MASK_DELETION_COUNTEREXAMPLES',
                sources=[verify_source(omitted, leading) for omitted in MODES for leading in (0, 1)],
                false_tuples=[witness(omitted) for omitted in MODES],
                review='Author and two independent complete proof/source reviews and fresh verification runs pass without findings.',
                scope='Both reductions are rejected. The valid nine-field104 source remains unchanged; '
                      'no improvement of its bound is claimed.')


if __name__ == '__main__':
    result = verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(result['status'])
    print([{k: s[k] for k in ('omitted', 'leading', 'operations', 'multiplications', 'additions')}
           for s in result['sources']])
    print([{k: v[k] for k in ('omitted', 'exact_outer_comparisons', 'masked_fields',
                             'exact_central_valuation', 'index_parity')}
           for v in result['false_tuples']])
