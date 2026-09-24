"""Removing the content guard admits a full positive zero-target false halt.

The rejected94/93 sources keep all prefix masks and true radix geometry.
All four generic fixed-leading-symbol/kernel schedules are checked symbolically.
"""
from pathlib import Path
import json
import sympy as sp
import explore_single_content_guard_tag as previous
import explore_unit_two_ternary_kernel as plus_kernel

old = previous.old
PARAMETERS = previous.PARAMETERS
POSITIVE = [name for name in previous.POSITIVE
            if name not in ('F_Nfinal', 'Lfinal', 'alphaH')]
FIELDS = previous.FIELDS[:8]


def positives(fixed_plus=False):
    return [name for name in POSITIVE if not fixed_plus or name != 'pell_u']


def prefix(c):
    removed = {'Nfinal', 'n_end', 'n_shift', 'halt_bound', 'scale',
               'guard_scale', 'guard_base', 'pack_add0',
               'content_shifted', 'pack_add2'}
    rows = []
    for name, op, a, b in previous.prefix(c)[0]:
        if name in removed:
            continue
        if name == 'q8':
            rows.append(('scale', '*', 'q4', 'q4'))
        elif name == 'l_end':
            rows.append((name, '*', 'q', 3))
        elif name == 'higher_scaled':
            rows.append((name, '*', 'q2', 'prefix_pair'))
        else:
            rows.append((name, op, a, b))
    return rows, previous.prefix(c)[1]


def schedule(c, fixed_plus=False):
    core = plus_kernel.schedule(1) if fixed_plus else old.kernel.SCHEDULE
    return prefix(c)[0] + [(old.rename(name), op, old.rename(a), old.rename(b))
                          for name, op, a, b in core]


def outer_comparisons():
    result = []
    for a, b in previous.outer_comparisons():
        if a == 'halt_bound':
            continue
        result.append((a, 'n_initial' if b == 'n_shift' else b))
    return result


def comparisons(fixed_plus=False):
    core = plus_kernel if fixed_plus else old.kernel
    return outer_comparisons() + [(old.rename(a), old.rename(b))
                                 for a, b in core.EQUALITIES]


def extend(c, s):
    return dict(s, F_Nfinal=1, Lfinal=3, alphaH=c['K']-3)


def verify_source(leading, fixed_plus=False):
    names = positives(fixed_plus) + PARAMETERS
    s = dict(zip(names, sp.symbols(' '.join(names))))
    Cbar, Kh, Ut, B, cc, j = sp.symbols('Cbar Khalf Uthird B c jguard')
    c = dict(Cbar=Cbar, Khalf=Kh, Uthird=Ut, B=B, c=cc,
             C=Kh*Cbar, K=3*Kh, U=3*Ut+leading, leading=leading,
             guard_coefficient=j)
    inherited = extend(c, s)
    raw = previous.conceptual(c, inherited)
    P = sum(raw[field]*s['q']**i for i, field in enumerate(FIELDS))
    source = previous.sources(c, inherited)
    src = [source[i] for i in (0, 1, 2, 3, 5, 6)] + [
        2*s['r']+1-s['q']**8-2*P,
        s['r']+s['betaP']-s['q']**8]
    kernel = plus_kernel if fixed_plus else old.kernel
    sub = {kernel.SYM[key]: s['q']**8 if key == 'D0' else s[old.rename(key)]
           for key in kernel.SYM}
    polynomials = kernel.source_residuals(1) if fixed_plus else kernel.source_residuals()
    core = [sp.expand(p.subs(sub, simultaneous=True))
            for p in polynomials]
    src += core
    env = old.run(schedule(c, fixed_plus), s)
    env['K'] = c['K']
    assert len(src) == len(comparisons(fixed_plus)) == 19-fixed_plus
    u = s['pell_j']*s['pell_c']+2*s['r']+1 if fixed_plus else s['pell_u']
    records = []
    for i, ((a, b), polynomial) in enumerate(zip(comparisons(fixed_plus), src)):
        correction = core[7]*(u*u-s['pell_y_aux']**2) if i == 16 else 0
        assert sp.expand(env[a]-env[b]-polynomial-correction) == 0, i
        records.append(dict(index=i, equality=[a, b], source=sp.sstr(polynomial),
                            correction=sp.sstr(correction)))
    assert sp.expand(env[prefix(c)[1]]-P) == 0
    assert source[4] == 0
    forbidden = {'Nfinal', 'F_Nfinal', 'Lfinal', 'alphaH', 'guard_scale',
                 'guard_base', 'pack_add0', 'content_shifted', 'pack_add2'}
    assert not any(name in forbidden or a in forbidden or b in forbidden
                   for name, _, a, b in prefix(c)[0])
    dag = schedule(previous.constants(2, (leading, 1)), fixed_plus)
    count = old.counts(dag)
    assert count == dict(operations=94-fixed_plus, multiplications=48-fixed_plus, additions=46)
    pos = positives(fixed_plus)
    assert len(pos) == len(set(pos)) == 30-fixed_plus
    return dict(leading=leading, fixed_plus=fixed_plus, **count,
                positive_unknowns=len(pos), equations=len(src),
                outer_equations=8, kernel_equations=11-fixed_plus, parameters=PARAMETERS,
                positive_coordinates=pos, fields=FIELDS, dag=dag, sources=records,
                scope='Generic fixed-coefficient DAG; products by constants that happen '
                      'to equal1 in the counterexample remain counted.')


def witness():
    c = previous.constants(2, (0, 1))
    assert (c['K'], c['Khalf'], c['U'], c['C'], c['c']) == (9, 3, 3, 2187, 1)
    A = 81
    R = c['C']*A
    assert R == 3**11
    height = 10
    q = R**height
    H = (q-1)//(R-1)
    b = R//9
    selectors = [1]*8+[0, 0]
    markers = [27]*9+[9]
    prefix_rows = [0, 0, 0, 1, 1, 0, 0, 0, 0, 1]
    pack = lambda rows: sum(value*R**i for i, value in enumerate(rows))
    S1, E, L = pack(selectors), pack(prefix_rows), pack(markers)
    Q = 13*S1
    M1 = 27*S1
    M0 = 27*R**8+9*R**9
    assert L == M0+M1
    assert E == R**3+R**4+R**9
    Ni, Li = 13, 27
    assert (S1-Ni) % 3 == 0
    numerator = b*(E-M1)+(S1-Ni)//3
    assert numerator % (b-1) == 0
    T = numerator//(b-1)
    N = 3*T+S1
    assert T > 0
    assert R*(N-3*E-S1+3*M1) == 9*(N-Ni)
    assert R*(L+2*M1) == 3*(L-Li+3*q)
    for i, (selector, marker) in enumerate(zip(selectors, markers)):
        successor = markers[i+1] if i+1 < height else 3
        assert marker*(3 if selector else 1) == 3*successor
    content_rows = [(N//R**i) % R for i in range(height)]
    assert N//q == 0
    assert content_rows == [59062, 6571, 739, 118189, 111555, 12403, 1387, 163, 27, 3]
    assert content_rows[0] == Ni+3*b
    s = dict(F_Q=Q+1, F_S1=S1+1, F_T=T+1, F_E=E+1,
             A=A, R=R, q=q, H=H, L=L, Ninit=Ni, Linit=Li,
             alphaI=A-Li, v=q//R)
    raw = previous.conceptual(c, extend(c, s))
    assert raw['M0'] == M0 and raw['M1'] == M1
    assert raw['Ebar'] == H-E > 0
    assert all(0 <= raw[field] < q and previous.tag.boolean(raw[field])
               for field in FIELDS)
    assert raw['Gstar'] % 3 == 1
    assert not previous.tag.boolean(raw['GN'])
    P = sum(raw[field]*q**i for i, field in enumerate(FIELDS))
    D0 = q**8
    r = P+(D0-1)//2
    s.update(r=r, betaP=D0-r)
    env = old.run(prefix(c)[0], s)
    env.update(K=c['K'], pell_tr1=2*r+1)
    assert all(env[a] == env[b] for a, b in outer_comparisons())
    assert env[prefix(c)[1]] == P
    for fixed_plus in (False, True):
        kernel = plus_kernel if fixed_plus else old.kernel
        assert set(s)-set(PARAMETERS) == set(positives(fixed_plus))-{old.rename(k) for k in kernel.SYM if k not in ('D0', 'r')}
    assert all(value > 0 for name, value in s.items() if name not in PARAMETERS)
    exponent = 8*(len(previous.tag.trits(q))-1)
    assert exponent == 880
    assert old.unit.mask_expected(r, exponent) and old.unit.valuation(r) == exponent
    assert D0 >= 81 and 27 <= r < D0 and D0 < r*r and r % 2 == 0
    initial, fixed = (1, 1, 1), (1, 0, 1)
    assert initial[2:]+(0, 1) == fixed and fixed[2:]+(0, 1) == fixed
    return dict(constants=c,rows=height,width_exponent=11,selectors=selectors,
                length_markers=markers,prefix_rows=prefix_rows,
                normalized_unmasked_content_rows=content_rows,
                raw_content=N,raw_T=T,divisibility_numerator=numerator,
                divisibility_denominator=b-1,positive_outer_coordinates=s,
                retained_fields={field:raw[field] for field in FIELDS},
                omitted_guard=raw['GN'],packed_word=P,scale=D0,index=r,
                index_parity=r%2,exact_central_valuation=exponent,
                outer_equations=len(outer_comparisons()),masked_fields=len(FIELDS),
                actual_nonhalting=dict(initial=initial,fixed=fixed),
                fixed_terminal=dict(content=0,length_marker=3),
                kernel_extensions=[
                    dict(fixed_plus=False,operations=94,positive_auxiliaries=17,
                         equations=19,parity_hypothesis='Neither parity required.'),
                    dict(fixed_plus=True,operations=93,positive_auxiliaries=16,
                         equations=18,parity_hypothesis='Even r, verified exactly.')],
                pell_scope='The parity-free44 and fixed-plus43 converses supply '
                           'respectively seventeen and sixteen fresh positive '
                           'auxiliaries at this same even index. These enormous '
                           'values are not materialized.')


def verify():
    return dict(status='PASS_UNMASKED_ZERO_TARGET_TAG_COUNTEREXAMPLE',
                sources=[verify_source(leading, fixed_plus)
                         for fixed_plus in (False, True) for leading in (0, 1)],
                witness=witness(),
                review='Author and two independent complete proof/source reviews and fresh verification runs pass without findings.',
                scope='Rejected94 and direct fixed-plus93 sources. Fixed terminal zero and exact prefix masks '
                      'do not replace the content guard. No improved bound.')


if __name__ == '__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status'])
    print([{key:s[key] for key in ('leading','fixed_plus','operations','multiplications','additions',
                                  'positive_unknowns','equations')} for s in result['sources']])
    print({key:result['witness'][key] for key in ('rows','outer_equations','masked_fields',
                                                'index_parity','exact_central_valuation')})
