"""Full positive counterexamples to deleting either ternary tag head mask."""
from pathlib import Path
import json
import sympy as sp
import explore_prefix_first_ternary_tag as previous

old, tag, kernel = previous.old, previous.tag, previous.kernel
POSITIVE, PARAMETERS = previous.POSITIVE, previous.PARAMETERS


def names(omit):
    assert omit in ('S0', 'S1')
    return [name for name in previous.FIELDS if name != omit]


def packing(c, omit):
    rows = [
        ('prefix_scale', '*', c['c'], 'H'),
        ('prefix_digits', '*', 'qm1', 'E'),
        ('prefix_pair', '+', 'prefix_scale', 'prefix_digits'),
        ('G', '+', 'Q', 'AH'), ('qG', '*', 'q', 'G'),
        ('QG_pair', '+', 'Q', 'qG'),
        ('marker_scaled', '*', 'qm1', 'M1'),
        ('marker_pair', '+', 'L', 'marker_scaled'),
        ('guard_base', '*', c['guard_coefficient'], 'AH'),
        ('GN', '+', 'N', 'guard_base'),
        ('content_shifted', '*', 'q2', 'GN'),
        ('marker_content', '+', 'marker_pair', 'content_shifted'),
        ('upper_pairs', '*', 'q2', 'marker_content'),
        ('upper_five', '+', 'QG_pair', 'upper_pairs'),
        ('upper_shifted', '*', 'q', 'upper_five'),
    ]
    if omit == 'S1':
        rows.append(('S0', '-', 'H', 'S1'))
    rows += [
        ('head_and_upper', '+', 'S1' if omit == 'S0' else 'S0', 'upper_shifted'),
        ('rest_shifted', '*', 'q2', 'head_and_upper'),
        ('pack_add8', '+', 'prefix_pair', 'rest_shifted'),
    ]
    return rows


def prefix(c, omit):
    prior = previous.prefix(c)[0]
    begin = next(i for i, row in enumerate(prior) if row[0] == 'prefix_head_coefficient')
    end = next(i for i, row in enumerate(prior) if row[0] == 'twiceP')
    before = []
    for name, op, a, b in prior[:begin]:
        if name == 'scale':
            continue
        before.append(('scale' if name == 'q8' else name, op, a, b))
    return before+packing(c, omit)+prior[end:]


def schedule(c, omit):
    return prefix(c, omit)+[(old.rename(n), op, old.rename(a), old.rename(b))
                           for n, op, a, b in kernel.schedule(1)]


def verify_source(omit, leading):
    s = dict(zip(POSITIVE+PARAMETERS, sp.symbols(' '.join(POSITIVE+PARAMETERS))))
    C, k, Ut, B, cc, j = sp.symbols('C k Ut B cc jguard')
    c = dict(C=C, Cbar=C/k, Khalf=k, Uthird=Ut, B=B, c=cc, K=3*k,
             U=3*Ut+leading, leading=leading, guard_coefficient=j)
    D, Z, Q, S, T, E, R, H, L, q, r = [s[n] for n in
        ('transport_scale', 'AH', 'Q', 'S1', 'Tcontent', 'E', 'R', 'H', 'L', 'q', 'r')]
    N = 3*T+S if leading == 0 else 3*T-2*Q
    M1 = 2*Q+S
    raw = previous.fields(c, s)
    P = sum(raw[f]*q**i for i, f in enumerate(names(omit)))
    source = [k*D-R, D*(T-E+Ut*M1)-N+s['Ninit'],
              D*(L+(B-1)*M1)-L+s['Linit']-3*q,
              R*H-H-q+1, R*H-C*Z, R*s['v']-q,
              2*r+1-q**8-2*P, r+s['betaP']-q**8]
    sub = {kernel.SYM[n]: q**8 if n == 'D0' else s[old.rename(n)] for n in kernel.SYM}
    core = [sp.expand(p.subs(sub, simultaneous=True)) for p in kernel.source_residuals(1)]
    source += core
    env = old.run(schedule(c, omit), s)
    u = s['pell_j']*s['pell_c']+2*r+1
    records = []
    assert len(source) == len(previous.comparisons()) == 18
    for index, ((a, b), polynomial) in enumerate(zip(previous.comparisons(), source)):
        correction = core[7]*(u*u-s['pell_y_aux']**2) if index == 16 else 0
        assert sp.expand(env[a]-env[b]-polynomial-correction) == 0, index
        records.append(dict(index=index, equality=[a, b], source=sp.sstr(sp.expand(polynomial)),
                            correction=sp.sstr(sp.expand(correction))))
    assert sp.expand(env['pack_add8']-P) == 0
    counts = old.counts(schedule(c, omit))
    expected = dict(operations=88+(omit == 'S1'), multiplications=48,
                    additions=40+(omit == 'S1'))
    assert counts == expected, counts
    assert len(POSITIVE) == len(set(POSITIVE)) == 29
    return dict(omitted_mask=omit, leading=leading, **counts, equations=18,
                positive_unknowns=29, positive_coordinates=POSITIVE, parameters=PARAMETERS,
                fields=names(omit), kernel_sign=1, kernel_operations=43,
                packing=old.counts(packing(c, omit)),
                dag=[[str(x) if isinstance(x, sp.Basic) else x for x in row]
                     for row in schedule(c, omit)], sources=records)


def constants():
    c = previous.constants(3, (0, 1, 0))
    c.update(C=3**14, Cbar=3**12, guard_coefficient=(3**14-3**11)//2)
    return c


def ordinary_step(word):
    assert len(word) >= 3
    return word[3:]+((0, 1, 0) if word[0] else (0,))


def nonhalting_check():
    initial = tuple(map(int, '0011001'))
    fixed = tuple(map(int, '10010'))
    assert ordinary_step(initial) == fixed and ordinary_step(fixed) == fixed
    assert len(initial) >= 3 and len(fixed) >= 3 and fixed[0] == 1
    assert initial[:2] == (0, 0) and tag.value(initial[:3])//3 > 0
    return dict(initial='0011001', prefix=['0011001'], cycle=['10010'],
                beta=3, appendant='010', genuine_one_reading=True,
                scope='Exact fixed-point nonhalting proof; not a bounded simulation inference.')


def witness(omit):
    c = constants()
    if omit == 'S0':
        strings = ['0011001', '1001010', '1010010', '0010010', '00100', '000']
        selectors = [9, 1, 1, 0, 0, 0]
        qs = [(3**len(w)-s)//2 if s else 0 for w, s in zip(strings, selectors)]
        prefix_rows = [0, 0, 3, 3, 3, 0]
        padded = True
        changed = 0
    else:
        strings = ['0011001', '10010', '100', '010']
        selectors = [0, -2, 1, 0]
        qs = [0, 1, 13, 0]
        prefix_rows = [3, 1, 0, 1]
        padded = False
        changed = 1
    words = [tuple(map(int, w)) for w in strings]
    numbers = list(map(tag.value, words))
    markers = [3**len(w) for w in words]
    tr = []
    for i, (n, L, S, Q, E) in enumerate(zip(numbers, markers, selectors, qs, prefix_rows)):
        M1 = 2*Q+S
        nn = numbers[i+1] if i+1 < len(words) else 0
        LL = markers[i+1] if i+1 < len(words) else 3
        assert M1 in (0, L)
        assert n-3*E-S+c['U']*M1 == c['K']*nn
        assert L+(c['B']-1)*M1 == c['Khalf']*LL
        T, rem = divmod(n-S, 3)
        assert rem == 0 and T >= 0
        tr.append(T)
        expected = words[i+1] if i+1 < len(words) else (0,)
        assert (ordinary_step(words[i]) == expected) == (i != changed)
        assert all(tag.boolean(x) for x in (Q, E, c['c']-E, M1, L-M1, n))
        assert tag.boolean(S if omit == 'S0' else 1-S)
    assert c['C'] > c['K']**2*markers[0]
    A, m, h = 3**9, 23, 2
    R = c['C']*A
    assert R == 3**m and A > max(markers)
    t = len(words)
    pack = lambda values: sum(v*R**i for i, v in enumerate(values))
    Q, S, E, N, L0, T = map(pack, (qs, selectors, prefix_rows, numbers, markers, tr))
    assert N == 3*T+S and min(Q, S, E, T) > 0
    q0 = R**t
    height = t+(m-h if padded else 0)
    q = R**height
    H = (q-1)//(R-1)
    delta = 3*q0*sum((R//c['Khalf'])**i for i in range(m)) if padded else 0
    assert (R//c['Khalf']-1)*delta == 3*(q-q0)
    s = dict(Q=Q, S1=S, Tcontent=T, E=E, H=H, R=R, L=L0+delta, q=q, v=q//R,
             transport_scale=R//c['Khalf'], AH=A*H, Ninit=numbers[0], Linit=markers[0])
    raw = previous.fields(c, s)
    assert all(0 <= raw[f] < q and tag.boolean(raw[f]) for f in names(omit))
    assert raw[omit] > 0 and not tag.boolean(raw[omit])
    assert raw['Ebar'] % 3 == 1
    P = sum(raw[f]*q**i for i, f in enumerate(names(omit)))
    D0, exponent = q**8, 8*m*height
    r = P+(D0-1)//2
    s.update(r=r, betaP=D0-r)
    env = old.run(prefix(c, omit), s)
    env['pell_tr1'] = 2*r+1
    assert all(env[a] == env[b] for a, b in previous.comparisons()[:8])
    assert env['pack_add8'] == P and env['scale'] == D0
    assert all(value > 0 for name, value in s.items() if name not in PARAMETERS)
    assert D0 >= 81 and 27 <= r < D0 and D0 < r*r
    assert r % 2 == 0 and old.unit.mask_expected(r, exponent)
    assert old.unit.valuation(r) == exponent
    assert exponent == (4968 if omit == 'S0' else 736)
    if omit == 'S1':
        assert S == R*R-2*R and tr == [255, 10, 0, 1]
    return dict(omitted_mask=omit, constants=c, initial=strings[0], beta=3, appendant='010',
                false_source_words=strings, terminal='0', changed_row=changed,
                effective_selector_rows=selectors, projector_rows=qs, prefix_rows=prefix_rows,
                content_adapter_rows=tr, original_source_rows=t, formal_height=height,
                zero_edge_padding=padded, padding_length_word=delta,
                width_power=m, width_coordinate=A, time_radix=R,
                positive_outer_coordinates=s, retained_fields={f: raw[f] for f in names(omit)},
                omitted_field_value=raw[omit], omitted_field_still_positive=True,
                packed_word=P, scale=D0, index=r, index_parity=0,
                exact_central_valuation=exponent, outer_equations=8,
                retained_masks=8,
                kernel_extension='Sixteen fresh positive auxiliaries from the general-scale fixed-plus43 converse; exact construction given in the proof, enormous values not materialized.',
                scope='Full positive solution of the specified deleted-mask source, on startup00 with an actual genuine one-reading event. This is not a full Neary Table2 instance.')


def verify():
    return dict(status='PASS_DELETED_TAG_HEAD_MASK_COUNTEREXAMPLES',
                sources=[verify_source(omit, leading) for omit in ('S0', 'S1') for leading in (0, 1)],
                genuine_nonhalting=nonhalting_check(), witnesses=[witness(omit) for omit in ('S0', 'S1')],
                proof='../1980/EXPLORATION_DELETED_TAG_HEAD_MASKS.md',
                review='Author and two independent complete proof/source reviews and fresh receipt checks PASS; one reviewer also contributed the local S1-deletion mechanism.',
                scope='Rejected88 and89 head-mask deletion sources. The valid90 source retains both masks. No universal improvement or full-Neary impossibility claim.')


if __name__ == '__main__':
    result = verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(result['status'])
    print([{key: x[key] for key in ('omitted_mask', 'leading', 'operations', 'multiplications', 'additions')}
           for x in result['sources']])
    print([{key: x[key] for key in ('omitted_mask', 'original_source_rows', 'formal_height', 'exact_central_valuation')}
           for x in result['witnesses']])
