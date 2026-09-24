"""Complete normalized ternary90 source; the raw-input universal bound is unchanged."""
from itertools import product
from pathlib import Path
import json
import sympy as sp

import explore_product_coordinate_tag as previous

old, tag, kernel = previous.old, previous.tag, previous.kernel
POSITIVE, PARAMETERS = previous.POSITIVE, previous.PARAMETERS
FIELDS = ['Ebar', 'E', 'S0', 'S1', 'Q', 'G', 'M0', 'M1', 'GN']
constants, fields, comparisons = previous.constants, previous.fields, previous.comparisons


def packing(c):
    return [
        ('prefix_head_coefficient', '+', c['c'], 'q2'),
        ('prefix_head_baseline', '*', 'prefix_head_coefficient', 'H'),
        ('head_shifted', '*', 'q2', 'S1'),
        ('prefix_head_digits', '+', 'E', 'head_shifted'),
        ('prefix_head_scaled', '*', 'qm1', 'prefix_head_digits'),
        ('low_four', '+', 'prefix_head_baseline', 'prefix_head_scaled'),
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
        ('upper_shifted', '*', 'q4', 'upper_five'),
        ('pack_add8', '+', 'low_four', 'upper_shifted'),
    ]


def prefix(c):
    rows = previous.prefix(c)[0]
    begin = next(i for i, row in enumerate(rows) if row[0] == 'guard_base')
    end = next(i for i, row in enumerate(rows) if row[0] == 'twiceP')
    return ([row for row in rows[:begin] if row[0] != 'prefix_scale']
            + packing(c) + rows[end:], 'pack_add8')


def schedule(c):
    return prefix(c)[0] + [(old.rename(n), op, old.rename(a), old.rename(b))
                           for n, op, a, b in kernel.schedule(1)]


def verify_source(leading):
    s = dict(zip(POSITIVE + PARAMETERS, sp.symbols(' '.join(POSITIVE + PARAMETERS))))
    C, k, Ut, B, cc, j = sp.symbols('C k Ut B cc jguard')
    c = dict(C=C, Cbar=C/k, Khalf=k, Uthird=Ut, B=B, c=cc, K=3*k,
             U=3*Ut+leading, leading=leading, guard_coefficient=j)
    D, Z, Q, S, T, E, R, H, L, q, r = [s[n] for n in
        ('transport_scale', 'AH', 'Q', 'S1', 'Tcontent', 'E', 'R', 'H', 'L', 'q', 'r')]
    N = 3*T+S if leading == 0 else 3*T-2*Q
    M1 = 2*Q+S
    raw = fields(c, s)
    P = sum(raw[f]*q**i for i, f in enumerate(FIELDS))
    source = [k*D-R, D*(T-E+Ut*M1)-N+s['Ninit'],
              D*(L+(B-1)*M1)-L+s['Linit']-3*q,
              R*H-H-q+1, R*H-C*Z, R*s['v']-q,
              2*r+1-q**9-2*P, r+s['betaP']-q**9]
    sub = {kernel.SYM[n]: q**9 if n == 'D0' else s[old.rename(n)] for n in kernel.SYM}
    core = [sp.expand(p.subs(sub, simultaneous=True)) for p in kernel.source_residuals(1)]
    source += core
    env = old.run(schedule(c), s)
    before = old.run(previous.schedule(c), s)
    u = s['pell_j']*s['pell_c']+2*r+1
    records = []
    assert len(source) == len(comparisons()) == 18
    for index, ((a, b), polynomial) in enumerate(zip(comparisons(), source)):
        correction = core[7]*(u*u-s['pell_y_aux']**2) if index == 16 else 0
        assert sp.expand(env[a]-env[b]-polynomial-correction) == 0, index
        if index != 6:
            assert sp.expand(env[a]-env[b]-before[a]+before[b]) == 0, index
        records.append(dict(index=index, equality=[a, b], source=sp.sstr(sp.expand(polynomial)),
                            correction=sp.sstr(sp.expand(correction))))
    assert sp.expand(env['pack_add8']-P) == 0
    generic = schedule(c)
    counts = old.counts(generic)
    assert counts == dict(operations=90, multiplications=49, additions=41)
    assert old.counts(packing(c)) == dict(operations=19, multiplications=9, additions=10)
    assert len(POSITIVE) == len(set(POSITIVE)) == 29
    assert sorted(FIELDS) == sorted(previous.FIELDS)
    return dict(leading=leading, **counts, positive_unknowns=29, equations=18,
                positive_coordinates=POSITIVE, parameters=PARAMETERS, fields=FIELDS,
                packing_operations=19, dag=[[str(x) if isinstance(x, sp.Basic) else x for x in row]
                                           for row in generic], sources=records)


def outer_pair(c, initial, words, selectors, prefixes, final):
    beta = len(tag.trits(c['K']))-1
    h, Li = beta-1, 3**len(initial)
    assert beta >= 3 and initial[:2] == (0, 0) and final == (0,)
    assert c['K']**2*Li < c['C'] and c['B'] >= 3
    ce = len(tag.trits(c['C']))-1
    m = max(ce+2+max(map(len, [initial]+words)), 2*h+3)
    if m % 2 == 0:
        m += 1
    R, t = 3**m, len(words)
    A, q0 = R//c['C'], R**t
    pack = lambda values: sum(value*R**i for i, value in enumerate(values))
    S = pack(selectors)
    Q = pack([si*(3**len(w)-1)//2 for si, w in zip(selectors, words)])
    E = pack([(d-si)//3 for d, si in zip(prefixes, selectors)])
    N, L0 = pack(map(tag.value, words)), pack(3**len(w) for w in words)
    T = (N-S)//3 if c['leading'] == 0 else (N+2*Q)//3
    assert min(Q, S, E, T) > 0
    results = []
    for padded in (False, True):
        height = t+(m-h if padded else 0)
        q, H = R**height, (R**height-1)//(R-1)
        delta = q0*3*sum((R//c['Khalf'])**i for i in range(m)) if padded else 0
        s = dict(Q=Q, S1=S, E=E, Tcontent=T, transport_scale=R//c['Khalf'], AH=A*H,
                 R=R, q=q, H=H, L=L0+delta, Ninit=tag.value(initial), Linit=Li, v=q//R)
        raw = fields(c, s)
        assert all(0 <= raw[f] < q and tag.boolean(raw[f]) for f in FIELDS)
        assert raw['Ebar'] % 3 == 1
        P = sum(raw[f]*q**i for i, f in enumerate(FIELDS))
        priorP = sum(raw[f]*q**i for i, f in enumerate(previous.FIELDS))
        scale = q**9
        r, priorr = P+(scale-1)//2, priorP+(scale-1)//2
        assert (P-priorP) % 2 == 0 and r % 2 == priorr % 2
        s.update(r=r, betaP=scale-r)
        env = old.run(prefix(c)[0], s)
        env['pell_tr1'] = 2*r+1
        assert env['pack_add8'] == P
        assert all(env[a] == env[b] for a, b in comparisons()[:8])
        prior = dict(s, r=priorr, betaP=scale-priorr)
        before = old.run(previous.prefix(c)[0], prior)
        before['pell_tr1'] = 2*priorr+1
        assert all(before[a] == before[b] for a, b in comparisons()[:8])
        assert all(value > 0 for name, value in s.items() if name not in PARAMETERS)
        exponent = 9*m*height
        assert old.unit.mask_expected(r, exponent) and old.unit.valuation(r) == exponent
        assert 27 <= r < scale and scale < r*r
        results.append(dict(padded=padded, height=height, index_parity=r % 2,
                            changed_index=r != priorr, valuation=exponent,
                            outer_equations=8, predecessor_outer_equations=8))
    assert results[0]['index_parity'] != results[1]['index_parity']
    return results


def history_checks():
    fixtures = set()
    for beta in (3, 4, 5, 6):
        for a in (3*beta-2, 4*beta-3):
            ell = a-beta+1
            structured = [0]*ell
            structured[2] = structured[beta] = 1
            for app in ((0,)*a, (1,)+(0,)*(a-1), (0, 1)+(0,)*(a-2)):
                for initial in (tuple(structured), (0, 0)+(1,)*(ell-2)):
                    fixtures.add((beta, app, initial))
    for a in (2, 3):
        for app in product((0, 1), repeat=a):
            for suffix in product((0, 1), repeat=4):
                fixtures.add((3, app, (0, 0, 1)+suffix))
    records = []
    cutoff = other_terminal = missing_startup = 0
    for beta, app, initial in sorted(fixtures):
        c = constants(beta, app)
        C = c['C']
        while C <= c['K']**2*3**len(initial):
            C *= 3
        c.update(C=C, Cbar=C//c['Khalf'], guard_coefficient=(C-C//c['K'])//2)
        w, words, ss, ds = initial, [], [], []
        for _ in range(120):
            if len(w) < beta:
                break
            words.append(w)
            ss.append(w[0])
            ds.append(tag.value(w[:beta]))
            w = w[beta:]+(app if w[0] else (0,))
        if len(w) >= beta:
            cutoff += 1
            continue
        if w != (0,):
            other_terminal += 1
            continue
        if not any(ss) or tag.value(initial[:beta])//3 == 0:
            missing_startup += 1
            continue
        records.append(dict(beta=beta, appendant=app, initial=initial, genuine_rows=len(words),
                            outer=outer_pair(c, initial, words, ss, ds, w)))
    branches = [sum(row['appendant'][0] == e for row in records) for e in (0, 1)]
    short = [sum(len(row['appendant']) == a for row in records) for a in (2, 3)]
    parities = [sum(row['outer'][0]['index_parity'] == p for row in records) for p in (0, 1)]
    assert min(branches) and min(short) and min(parities)
    assert any(row['beta'] % 2 for row in records)
    assert all(p['changed_index'] for row in records for p in row['outer'])
    return dict(histories=len(records), genuine_rows=sum(row['genuine_rows'] for row in records),
                full_outer_tuples=2*len(records), leading_branches=branches,
                short_appendant_lengths_2_3=short, canonical_index_parities=parities,
                cutoff_unclassified=cutoff, excluded_other_terminal=other_terminal,
                excluded_missing_startup=missing_startup, records=records,
                scope='Finite ordinary tag histories, including both parity choices; fresh positive Pell '
                      'extensions at the selected even indices follow from the established theorem.')


def verify():
    return dict(status='PASS_PREFIX_FIRST_TERNARY_TAG90', sources=[verify_source(e) for e in (0, 1)],
                histories=history_checks(), proof='../1980/EXPLORATION_PREFIX_FIRST_TERNARY_TAG.md',
                review='Author and two independent complete proof/source/dependency reviews PASS; fresh verification reproduces the saved receipt.',
                scope='Normalized encoded-instance certificate on initial00, positive-startup and '
                      'singleton-zero terminal histories. Neary001 is covered; no fixed raw-input improvement.')


if __name__ == '__main__':
    result = verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(result['status'])
    print([{k: row[k] for k in ('leading', 'operations', 'multiplications', 'additions', 'positive_unknowns', 'equations')}
           for row in result['sources']])
    print({k: v for k, v in result['histories'].items() if k not in ('records', 'scope')})
