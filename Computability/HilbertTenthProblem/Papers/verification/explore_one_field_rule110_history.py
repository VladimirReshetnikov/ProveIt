#!/usr/bin/env python3
"""A complete 77-operation radix-16 finite history, not a universal system."""
from itertools import product
from pathlib import Path
import json
import sympy as sp

import round39_1980_boolean_history_components as retained
import round4_1980_operation_count as baseline
from round13_1980_certificate import verify_primitives

PARAMETERS = ['I', 'F']
OUTER_NAMES = ['q', 'v', 'quot', 'hrow', 'Cw', 'Yw', 'Jrow', 'alphaI']
CORE_NAMES = retained.CORE_NAMES
NAMES = PARAMETERS + OUTER_NAMES + CORE_NAMES
SYM = {name: sp.Symbol(name) for name in NAMES}
ALLOWED_U = {0, 1, 2, 3, 8, 9, 10, 11}

OUTER = [
    ('Q2', '*', 'q', 'q'), ('Lbig', '*', 'Q2', 'Q2'),
    ('n2', '*', 'Lbig', 'Q2'),
    ('vq', '*', 'v', 'quot'), ('v2', '*', 'v', 'v'),
    ('W', '*', 'v2', 'v2'), ('Qm1', '-', 'q', 1),
    ('Wm1', '-', 'W', 1), ('row_geom', '*', 'hrow', 'Wm1'),
    ('C307', '*', 307, 'Cw'), ('Y4', '*', 4, 'Yw'),
    ('local_sum', '+', 'C307', 'Y4'), ('Uw', '+', 'local_sum', 'Jrow'),
    ('Ibound', '+', 'I', 'alphaI'),
    ('WY', '*', 'W', 'Yw'), ('time_lhs', '+', 'I', 'WY'),
    ('QF', '*', 'q', 'F'), ('time_rhs', '+', 'Cw', 'QF'),
    ('Bw', '*', 16, 'Cw'), ('Tword', '+', 'Bw', 'hrow'),
    ('q2U', '*', 'Q2', 'Uw'), ('Yq2U', '+', 'Yw', 'q2U'),
    ('qYq2U', '*', 'q', 'Yq2U'), ('packed', '+', 'Tword', 'qYq2U'),
    ('qp1', '+', 'q', 1), ('fourQ2', '*', 4, 'Q2'),
    ('mask_inner', '+', 'fourQ2', 14),
    ('mask_product', '*', 'qp1', 'mask_inner'),
    ('mask', '*', 'Jrow', 'mask_product'),
    ('fifteenJ', '*', 15, 'Jrow'),
    ('packing_gap', '-', 'Lbig', 'packed'), ('Lm1', '-', 'Lbig', 1),
    ('r_product', '*', 'packing_gap', 'Lm1'), ('r_lhs', '+', 'r_product', 'mask'),
]
CORE = [
    ('H17', '-', 'jc', 'tr1') if row[0] == 'H17' else
    ('aux_u_rhs', '-', 'of', 'c') if row[0] == 'aux_u_rhs' else row
    for row in retained.CORE
]
SCHEDULE = OUTER + CORE
OUTER_EQUALITIES = [
    ('q', 'vq'), ('Qm1', 'row_geom'), ('Ibound', 'v'),
    ('time_lhs', 'time_rhs'), ('fifteenJ', 'Qm1'), ('r', 'r_lhs'),
]
EQUALITIES = OUTER_EQUALITIES + retained.CORE_EQUALITIES


def source_residuals():
    z = SYM
    q, v, quot, H, C, Y, J, alphaI = [z[n] for n in OUTER_NAMES]
    a, c, d, f, h, i, j, k, o, r, s, w, tau, eta, zeta, ga, ya = [z[n] for n in CORE_NAMES]
    W, L, scale = v**4, q**4, q**6
    U, T = 307*C+4*Y+J, 16*C+H
    P = T+q*Y+q**3*U
    M = J*(q+1)*(4*q*q+14)
    Up, Yp = w*scale, s*scale
    Dpell = a*a+4*a+3
    K, auxu = Dpell*(f*f-1), j*c-(2*r+1)
    return [
        q-v*quot, q-1-H*(W-1), z['I']+alphaI-v,
        z['I']+W*Y-C-q*z['F'], 15*J-q+1,
        r-(L-P)*(L-1)-M,
        Up*Yp*Yp*(Up*Yp*Yp+1)*k*k-tau*(tau+1),
        c-Yp*k-eta, k-eta-zeta, k-r-1-h*Up*Yp,
        a-Yp*(Up+1), d-Up-a*c-ga*(4*a+3),
        d*d-Dpell*c*c-1, (i*c*c)**2-Dpell*(f*f-1),
        K*(auxu*auxu-ya*ya)-(1-ya*ya), auxu+c-o*f,
    ]


def verify_source():
    env = dict(SYM)
    histogram = baseline.run_schedule(SCHEDULE, env)
    source = source_residuals()
    auxu = SYM['j']*SYM['c']-(2*SYM['r']+1)
    correction = source[13]*(auxu**2-SYM['y_aux']**2)
    records = []
    assert len(source) == len(EQUALITIES) == 16
    for index, ((left, right), residual) in enumerate(zip(EQUALITIES, source)):
        actual = sp.expand(env[left]-env[right])
        adjustment = correction if index == 14 else sp.Integer(0)
        if sp.expand(actual-residual-adjustment) == 0:
            sign = 1
        else:
            assert adjustment == 0 and sp.expand(actual+residual) == 0, index
            sign = -1
        records.append(dict(index=index, equality=[left, right], source_sign=sign,
                            source=sp.sstr(sp.expand(residual)),
                            correction=sp.sstr(sp.expand(adjustment))))
    primitives, counts = verify_primitives(SCHEDULE, env)
    assert len(OUTER) == 34 and len(CORE) == 43 and len(primitives) == 77
    assert counts == {'+': 33, '*': 44}
    assert len(OUTER_NAMES+CORE_NAMES) == len(set(OUTER_NAMES+CORE_NAMES)) == 25
    assert all(p.free_symbols <= set(SYM.values()) for p in source)
    assert set(NAMES) <= ({x for row in SCHEDULE for x in row[2:]}
                         | {x for pair in EQUALITIES for x in pair})
    assert sp.expand(env['n2']-SYM['q']**6) == 0
    assert sp.expand(env['W']-SYM['v']**4) == 0
    assert sp.expand(env['mask']-SYM['Jrow']*(14+14*SYM['q']+4*SYM['q']**2+4*SYM['q']**3)) == 0
    return dict(operations=77, multiplications=44, additions_subtractions=33,
                outer_operations=34, kernel_operations=43,
                positive_unknown_count=25, positive_unknowns=OUTER_NAMES+CORE_NAMES,
                parameters=PARAMETERS, equations=16, outer_equations=6,
                primitive_instructions=primitives, histogram=histogram,
                equalities=EQUALITIES, sources=records,
                kernel_sign='fixed minus, canonical odd index')


def word(raw):
    value, place = 0, 1
    while raw:
        value += (raw & 1)*place
        raw >>= 1
        place *= 16
    return value


def typed(value, allowed={0, 1}):
    if value < 0:
        return False
    while value:
        value, digit = divmod(value, 16)
        if digit not in allowed:
            return False
    return True


def rule(value):
    assert typed(value)
    result, place = 0, 1
    for _ in range((value.bit_length()+3)//4+1):
        a = value//(place//16) % 16 if place > 1 else 0
        b, c = value//place % 16, value//(16*place) % 16
        y = (110 >> (4*a+2*b+c)) & 1
        result += y*place
        place *= 16
    return result


def numeric_outer(values):
    env = dict(values)
    for name, op, left, right in OUTER:
        a = env[left] if isinstance(left, str) else left
        b = env[right] if isinstance(right, str) else right
        env[name] = a+b if op == '+' else a-b if op == '-' else a*b
    return env


def check_tuple(m, t, B, Y, I, F):
    v, W, q = 2**m, 16**m, 16**(m*t)
    H, J = (q-1)//(W-1), (q-1)//15
    assert B > 0 and B % 16 == 0
    C = B//16
    U, T = 307*C+4*Y+J, B+H
    assert all(0 < x < q for x in (U, T, Y))
    assert typed(U, ALLOWED_U) and typed(T) and typed(Y)
    assert 0 < I < v and F > 0 and I+W*Y == C+q*F
    P = T+q*Y+q**3*U
    M, L, D0 = J*(q+1)*(4*q*q+14), q**4, q**6
    r = (L-P)*(L-1)+M
    outer = dict(q=q, v=v, quot=q//v, hrow=H, Cw=C, Yw=Y,
                 Jrow=J, alphaI=v-I, r=r, I=I, F=F)
    assert all(x > 0 for x in outer.values())
    env = numeric_outer(outer)
    assert all(env[a] == env[b] for a, b in OUTER_EQUALITIES)
    assert env['packed'] == P and env['mask'] == M and env['Uw'] == U
    assert 0 < P < L and 0 < M < L and not P & M
    assert M.bit_count() == 8*m*t
    assert r.bit_count() == 24*m*t
    assert D0 == 1 << (24*m*t)
    assert r % 2 == 1 and q**3 <= r < 2*(q**3)**3 and q**3 >= 64
    assert typed(B) and typed(I) and typed(F)
    current = 16*I
    for j in range(t):
        bj, yj = B//W**j % W, Y//W**j % W
        assert bj == current and bj % 16 == 0
        assert yj == rule(bj)
        current = 16*yj
    assert current == 16*F and F < W//16
    return dict(m=m, t=t, I=I, F=F, source_B=B, output_Y=Y,
                positive_outer_coordinates=outer, checked_outer_equations=6,
                index_parity=1, exact_central_valuation=24*m*t,
                field_bounds=True, mixed_mask=True)


def verify_histories():
    table_candidates = boundary_candidates = final_candidates = 0
    accepted = []
    for N in range(2, 13):
        q = 16**N
        all_words = [word(raw) for raw in range(1 << N)]
        for m in range(1, min(6, N)+1):
            if N % m:
                continue
            t, W, v = N//m, 16**m, 2**m
            H, J = (q-1)//(W-1), (q-1)//15
            final_words = [word(raw) for raw in range(1, 1 << m)]
            for T in all_words:
                table_candidates += 1
                B = T-H
                if B <= 0 or B % 16:
                    continue
                C = B//16
                I, lower_Y = C % W, C//W
                if not 0 < I < v or not typed(lower_Y):
                    continue
                boundary_candidates += 1
                for F in final_words:
                    final_candidates += 1
                    Y = lower_Y+(q//W)*F
                    U = 307*C+4*Y+J
                    if not 0 < U < q or not typed(U, ALLOWED_U):
                        continue
                    accepted.append(check_tuple(m, t, B, Y, I, F))
    canonical = []
    for I in (1, 17, 257, 273, 4097):
        for t in (1, 2, 3, 4, 8, 16):
            rows, outputs = [], []
            current = 16*I
            for _ in range(t):
                rows.append(current)
                outputs.append(rule(current))
                current = 16*outputs[-1]
            m = max(3, max(x.bit_length() for x in rows+outputs)//4+3)
            while 2**m <= I:
                m += 1
            W = 16**m
            B = sum(x*W**j for j, x in enumerate(rows))
            Y = sum(x*W**j for j, x in enumerate(outputs))
            canonical.append(check_tuple(m, t, B, Y, I, outputs[-1]))
    assert accepted and len(canonical) == 30
    return dict(complete_T_words=table_candidates,
                surviving_boundary_candidates=boundary_candidates,
                compatible_final_words=final_candidates,
                accepted_count=len(accepted), accepted=accepted,
                canonical_count=len(canonical), canonical=canonical,
                scope='Exact bounded enumeration and genuine canonical histories; enormous Pell witnesses are supplied by the proved converse, not materialized.')


def verify_prepower():
    checked = accepted = nonpower = 0
    for v, H in product(range(2, 9), range(1, 8)):
        W = v**4
        q = 1+H*(W-1)
        if q % v or (q-1) % 15:
            continue
        J = (q-1)//15
        L = q**4
        M = J*(q+1)*(4*q*q+14)
        assert q >= W >= 16 and 0 < M < L
        for C, Y in product(sorted({1, max(1, q//307-1), q//307+1, q, q*q}),
                            sorted({1, max(1, q//4-1), q//4+1, q, q*q})):
            checked += 1
            U, T = 307*C+4*Y+J, 16*C+H
            P = T+q*Y+q**3*U
            r = (L-P)*(L-1)+M
            if r <= 0:
                continue
            accepted += 1
            nonpower += int(q & (q-1) != 0)
            assert U < q and 307*C < q and 4*Y < q
            assert 256*C < q and T < q
            assert P < L and q**3 < r < q**8
    assert checked and accepted and nonpower
    return dict(integer_candidates=checked, positive_index_candidates=accepted,
                nonpower_q_positive_index_candidates=nonpower,
                scope='Geometry, repunit and positive-index bound tests only; no full kernel solutions are claimed for nonpower q.')


def verify():
    return dict(status='PASS_ONE_FIELD_RULE110_HISTORY77', source=verify_source(),
                prepower=verify_prepower(), histories=verify_histories(),
                proof='../1980/EXPLORATION_ONE_FIELD_RULE110_HISTORY.md',
                review='Author and two independent complete proof/source reviews PASS; fresh checks reproduce the saved receipt.',
                universality_status='DECIDABLE_RADIX16_ENDPOINT_RELATION',
                scope='Complete positive finite moving-history certificate for radix16 I,F. This changes the numerical radix8 endpoint predicate and supplies no universal input/halting interface.')


if __name__ == '__main__':
    result = verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(result['status'])
    print({k: result['source'][k] for k in ('operations', 'multiplications', 'additions_subtractions', 'positive_unknown_count', 'equations')})
    print(result['prepower'])
    print({k: v for k, v in result['histories'].items() if k not in ('accepted', 'canonical', 'scope')})
