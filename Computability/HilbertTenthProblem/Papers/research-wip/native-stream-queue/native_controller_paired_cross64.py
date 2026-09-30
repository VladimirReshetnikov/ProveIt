"""Complementary-lane paired FIFO64, centered69/general71 carry and even alignment."""
import argparse
from collections import Counter
from itertools import product
import json
from pathlib import Path
import sympy as sp
import input_bridge_boolean_ternary60 as boolean
import native_boolean_pair_fifo63 as paired

FILTER = [('cx_X_bound', '+', 'r', 'bound_beta'),
          ('cx_H', '+', 'F0', 'F3'), ('cx_twiceH', '+', 'cx_H', 'cx_H'),
          ('cx_repunit', '+', 'cx_twiceH', 1),
          ('cx_other', '+', 'F1', 'F2'), ('cx_other_bound', '+', 'cx_other', 'alpha')]
FIFO = [('cx_input', '*', 2, 'x'), ('cx_initial_sum', '+', 'init0', 'init1'),
        ('cx_tail0', '*', 'W', 'F0'), ('cx_transport0', '+', 'init0', 'cx_tail0'),
        ('cx_tail1', '*', 'W', 'F1'), ('cx_transport1', '+', 'init1', 'cx_tail1'),
        ('cx_width', '+', 'cx_input', 'width_beta'), ('cx_divisor', '*', 'W', 'L')]
CONTROL = [('cx_g0', '*', 'g0', 'F1'), ('cx_g1', '*', 'g1', 'F2'),
           ('cx_g2', '*', 'g2', 'F3'), ('cx_g01', '+', 'cx_g0', 'cx_g1'),
           ('cx_gsum', '+', 'cx_g01', 'cx_g2')]
GENERAL = [('cx_offset', '*', 'offset', 'cx_H'), ('cx_general', '+', 'cx_gsum', 'cx_offset')]
EVEN = [('cx_time_square', '*', 'time_root', 'time_root'),
        ('cx_width_square', '*', 'width_root', 'width_root')]
PARAMETERS = ['q', 'F0', 'F1', 'F2', 'F3', 'x', 'W']


def independent_sources(z, mode='bare', aligned=False):
    result = boolean.independent_sources(z, False)[:12]
    result += [2*(z['F0']+z['F3'])+1-z['q'], z['F1']+z['F2']+z['alpha']-z['q'],
               z['init0']+z['init1']-2*z['x'],
               z['F2']-z['init0']-z['W']*z['F0'],
               z['F3']-z['init1']-z['W']*z['F1'],
               2*z['x']+z['width_beta']-z['W'], z['W']*z['L']-z['q']]
    if mode != 'bare':
        p = z['g0']*z['F1']+z['g1']*z['F2']+z['g2']*z['F3']-z['gap']
        if mode == 'general':
            p += z['offset']*(z['F0']+z['F3'])
        result += [p]
    if aligned:
        result += [z['time_root']**2-z['q'], z['width_root']**2-z['W']]
    return result


def source_check(mode='bare', aligned=False):
    assert mode in ('bare', 'centered', 'general')
    auxiliaries = boolean.prior.CORE_NAMES+['bound_beta', 'alpha', 'width_beta', 'L', 'init0', 'init1']
    if aligned:
        auxiliaries += ['time_root', 'width_root']
    fixed = [] if mode == 'bare' else ['g0', 'g1', 'g2', 'gap']+(['offset'] if mode == 'general' else [])
    z = {name: sp.Symbol(name) for name in PARAMETERS+auxiliaries+fixed}
    schedule = boolean.PACK+boolean.CORE+FILTER+FIFO
    equalities = [('r', 'bt_packed')]+boolean.prior.kernel.EQUALITIES[1:]+[
        ('cx_X_bound', 'wn2'), ('cx_repunit', 'q'), ('cx_other_bound', 'q'),
        ('cx_initial_sum', 'cx_input'), ('F2', 'cx_transport0'), ('F3', 'cx_transport1'),
        ('cx_width', 'W'), ('cx_divisor', 'q')]
    if mode != 'bare':
        schedule += CONTROL
        if mode == 'general':
            schedule += GENERAL
        equalities += [('cx_general' if mode == 'general' else 'cx_gsum', 'gap')]
    if aligned:
        schedule += EVEN
        equalities += [('cx_time_square', 'q'), ('cx_width_square', 'W')]
    env = boolean.prior.execute(schedule, dict(z, n2=z['q']))
    sources = independent_sources(z, mode, aligned)
    u = 2*z['r']+1+z['j']*z['c']
    correction = sources[8]*(u*u-z['y_aux']**2)
    records = []
    for ix, ((left, right), p) in enumerate(zip(equalities, sources)):
        adjust = correction if ix == 9 else 0
        assert sp.expand(env[left]-env[right]-p-adjust) == 0, ix
        records.append(dict(equality=[left, right], source=str(sp.expand(p)), correction=str(sp.expand(adjust))))
    counts = Counter(row[1] for row in schedule)
    total = 64+(0 if mode == 'bare' else 5 if mode == 'centered' else 7)+2*aligned
    mult = 32+(0 if mode == 'bare' else 3 if mode == 'centered' else 4)+2*aligned
    assert len(schedule) == total and counts['*'] == mult
    assert counts['+']+counts['-'] == total-mult
    assert len(equalities) == len(sources) == 19+(mode != 'bare')+2*aligned
    assert len(PARAMETERS)+len(auxiliaries)-1 == 29+2*aligned
    assert set().union(*(p.free_symbols for p in sources)) == set(z.values())
    return dict(operations=total, multiplications=mult, additions_subtractions=total-mult,
                equations=len(equalities), positive_existentials_excluding_x=29+2*aligned,
                positive_parameters=PARAMETERS, positive_auxiliaries=auxiliaries,
                mode=mode, even_time_and_width=aligned, aliases={'n2': 'q'},
                fixed_constants=({} if mode == 'bare' else
                    dict(g0='v1', g1='u0', g2='u1-v0', gap='cf-cs',
                         offset=('h+v0-2cf' if mode == 'general' else '0; chosen condition h+v0=2cf'))),
                instructions=[list(row) for row in schedule], sources=records,
                scope='Exact complementary-lane filter a0+d1=1 with positive split ordinary input2x; no universal compiler')


def prepower():
    checked = 0
    for q in range(5, 32, 2):
        H = (q-1)//2
        for f0 in range(1, H):
            f3 = H-f0
            for f1 in range(1, q-1):
                for f2 in range(1, q-f1):
                    fields = [f0, f1, f2, f3]
                    r = boolean.pack(fields, q); X = q*(r//q+1); Y = 4
                    a = Y*(X+1); E = X*Y; P = 2*X*Y*Y+1
                    assert all(0 < F < q for F in fields)
                    assert q**3+q*q+q+1 <= r < q**4 and r >= 156
                    assert X > r and E > r+1 and a > 2*r+1 and P > a+3 and 6*X*Y*Y > a
                    checked += 1
    return dict(arbitrary_positive_pre_power_tuples=checked, minimum_q=5, minimum_r=156,
                no_joint_sum_bound_used=True)


def typing():
    rows = []
    for t in range(1, 5):
        q = 3**t; H = (q-1)//2; checked = admitted = beyond_old_joint = 0
        for f0 in range(1, H):
            f3 = H-f0
            for f1 in range(1, q-1):
                for f2 in range(1, q-f1):
                    fields = [f0, f1, f2, f3]; r = boolean.pack(fields, q)
                    arithmetic = r % 2 == 0 and boolean.prior.valuation(r) == 0
                    semantic = all(boolean.native_boolean(F, t) for F in fields) and sum(fields) % 2 == 0
                    assert arithmetic == semantic
                    if arithmetic:
                        assert all((f0//3**j % 3)+(f3//3**j % 3) == 1 for j in range(t))
                        admitted += 1; beyond_old_joint += sum(fields) >= q
                    checked += 1
        rows.append(dict(t=t, field_tuples=checked, admitted=admitted,
                         admitted_without_old_joint_bound=beyond_old_joint))
    return dict(domains=rows, field_tuples=sum(row['field_tuples'] for row in rows),
                admitted=sum(row['admitted'] for row in rows))


def semantic_checks():
    rows = []; example_without_joint = None
    for t in range(2, 6):
        q = 3**t; H = (q-1)//2
        values = [sum(bit*3**j for j, bit in enumerate(bits)) for bits in product((0, 1), repeat=t) if any(bits)]
        checked = admitted = 0
        for f0 in values:
            f3 = H-f0
            if f3 <= 0:
                continue
            for f1, f2 in product(values, repeat=2):
                fields = [f0, f1, f2, f3]
                assert f1+f2 < q
                for m in range(1, t+1):
                    W = 3**m; I0 = f2-W*f0; I1 = f3-W*f1
                    arithmetic = min(I0, I1) > 0 and (I0+I1) % 2 == 0 and I0+I1 < W
                    semantic = arithmetic and paired.direct_pair((I0, I1), fields, m, t)
                    assert arithmetic == semantic
                    if arithmetic:
                        assert all(paired.prior.native_boolean(I, m) for I in (I0, I1))
                        assert sum(fields) % 2 == 0 and t >= m+1
                        admitted += 1
                        if sum(fields) >= q and example_without_joint is None:
                            example_without_joint = dict(x=(I0+I1)//2, W=W, q=q, fields=fields, initials=[I0, I1])
                    checked += 1
        rows.append(dict(t=t, stream_width_tuples=checked, admitted=admitted))
    return dict(domains=rows, stream_width_tuples=sum(row['stream_width_tuples'] for row in rows),
                admitted=sum(row['admitted'] for row in rows),
                example_without_old_joint_bound=example_without_joint)


def positive_maps():
    examples = []
    for x in range(1, 201):
        I0, I1 = paired.positive_split(2*x)
        for aligned in (False, True):
            step = 2 if aligned else 1; m = step
            while 3**m <= 6*x:
                m += step
            W = 3**m; Hm = (W-1)//2; q = W*W; t = 2*m
            fields = [Hm-I1, Hm, I0+W*(Hm-I1), I1+W*Hm]
            assert all(boolean.native_boolean(F, t) for F in fields)
            assert fields[0]+fields[3] == (q-1)//2
            alpha = q-fields[1]-fields[2]
            assert alpha > 0 and W-2*x > 0 and sum(fields) % 2 == 0
            assert paired.direct_pair((I0, I1), fields, m, t)
            if aligned:
                assert (3**(m//2))**2 == W and W**2 == q
            if x in (1, 2, 10, 200):
                examples.append(dict(x=x, aligned=aligned, m=m, t=t, W=W, q=q, fields=fields,
                                     initials=[I0, I1], alpha=alpha, width_beta=W-2*x, L=W))
    return dict(ordinary_inputs=200, maps_per_input=2, examples=examples,
                full_kernel_extension='Fresh positive raw Boolean-kernel map proved; no old joint slack is assumed')


def controller_checks():
    F0, F1, F2, F3, H = sp.symbols('F0 F1 F2 F3 H')
    u0, u1, v0, v1, h, cs, cf = sp.symbols('u0 u1 v0 v1 h cs cf')
    original = cs+h*H+u0*F2+u1*F3+v0*F0+v1*F1-(2*H+1)*cf
    reduced = v1*F1+u0*F2+(u1-v0)*F3+(h+v0-2*cf)*H-cf+cs
    assert sp.expand(original.subs(F0, H-F3)-reduced) == 0
    labels = [(a0, a1, d0, d1) for a0, a1, d0, d1 in product((0, 1), repeat=4) if a0+d1 == 1]
    history_triples = set()
    for a0, a1, d0, d1 in labels:
        past, current, next_value = 1-d0, d1, a1
        assert (a0, a1) == (1-current, next_value)
        history_triples.add((past, current, next_value))
    assert history_triples == set(product((0, 1), repeat=3))
    tested = admitted = 0
    for u0, u1, v0, v1, h, cs, cf in ((2, 3, -2, 4, 2, 0, 0), (1, -2, 3, -1, 0, 1, -2), (0, 0, 0, 0, 0, 0, 0)):
        g0, g1, g2, offset = v1, u0, u1-v0, h+v0-2*cf
        for t in range(1, 5):
            q = 3**t; H = (q-1)//2
            for path in product(labels, repeat=t):
                fields = [sum(row[i]*3**j for j, row in enumerate(path)) for i in range(4)]
                equality = g0*fields[1]+g1*fields[2]+g2*fields[3]+offset*H == cf-cs
                carry = cs; integral = True
                for a0, a1, d0, d1 in path:
                    numerator = carry+h+u0*d0+u1*d1+v0*a0+v1*a1
                    if numerator % 3:
                        integral = False; break
                    carry = numerator//3
                assert equality == (integral and carry == cf)
                tested += 1; admitted += equality
    return dict(local_words_and_controller_tuples=tested, admitted=admitted,
                unrestricted_history_triples=len(history_triples),
                scope='Includes general nonzero offset and every allowed full label; not a selected subgraph')


def verify():
    sources = {}
    for mode, aligned in (('bare', False), ('centered', False), ('centered', True), ('general', False), ('general', True)):
        source = source_check(mode, aligned)
        sources[f'{mode}_{source["operations"]}'] = source
    return dict(status='PASS_COMPLEMENTARY_LANE_PAIRED64', sources=sources,
                prepower=prepower(), typing=typing(), semantics=semantic_checks(),
                positive_maps=positive_maps(), controllers=controller_checks(),
                scope='Exact changed filter and complete carry relations; universal input simulation and acceptance remain open',
                established_complete_universal_bound=76)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(); parser.add_argument('--write', action='store_true'); args = parser.parse_args()
    result = verify(); receipt = Path(__file__).with_suffix('.json')
    if args.write:
        receipt.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    else:
        assert json.loads(receipt.read_text()) == result, 'receipt mismatch'
    print(json.dumps({key: value for key, value in result.items() if key != 'sources'}, indent=2))
