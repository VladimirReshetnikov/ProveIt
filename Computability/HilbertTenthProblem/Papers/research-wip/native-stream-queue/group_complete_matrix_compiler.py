"""Compose four paid components into a complete fixed-table matrix compiler.

Only x is a runtime relation argument. All other supplied coordinates are
strictly positive existential witnesses; alpha, beta and the macro table
are fixed compiler data. No numerically instantiated universal table is
claimed. The finite positive fixtures test outer interfaces; the imported
parametric Pell converses supply their full positive core extensions.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import random

import sympy as sp

import group_four_register_canonical_history47 as history
import group_four_register_history as physical
import group_regular_macro_controller as control
import group_linked_binary_geometry47 as geometry
import native_binary_masked_selection63 as selection


GLOBAL_AUX = (['q_geom', 'P', 'J', 'history_bound']
              +[f'H{i}' for i in range(4)]
              +[f'Shat{i}' for i in range(8)]
              +[f'Zhat{i}' for i in range(8)])


def build(codes, alpha=24, beta=12):
    assert isinstance(alpha, int) and isinstance(beta, int)
    assert alpha > 0 and beta > 0
    edges = control.macro_table(codes)
    ctrl = control.build(edges)
    geom = geometry.build(shared_B=True)
    hs, hp = history.source()
    ss, sp, _ = selection.source('exclusive119_prescribed')
    spar, saux = selection.domains('exclusive119_prescribed')
    aliases = {
        'history': dict(x='x', alpha=alpha, beta=beta, q='q_geom',
                        P='P', B='B', D='D', history_bound='history_bound'),
        'selection': dict(P='P', B='B'),
        'controller': dict(P='P', B='B', J='J'),
        'geometry': dict(q='q_geom', B='B', J='J'),
    }
    for i in range(4):
        aliases['history'][f'H{i}'] = f'H{i}'
        aliases['selection'][f'history{i}'] = f'H{i}'
        for offset, sign in enumerate(('p', 'm')):
            aliases['history'][f'S{i}{sign}'] = f'Shat{2*i+offset}'
            aliases['history'][f'Z{i}{sign}'] = f'Zhat{2*i+offset}'
    for i in range(8):
        for tag in ('S', 'Z'):
            aliases['selection'][f'{tag}hat{i}'] = f'{tag}hat{i}'
        aliases['controller'][f'Shat{i}'] = f'Shat{i}'

    def renamed(tag, value):
        if isinstance(value, int):
            return value
        return aliases[tag].get(value, f'{tag}__{value}')

    source, pairs, blocks = [], [], []
    for tag, instructions, comparisons in (
        ('history', hs, hp), ('selection', ss, sp),
        ('controller', ctrl['source'], ctrl['comparisons']),
        ('geometry', geom['source'], geom['comparisons']),
    ):
        start, cstart = len(source), len(pairs)
        source += [(renamed(tag, n), op, renamed(tag, a), renamed(tag, b))
                   for n, op, a, b in instructions]
        pairs += [(renamed(tag, a), renamed(tag, b)) for a, b in comparisons]
        blocks.append(dict(name=tag, instruction_start=start,
                           instruction_count=len(instructions),
                           comparison_start=cstart, comparison_count=len(comparisons)))
    aux = list(GLOBAL_AUX)
    aux += [renamed('selection', name) for name in saux]
    aux += [renamed('controller', name) for name in ctrl['auxiliaries'] if name != 'J']
    aux += [renamed('geometry', name) for name in geom['auxiliaries']]
    assert len(aux) == len(set(aux))
    m, h, p = ctrl['m'], ctrl['h'], ctrl['projection_additions']
    counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    assert counts == {'M': 3*m+2*h+128, 'A': 4*m+h+p+145}
    assert len(source) == 7*m+3*h+p+273
    assert len(pairs) == 60 and len(aux) == m+87
    available = {'x', *aux}
    for name, op, left, right in source:
        assert name not in available and op in ('+', '-', '*')
        assert all(isinstance(value, int) or value in available for value in (left, right))
        available.add(name)
    assert all(isinstance(v, int) or v in available for pair in pairs for v in pair)
    return dict(codes=tuple(tuple(code) for code in codes), edges=edges,
                alpha=alpha, beta=beta, m=m, h=h, projection_additions=p,
                parameters=['x'], auxiliaries=aux, aliases=aliases, blocks=blocks,
                source=source, comparisons=pairs, operations=len(source),
                multiplications=counts['M'], additions_subtractions=counts['A'],
                equations=len(pairs), positive_witnesses=len(aux))


def execute(source, values):
    return control.execute(source, values)


def residuals(packet, env):
    return control.residuals(packet, env)


def polynomial_source(packet):
    return control.polynomial_source(packet)


def restored_inputs(packet, values, env, tag, names):
    result = {}
    for name in names:
        key = packet['aliases'][tag].get(name, f'{tag}__{name}')
        result[name] = key if isinstance(key, int) else env[key]
    return result


def independent_residuals(packet, values, env):
    q, P, B = values['q_geom'], values['P'], 8*values['q_geom']**2
    D, r = q*q, packet['alpha']*values['x']+packet['beta']
    starts, ends = (D+q, D+1)*2, (D+(1+r)*q+1, D-r*r*q+1-r)*2
    answer = []
    for i in range(4):
        dz = values[f'Zhat{2*i}']-values[f'Zhat{2*i+1}']
        ds = values[f'Shat{2*i}']-values[f'Shat{2*i+1}']
        H = values[f'H{i}']
        answer.append(B*(H+dz-D*ds)-H-ends[i]*P+starts[i])
    answer.append(sum(values[f'H{i}'] for i in range(4))+values['history_bound']-P)
    spar, saux = selection.domains('exclusive119_prescribed')
    z = restored_inputs(packet, values, env, 'selection', spar+saux)
    slots = (1, 1, 0, 0, 3, 3, 2, 2)
    Hb = sum(z[f'history{slots[i]}']*P**i for i in range(8))
    Mb = (B-1)*sum((z[f'Shat{i}']-1)*P**i for i in range(8))
    Zb = sum((z[f'Zhat{i}']-1)*P**i for i in range(8))
    raw = dict(z, q=16*P**8, F3=16*Zb+8)
    native = list(selection.parent.native.independent_sources(raw))
    root = z['j']*z['c']-(2*z['r']+1)
    native[12] += native[11]*(root*root-z['y_aux']**2)
    answer += native
    answer += [z['F1']+raw['F3']-16*Hb-12,
               z['F2']+raw['F3']-16*Mb-10,
               sum(z[f'Zhat{i}'] for i in range(8))+z['bound_global']-P-1]
    ctrl = control.build(packet['edges'])
    z = restored_inputs(packet, values, env, 'controller', ctrl['parameters']+ctrl['auxiliaries'])
    answer += control.manual_residuals(ctrl, z)
    geom = geometry.build(shared_B=True)
    z = restored_inputs(packet, values, env, 'geometry', geom['parameters']+geom['auxiliaries'])
    # The geometry module supplies its independently expanded original core.
    answer += geometry.manual(z, B)
    return answer


def source_checks():
    examples = [(), ((1,), (2,)), ((1, 3), (4, 2), (5, 7, 6, 8))]
    rng = random.Random(6087273)
    packets, cases, signed = [], 0, 0
    for codes in examples:
        packet = build(codes)
        sos, out = polynomial_source(packet)
        m, h, p = packet['m'], packet['h'], packet['projection_additions']
        counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in sos)
        assert len(sos) == 7*m+3*h+p+452
        assert counts == {'M':3*m+2*h+188, 'A':4*m+h+p+264}
        for case in range(256):
            z = {name:rng.randrange(1, 13) if case < 192 else rng.randrange(-5, 6)
                 for name in packet['parameters']+packet['auxiliaries']}
            env = execute(sos, z)
            expected = independent_residuals(packet, z, env)
            assert residuals(packet, env) == expected and len(expected) == 60
            assert env[out] == sum(value*value for value in expected)
            cases += 1
            signed += case >= 192
        packet['sum_of_squares'] = dict(operations=len(sos), multiplications=counts['M'],
                                       additions_subtractions=counts['A'], output=out)
        packets.append(packet)
    return dict(packets=packets, independent_full_residual_assignments=cases,
                signed_off_zero_assignments=signed,
                scope='All60 residuals and the complete SOS are evaluated; no finite full Pell zeros are inferred.')


def positive_outer_checks():
    """Common positive interface fixtures, with deliberately unfilled Pell cores."""
    code = physical.target_word(2)
    codes = (code, physical.inverse_word(code))
    packet = build(codes, alpha=1, beta=1)
    ctrl = control.build(packet['edges'])
    records = []
    for tokens in ((0,), (0, 1, 0)):
      for padding in (0, 2):
        indices = []
        for token in tokens:
            start = 1+sum(len(c) for c in codes[:token])
            indices.extend(range(start, start+len(codes[token])))
        indices += [0]*padding
        word = tuple(packet['edges'][i][2] for i in indices)
        assert control.action_path(packet['edges'], indices)
        t, q = len(word), 2**len(word)
        B, P = 8*q*q, (8*q*q)**t
        J = (P-1)//(B-1)
        assert B > packet['m'] and J > B and J.bit_count() == t
        current, rows = [q, 1, q, 1], []
        for label in word:
            rows.append([q*q+v for v in current])
            if label:
                target = (label-1)//2
                current[target] += (1 if label % 2 else -1)*current[target ^ 1]
        assert current == [3*q+1, -4*q-1]*2
        H = [sum(row[i]*B**j for j, row in enumerate(rows)) for i in range(4)]
        S = [sum((label == i+1)*B**j for j, label in enumerate(word)) for i in range(8)]
        Z = [sum((label == i+1)*rows[j][(i//2) ^ 1]*B**j
                 for j, label in enumerate(word)) for i in range(8)]
        z = {name:1 for name in packet['parameters']+packet['auxiliaries']}
        z.update(q_geom=q, P=P, J=J, history_bound=P-sum(H))
        z.update({f'H{i}':v for i, v in enumerate(H)})
        z.update({f'Shat{i}':v+1 for i, v in enumerate(S)})
        z.update({f'Zhat{i}':v+1 for i, v in enumerate(Z)})
        z['selection__bound_global'] = P-sum(Z)-7
        slots = (1, 1, 0, 0, 3, 3, 2, 2)
        Hb = sum(H[slots[i]]*P**i for i in range(8))
        Mb = (B-1)*sum(S[i]*P**i for i in range(8))
        Zb = sum(Z[i]*P**i for i in range(8))
        assert Hb & Mb == Zb
        fields = selection.parent.truth_fields(P**8, Hb, Mb)
        z.update({f'selection__F{i}':fields[i] for i in range(3)})
        cv = control.outer_fixture(ctrl, indices, B)
        for name in ctrl['auxiliaries']:
            if name != 'J':
                z[f'controller__{name}'] = cv[name]
        # Fill the geometry's three paid outer conditions; its full norm
        # coordinates exist parametrically and are not materialized here.
        z['geometry__s'] = 3
        z['geometry__w'] = J//q+1
        z['geometry__bound_beta'] = q*z['geometry__w']-J
        z['geometry__index_beta'] = J-B
        assert min(z.values()) > 0
        env = execute(packet['source'], z)
        rr = residuals(packet, env)
        assert rr[:5] == [0]*5
        assert rr[5+1] == 0 and rr[5+14:5+17] == [0]*3
        cstart = 22
        assert rr[cstart:cstart+3] == [0]*3
        assert rr[cstart+16:cstart+25] == [0]*9
        assert rr[-3:] == [0]*3
        assert env['selection__F3'] == fields[3]
        assert env['controller__q'] != q and env['selection__q'] != q
        assert physical.word_matrices(word) == (physical.target(2),)*2
        records.append(dict(duration=t, q_bits=q.bit_length(), P_bits=P.bit_length(),
                            J_population=J.bit_count(), table_edges=packet['m'],
                            every_supplied_coordinate_positive=True,
                            common_outer_comparisons_verified=True))
    return dict(fixtures=records,
                limitation='Full Pell core equalities are not asserted for placeholder coordinates. '
                           'Their positive extensions follow from the three independent core theorems.')


def degree_checks():
    records = []
    examples = [(), ((1,), (2,)), ((1, 3), (4, 2)),
                ((1, 3), (4, 2), (5, 7, 6, 8))]
    t = sp.Symbol('t')
    for codes in examples:
        packet = build(codes)
        degrees = {name:1 for name in packet['parameters']+packet['auxiliaries']}
        def deg(value):
            return 0 if isinstance(value, int) else degrees[value]
        for name, op, left, right in packet['source']:
            degrees[name] = deg(left)+deg(right) if op == '*' else max(deg(left), deg(right))
        upper = [max(deg(a), deg(b)) for a, b in packet['comparisons']]
        assert max(upper[:5]) <= 5
        assert max(upper[5:22]) == 56 and upper[9] == 56
        assert max(upper[22:47]) == 6*packet['m']+8 and upper[28] == 6*packet['m']+8
        assert max(upper[47:]) <= 14
        names = packet['parameters']+packet['auxiliaries']
        scales = {name:1+i % 3 for i, name in enumerate(names)}
        values = {name:sp.Poly(scales[name]*t+i+1, t) for i, name in enumerate(names)}
        sos, out = polynomial_source(packet)
        env = execute(sos, values)
        rr = [sp.Poly(value, t) for value in residuals(packet, env)]
        s = scales
        select_top = (s['selection__w']**2*s['selection__s']**4*s['selection__k']**2
                      *(16*s['P']**8)**6)
        ctrl_top = (s['controller__w']**2*s['controller__s']**4*s['controller__k']**2
                    *(8*s['J']*s['P']**(packet['m']-1))**6)
        assert rr[9].degree() == 56 and rr[9].LC() == select_top
        assert rr[28].degree() == 6*packet['m']+8 and rr[28].LC() == ctrl_top
        exact = max(112, 12*packet['m']+16)
        expected = (select_top**2 if exact == 112 else 0)
        expected += ctrl_top**2 if exact == 12*packet['m']+16 else 0
        assert env[out].degree() == exact and env[out].LC() == expected
        assert all(rr[i].degree() < exact//2 for i in range(60) if i not in (9, 28))
        records.append(dict(m=packet['m'], residual_degree_upper_bounds=upper,
                            exact_polynomial_degree=exact,
                            selector_first_norm_degree=56,
                            controller_first_norm_degree=6*packet['m']+8,
                            weighted_leading_coefficient=str(expected)))
    return dict(exact_degree='max(112,12m+16)', fixtures=records,
                argument='The actual DAG upper bounds are attained by the independent squared first-norm highest forms; m=8 has both contributions.')


def verify():
    return dict(status='PASS_GROUP_COMPLETE_MATRIX_COMPILER',
                arithmetic=source_checks(),
                positive_common_interfaces=positive_outer_checks(),
                exact_degree=degree_checks(),
                comparison_operations='7m+3h+p+273',
                polynomial_operations='7m+3h+p+452',
                positive_witnesses='m+87', equations=60,
                ordinary_input='x>0; r=alpha*x+beta with paid fixed-numeral prefix',
                scope='Complete for a supplied fixed macro table; the universal subgroup alphabet is not numerically instantiated.')


if __name__ == '__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write', action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result, indent=2)+'\n')
    else:assert json.loads(path.read_text())==result, 'receipt mismatch'
    print(result['status'])
