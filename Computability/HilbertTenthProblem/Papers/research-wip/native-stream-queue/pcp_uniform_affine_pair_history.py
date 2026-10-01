"""Complete positive-duration affine-pair histories for a fixed tile table.

All selection, range, duration, and radix interfaces are paid.  Finite outer
fixtures deliberately do not claim to instantiate astronomical Pell witnesses.
"""
import argparse
from collections import Counter
from itertools import product
import json
from pathlib import Path
import random

import sympy as sp
import native_binary_masked_selection63 as native

execute = native.parent.execute
PARAMETERS = ['Vinitial', 'Ufinal', 'Vfinal']
DEFAULT_MAPS = ((4, 1, 2, 1), (2, 0, 4, 2), (8, 3, 2, 0))


class DAG:
    """Literal paid arithmetic, with exact structural sharing and 0/1 aliases."""
    def __init__(self):
        self.source = []
        self.cache = {}
        self.powers = {0: 1}
        self.repunits = {}

    def op(self, op, a, b, tag='v'):
        if isinstance(a, int) and isinstance(b, int):
            return a*b if op == '*' else a+b if op == '+' else a-b
        if op == '*':
            if a == 0 or b == 0: return 0
            if a == 1: return b
            if b == 1: return a
        if op == '+':
            if a == 0: return b
            if b == 0: return a
        if op == '-' and b == 0: return a
        if op in ('*', '+') and repr(a) > repr(b): a, b = b, a
        key = (op, a, b)
        if key in self.cache: return self.cache[key]
        name = f'{tag}__{len(self.source)}'
        self.source.append((name, op, a, b))
        self.cache[key] = name
        return name

    def add(self, a, b, tag='sum'): return self.op('+', a, b, tag)
    def sub(self, a, b, tag='difference'): return self.op('-', a, b, tag)
    def mul(self, a, b, tag='product'): return self.op('*', a, b, tag)

    def total(self, values, tag='sum'):
        out = 0
        for value in values: out = self.add(out, value, tag)
        return out

    def power(self, exponent):
        if exponent not in self.powers:
            half = self.power(exponent//2)
            result = self.mul(half, half, f'P{exponent-exponent%2}')
            if exponent % 2: result = self.mul(result, self.powers[1], f'P{exponent}')
            self.powers[exponent] = result
        return self.powers[exponent]

    def repunit(self, length, stride=1):
        key = (length, stride)
        if key not in self.repunits:
            if length == 0: out = 0
            elif length == 1: out = 1
            else:
                half = length//2
                out = self.mul(self.repunit(half, stride),
                               self.add(1, self.power(half*stride), 'repunit_factor'),
                               'repunit_product')
                if length % 2: out = self.add(out, self.power((length-1)*stride), 'repunit_tail')
            self.repunits[key] = out
        return self.repunits[key]

    def pack(self, values, stride=1):
        out = values[-1]
        for value in reversed(values[:-1]):
            out = self.add(value, self.mul(self.power(stride), out, 'pack_product'), 'pack_sum')
        return out

    def hatpack(self, values, stride=1):
        return self.sub(self.pack(values, stride), self.repunit(len(values), stride), 'unhat_pack')


def maps_from_tiles(tiles, width):
    assert isinstance(width, int) and width >= 1
    maps = []
    for top, bottom in tiles:
        assert top and bottom, 'each tile word must be nonempty'
        def value(word):
            result = 0
            for digit in word:
                assert isinstance(digit, int) and 0 <= digit < 1 << width
                result = (result << width)+digit
            return result
        maps.append((1 << (width*len(top)), value(top),
                     1 << (width*len(bottom)), value(bottom)))
    return tuple(maps)


def build_from_tiles(tiles, width, layout='auto'):
    return build(maps_from_tiles(tiles, width), layout)


def validate_maps(maps):
    maps = tuple(tuple(row) for row in maps)
    assert maps, 'the fixed table must contain at least one tile'
    for row in maps:
        assert len(row) == 4 and all(isinstance(v, int) for v in row)
        a, c, b, d = row
        assert a >= 1 and b >= 1 and c >= 0 and d >= 0
    return maps


def build(maps=DEFAULT_MAPS, layout='auto'):
    maps = validate_maps(maps)
    if layout == 'auto':
        candidates = [build(maps, name) for name in ('contiguous', 'interleaved')]
        chosen = min(candidates, key=lambda p: (p['operations'], p['scale_exponent'], p['multiplications']))
        return dict(chosen, requested_layout='auto', candidate_ledgers=[ledger(p) for p in candidates])
    assert layout in ('contiguous', 'interleaved')
    s = len(maps)
    threshold = max(8, s+4, 1+max(max(a+c, b+d) for a, c, b, d in maps))
    K = 1 << (threshold-1).bit_length()
    g = DAG()
    D = g.total(PARAMETERS+['height_slack'], 'height_sum')
    B = g.mul(K, D, 'B')
    J = g.sub(g.total([f'Shat{i}' for i in range(s)], 'selector_sum'), s, 'J')
    Bm1 = g.sub(B, 1, 'Bm1')
    P = g.add(g.mul(Bm1, J, 'P_product'), 1, 'P')
    g.powers[1] = P
    Hsum = g.add('H_U', 'H_V', 'history_sum')
    Zsum = g.total([f'{tag}hat{i}' for tag in ('ZU', 'ZV') for i in range(s)], 'selected_sum')
    global_lhs = g.add(g.add(Hsum, Zsum, 'global_sum'), 'global_bound', 'global_lhs')
    pairs = [(global_lhs, P)]

    # Two exact transports; signed decoded values are polynomial expressions.
    next_values = []
    for tag, ai, ci in (('U', 0, 1), ('V', 2, 3)):
        terms = []
        constant = 0
        for i, row in enumerate(maps):
            terms += [g.mul(row[ai], f'Z{tag}hat{i}', f'{tag}_slope'),
                      g.mul(row[ci], f'Shat{i}', f'{tag}_offset')]
            constant += row[ai]+row[ci]
        next_values.append(g.sub(g.total(terms, f'{tag}_next_sum'), constant, f'{tag}_next'))
    leftU = g.add(g.mul(B, next_values[0], 'U_update'), 1, 'U_lhs')
    leftV = g.add(g.mul(B, next_values[1], 'V_update'), 'Vinitial', 'V_lhs')
    rightU = g.add('H_U', g.mul(P, 'Ufinal', 'U_terminal'), 'U_rhs')
    rightV = g.add('H_V', g.mul(P, 'Vfinal', 'V_terminal'), 'V_rhs')
    pairs += [(leftU, rightU), (leftV, rightV)]

    stride = 1 if layout == 'contiguous' else 2
    R = g.repunit(s, stride)
    S = g.hatpack([f'Shat{i}' for i in range(s)], stride)
    Mc = g.mul(J, R, 'controller_mask')
    T = g.add('H_U', g.mul(P, 'H_V', 'range_second_history'), 'range_histories')
    if layout == 'contiguous':
        Tsel = g.add('H_U', g.mul(g.power(s), 'H_V', 'selected_second_history'), 'selected_histories')
        duplicate = g.add(1, g.power(s), 'selector_duplicate')
        zlist = [f'ZUhat{i}' for i in range(s)]+[f'ZVhat{i}' for i in range(s)]
        control_width = s
    else:
        Tsel = T
        duplicate = g.add(1, P, 'selector_duplicate')
        zlist = [f'{tag}hat{i}' for i in range(s) for tag in ('ZU', 'ZV')]
        control_width = 2*s
    Hb = g.mul(Tsel, R, 'history_batch')
    Mb = g.mul(g.mul(Bm1, duplicate, 'cell_mask_duplicate'), S, 'mask_batch')
    Zb = g.hatpack(zlist)
    RM = g.mul(g.mul(g.sub(D, 1, 'range_cell'), J, 'range_repunit'),
               g.add(1, P, 'range_duplicate'), 'range_mask')
    ec, er, et, N = 2*s, 2*s+control_width, 2*s+control_width+2, 2*s+control_width+4
    C = g.mul(g.power(ec), S, 'controller_region')
    Rregion = g.mul(g.power(er), T, 'range_region')
    common = g.add(C, Rregion, 'common_joined')
    H = g.total([Hb, common, g.mul(g.power(et), B, 'top_history')], 'joined_H')
    M = g.total([Mb, g.mul(g.power(ec), Mc, 'controller_mask_region'),
                 g.mul(g.power(er), RM, 'range_mask_region'),
                 g.mul(g.power(et), Bm1, 'top_mask')], 'joined_M')
    Z = g.add(Zb, common, 'joined_Z')
    scale = g.power(N)
    wrapper = list(g.source)
    aliases = dict(P=scale, Hhat=H, Mhat=M, Zhat=Z)
    raw_source, raw_pairs, _ = native.source('and64_prescribed')
    def alias(value):
        if isinstance(value, int): return value
        return aliases.get(value, 'and__'+value)
    kernel = []
    for name, op, a, b in raw_source:
        if name in ('padded_A', 'padded_B', 'F3'):
            op, b = '+', {'padded_A': 12, 'padded_B': 10, 'F3': 8}[name]
        kernel.append(('and__'+name, op, alias(a), alias(b)))
    source = wrapper+kernel
    pairs += [(alias(a), alias(b)) for a, b in raw_pairs]
    native_aux = native.domains('and64_prescribed')[1]
    aux = ['height_slack', 'H_U', 'H_V', 'global_bound']
    aux += [f'Shat{i}' for i in range(s)]
    aux += [f'{tag}hat{i}' for tag in ('ZU', 'ZV') for i in range(s)]
    aux += ['and__'+name for name in native_aux]
    counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    assert len(kernel) == 64 and len(aux) == 3*s+26 and len(pairs) == 19
    names = set(PARAMETERS+aux)
    for name, _, a, b in source:
        assert name not in names and all(not isinstance(v, str) or v in names for v in (a, b))
        names.add(name)
    return dict(maps=maps, layout=layout, requested_layout=layout, tiles=s, K=K,
                scale_exponent=N, control_width=control_width, source=source,
                comparisons=pairs, parameters=list(PARAMETERS), auxiliaries=aux,
                operations=len(source), multiplications=counts['M'], additions_subtractions=counts['A'],
                equations=19, witnesses=len(aux), positive_witnesses=len(aux),
                exact_degree=24*N+16, wrapper_operations=len(wrapper),
                interfaces=dict(D=D, B=B, J=J, P=P, R=R, S=S, Mc=Mc, T=T,
                                Hb=Hb, Mb=Mb, Zb=Zb, RM=RM, H=H, M=M, Z=Z,
                                scale=scale, nextU=next_values[0], nextV=next_values[1]),
                region_exponents=dict(controller=ec, range=er, top=et),
                native_prefix='and__', native_auxiliaries=native_aux)


def ledger(packet):
    keys = ('layout', 'tiles', 'K', 'scale_exponent', 'operations', 'multiplications',
            'additions_subtractions', 'equations', 'witnesses', 'exact_degree', 'wrapper_operations')
    result = {key: packet[key] for key in keys}
    result['polynomial'] = dict(operations=packet['operations']+56,
                                multiplications=packet['multiplications']+19,
                                additions_subtractions=packet['additions_subtractions']+37,
                                exact_degree=packet['exact_degree'])
    return result


def polynomial_source(packet):
    return native.parent.sos_source(packet['source'], packet['comparisons'])


def scalar(value, env): return env[value] if isinstance(value, str) else value


def manual(packet, v):
    maps, s, K = packet['maps'], packet['tiles'], packet['K']
    D = sum(v[n] for n in PARAMETERS)+v['height_slack']
    B = K*D
    Slist = [v[f'Shat{i}']-1 for i in range(s)]
    Zu = [v[f'ZUhat{i}']-1 for i in range(s)]
    Zv = [v[f'ZVhat{i}']-1 for i in range(s)]
    J = sum(Slist); P = (B-1)*J+1
    stride = 1 if packet['layout'] == 'contiguous' else 2
    R = sum(P**(stride*i) for i in range(s))
    S = sum(Slist[i]*P**(stride*i) for i in range(s))
    T = v['H_U']+P*v['H_V']
    if stride == 1:
        Hb = (v['H_U']+P**s*v['H_V'])*R
        Mb = (B-1)*(1+P**s)*S
        Zb = sum(Zu[i]*P**i+Zv[i]*P**(s+i) for i in range(s))
    else:
        Hb = T*R; Mb = (B-1)*(1+P)*S
        Zb = sum((Zu[i]+P*Zv[i])*P**(2*i) for i in range(s))
    ec, er, et = [packet['region_exponents'][key] for key in ('controller', 'range', 'top')]
    Mc = J*R; RM = (D-1)*J*(1+P)
    H = Hb+P**ec*S+P**er*T+P**et*B
    M = Mb+P**ec*Mc+P**er*RM+P**et*(B-1)
    Z = Zb+P**ec*S+P**er*T
    scale = P**packet['scale_exponent']
    nextU = sum(a*Zu[i]+c*Slist[i] for i, (a,c,b,d) in enumerate(maps))
    nextV = sum(b*Zv[i]+d*Slist[i] for i, (a,c,b,d) in enumerate(maps))
    residuals = [v['H_U']+v['H_V']+sum(Zu)+sum(Zv)+2*s+v['global_bound']-P,
                 B*nextU+1-v['H_U']-P*v['Ufinal'],
                 B*nextV+v['Vinitial']-v['H_V']-P*v['Vfinal']]
    raw = {name: v['and__'+name] for name in packet['native_auxiliaries']}
    raw.update(P=scale, Hhat=H+1, Mhat=M+1, Zhat=Z+1)
    old, pairs, _ = native.source('and64_prescribed')
    env = execute(old, raw)
    residuals += [scalar(a, env)-scalar(b, env) for a,b in pairs]
    return residuals, dict(D=D,B=B,J=J,P=P,R=R,S=S,Mc=Mc,T=T,Hb=Hb,Mb=Mb,Zb=Zb,
                           RM=RM,H=H,M=M,Z=Z,scale=scale,nextU=nextU,nextV=nextV)


def positive_outer_fixture(packet, selection, Vinitial=1):
    """Genuine path plus scalar truth fields, with core placeholders, not Pell zeros."""
    assert selection and Vinitial > 0
    maps, s = packet['maps'], packet['tiles']
    U, V = 1, Vinitial
    hu, hv = [], []
    for tile in selection:
        assert 0 <= tile < s
        hu.append(U); hv.append(V)
        a,c,b,d = maps[tile]
        U, V = a*U+c, b*V+d
    total = Vinitial+U+V
    D = 1 << total.bit_length()
    B = packet['K']*D; t = len(selection); P = B**t
    pack = lambda row: sum(value*B**j for j,value in enumerate(row))
    H_U, H_V = pack(hu), pack(hv)
    v = dict(Vinitial=Vinitial,Ufinal=U,Vfinal=V,height_slack=D-total,H_U=H_U,H_V=H_V)
    ztotal = 0
    for i in range(s):
        bits = [int(tile == i) for tile in selection]
        su = pack([bit*x for bit,x in zip(bits,hu)])
        sv = pack([bit*x for bit,x in zip(bits,hv)])
        v.update({f'Shat{i}':pack(bits)+1,f'ZUhat{i}':su+1,f'ZVhat{i}':sv+1})
        ztotal += su+sv+2
    v['global_bound'] = P-H_U-H_V-ztotal
    v.update({'and__'+name:1 for name in packet['native_auxiliaries']})
    _, face = manual(packet, v)
    assert face['P'] == P and face['H'] & face['M'] == face['Z']
    fields = native.parent.truth_fields(face['scale'], face['H'], face['M'])
    v.update({f'and__F{i}':fields[i] for i in range(3)})
    assert all(value > 0 for value in v.values())
    env = execute(packet['source'], v)
    assert all(scalar(a,env) == scalar(b,env) for a,b in packet['comparisons'][:3])
    assert env['and__F3'] == fields[3]
    for index in (1,14,15):
        a,b = packet['comparisons'][3+index]
        assert scalar(a,env) == scalar(b,env)
    return v


def degree_check(packet):
    """Exact residual univariates; the degree audit never expands the final SOS."""
    t = sp.Symbol('t')
    variables = packet['parameters']+packet['auxiliaries']
    weights = {name:1+i%5 for i,name in enumerate(variables)}
    inputs = {name:sp.Poly(weights[name]*t+i+2,t) for i,name in enumerate(variables)}
    env = execute(packet['source'], inputs)
    degrees, tops = [], []
    for a,b in packet['comparisons']:
        value = sp.Poly(scalar(a,env)-scalar(b,env), t)
        degrees.append(value.degree()); tops.append(value.LC())
    top_index = 3+4
    N = packet['scale_exponent']
    expected_degree = 12*N+8
    assert degrees[top_index] == expected_degree
    assert all(degree < expected_degree for i,degree in enumerate(degrees) if i != top_index)
    qtop = sp.Poly(env['and__q'],t).LC()
    expected_top = weights['and__w']**2*weights['and__s']**4*weights['and__k']**2*qtop**6
    assert tops[top_index] == expected_top
    return dict(layout=packet['layout'],tiles=packet['tiles'],scale_exponent=N,
                residual_degrees=degrees,unique_highest_residual=top_index,
                exact_polynomial_degree=2*expected_degree,leading_coefficient=str(expected_top**2))


def verify():
    rng = random.Random(20261001)
    tables = [((1,0,1,0),),((2,1,4,0),),DEFAULT_MAPS,
              ((4,1,2,1),(2,0,4,2)),tuple((2, i,4,i%3) for i in range(5)),
              tuple((4,i%4,8,i%8) for i in range(8)),
              ((3,2,5,1),(1,4,7,0))]
    ledgers=[]; signed=positive=outer=t1=zero_selected=0
    example = None
    for maps in tables:
        choices=[]
        for layout in ('contiguous','interleaved'):
            packet=build(maps,layout);choices.append(packet);ledgers.append(ledger(packet))
            sos,out=polynomial_source(packet)
            counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in sos)
            assert len(sos)==packet['operations']+56
            assert counts==dict(M=packet['multiplications']+19,A=packet['additions_subtractions']+37)
            for case in range(64):
                values={name:rng.randrange(1,6) if case<48 else rng.randrange(-3,4)
                        for name in packet['parameters']+packet['auxiliaries']}
                residuals,face=manual(packet,values);env=execute(sos,values)
                assert residuals==[scalar(a,env)-scalar(b,env) for a,b in packet['comparisons']]
                assert all(scalar(packet['interfaces'][name],env)==value for name,value in face.items())
                assert env[out]==sum(v*v for v in residuals)
                if case<48:
                    assert face['P']>=1 and face['D']>=4 and face['J']>=0
                    assert min(face[name] for name in ('H','M','Z'))>=0
                    positive+=1
                else:signed+=1
            for case in range(32):
                selection=tuple(rng.randrange(len(maps)) for _ in range(1+case%5))
                values=positive_outer_fixture(packet,selection,1+case%4)
                outer+=1;t1+=len(selection)==1
                zero_selected+=any(values[f'ZUhat{i}']==1 for i in range(len(maps)))
            if maps==DEFAULT_MAPS and layout=='contiguous':example=packet
        chosen=build(maps)
        assert chosen['operations']==min(p['operations'] for p in choices)
    assert maps_from_tiles((((1,2),(3,)),),2)==((16,6,4,3),)
    degree_audits=[degree_check(build(maps,layout)) for maps in tables[:3]
                  for layout in ('contiguous','interleaved')]
    return dict(status='PASS_PCP_UNIFORM_AFFINE_PAIR_HISTORY',
                exact_projection='Existence of a nonempty common tile word taking (1,Vinitial) '
                                 'to (Ufinal,Vfinal); all three parameters and all witnesses positive.',
                ledgers=ledgers,example=dict(ledger=ledger(example),parameters=example['parameters'],
                    auxiliaries=example['auxiliaries'],source=example['source'],
                    comparisons=example['comparisons'],interfaces=example['interfaces']),
                checks=dict(arbitrary_positive_full_residual_and_SOS=positive,
                            arbitrary_signed_full_residual_and_SOS=signed,
                            genuine_outer_paths=outer,duration_one=t1,
                            paths_with_unused_tile=zero_selected,
                            full_Pell_witnesses_materialized=False),
                degree_audits=degree_audits,
                scope='Complete uniform fixed-table certificate. No instantiated universal PCP table '
                      'or new numerical universal arithmetic bound is asserted.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
