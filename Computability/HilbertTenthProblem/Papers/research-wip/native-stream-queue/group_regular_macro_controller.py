"""Paid regular macro control, conditional only on dyadic B and P.

The full positive Pell extension is imported from the binary three-field
theorem, not inferred from the finite fixtures here.
"""
import argparse
from collections import Counter
from itertools import product
import json
from pathlib import Path
import random

import native_binary_three_row_fifo58 as binary


def macro_table(codes):
    """Separate hub-to-hub paths; duplicate idle loops pad to 2**h edges."""
    edges = [(0, 0, 0)]
    states = 1
    for code in codes:
        assert code and all(1 <= letter <= 8 for letter in code)
        old = 0
        for index, letter in enumerate(code):
            new = 0 if index == len(code)-1 else states
            if new:
                states += 1
            edges.append((old, new, letter))
            old = new
    size = 2
    while size < len(edges):
        size *= 2
    edges += [(0, 0, 0)]*(size-len(edges))
    assert states <= size
    return tuple(edges)


def build(edges):
    m = len(edges)
    h = m.bit_length()-1
    assert m >= 2 and m == 1 << h
    assert all(0 <= s < m and 0 <= t < m and 0 <= a <= 8 for s,t,a in edges)
    parameters = ['B', 'P']+[f'Shat{i}' for i in range(8)]
    auxiliaries = ([f'edge_hat{i}' for i in range(m)]+['J', 'radix_beta', 'F0']
                   +binary.CORE_NAMES+['odd_half', 'bound_beta'])
    source = []

    def emit(name, op, left, right):
        source.append((name, op, left, right))
        return name

    def sum_terms(terms, prefix):
        if not terms:
            return 0
        value = terms[0]
        for index, term in enumerate(terms[1:], 1):
            value = emit(f'{prefix}{index}', '+', value, term)
        return value

    emit('cell_minus1', '-', 'B', 1)
    emit('geometry_product', '*', 'cell_minus1', 'J')
    emit('geometry_power', '+', 'geometry_product', 1)
    emit('radix_margin', '+', m, 'radix_beta')
    edge_sum = sum_terms([f'edge_hat{i}' for i in range(m)], 'edge_sum')
    emit('edge_checksum', '+', 'J', m)
    pairs = [('geometry_power', 'P'), ('radix_margin', 'B'),
             (edge_sum, 'edge_checksum')]

    powers = ['P']
    for index in range(1, h):
        powers.append(emit(f'lane_power{index}', '*', powers[-1], powers[-1]))
    factors = [emit(f'lane_factor{i}', '+', power, 1) for i,power in enumerate(powers)]
    repunit = factors[0]
    for index, factor in enumerate(factors[1:], 1):
        repunit = emit(f'lane_repunit{index}', '*', repunit, factor)
    value = f'edge_hat{m-1}'
    for index in range(m-2, -1, -1):
        mult = emit(f'edge_pack_mult{index}', '*', 'P', value)
        value = emit(f'edge_pack_sum{index}', '+', f'edge_hat{index}', mult)
    emit('edge_word', '-', value, repunit)
    emit('origin_mask', '*', 'J', repunit)
    emit('edge_word8', '*', 8, 'edge_word')
    emit('F2', '+', 'edge_word8', 4)
    emit('origin_mask8', '*', 8, 'origin_mask')
    emit('subset_gap8', '-', 'origin_mask8', 'edge_word8')
    emit('F1', '+', 'subset_gap8', 2)

    # Share 8*M: q=F0+F1+F2+1=F0+8*M+7 saves one checksum addition.
    checksum = binary.OUTER[4:7]
    assert checksum[-1] == ('bs_q', '+', 'bs_sum012', 1)
    emit('subset_scale0', '+', 'F0', 'origin_mask8')
    emit('q', '+', 'subset_scale0', 7)
    source += binary.OUTER[:4]+binary.OUTER[7:]
    source += [(name, op, 'q' if left == 'n2' else left,
                'q' if right == 'n2' else right) for name,op,left,right in binary.CORE]
    source += binary.BOUND
    pairs += [('r', 'bs_packed'), ('s', 'bs_odd'), ('bs_X_bound', 'wn2')]
    pairs += binary.prior.CORE_EQUALITIES

    # This literal dense schedule deliberately charges every fixed product,
    # including coefficients zero and one. It is an upper bound, not optimal.
    weighted = []
    for coordinate, tag in ((0, 'source'), (1, 'target')):
        terms = [emit(f'{tag}_weighted{i}', '*', edge[coordinate], f'edge_hat{i}')
                 for i,edge in enumerate(edges)]
        total = sum_terms(terms, tag+'_sum')
        weighted.append(emit(tag+'_word', '-', total, sum(e[coordinate] for e in edges)))
    emit('shifted_target', '*', 'B', weighted[1])
    pairs.append((weighted[0], 'shifted_target'))

    projection_additions = 0
    for label in range(1,9):
        terms = [f'edge_hat{i}' for i,e in enumerate(edges) if e[2] == label]
        if not terms:
            value = 1
        elif len(terms) == 1:
            value = terms[0]
        else:
            value = sum_terms(terms, f'port{label}_sum')
            value = emit(f'port{label}', '-', value, len(terms)-1)
            projection_additions += len(terms)
        pairs.append((value, f'Shat{label-1}'))
    counts = Counter('M' if op == '*' else 'A' for _,op,_,_ in source)
    expected = {'M':3*m+2*h+30, 'A':4*m+h+projection_additions+30}
    assert counts == expected
    assert len(pairs) == 25 and len(auxiliaries) == m+22
    return dict(m=m, h=h, edges=edges, parameters=parameters, auxiliaries=auxiliaries,
                source=source, comparisons=pairs, multiplications=counts['M'],
                additions_subtractions=counts['A'], operations=len(source),
                projection_additions=projection_additions)


def execute(source, values):
    env = dict(values)
    for name, op, left, right in source:
        assert name not in env, name
        left = env[left] if isinstance(left,str) else left
        right = env[right] if isinstance(right,str) else right
        env[name] = left*right if op == '*' else left+right if op == '+' else left-right
    return env


def residuals(packet, env):
    def get(value):
        return env[value] if isinstance(value,str) else value
    return [get(left)-get(right) for left,right in packet['comparisons']]


def polynomial_source(packet):
    source=list(packet['source'])
    for i,(left,right) in enumerate(packet['comparisons']):
        source += [(f'poly_res{i}','-',left,right),
                   (f'poly_square{i}','*',f'poly_res{i}',f'poly_res{i}')]
    value='poly_square0'
    for i in range(1,len(packet['comparisons'])):
        source.append((f'poly_sum{i}','+',value,f'poly_square{i}'))
        value=f'poly_sum{i}'
    return source,value


def manual_residuals(packet, z):
    edges=packet['edges'];m=packet['m'];B=z['B'];P=z['P'];J=z['J']
    E=[z[f'edge_hat{i}']-1 for i in range(m)]
    K=sum(P**i for i in range(m));H=sum(E[i]*P**i for i in range(m));M=J*K
    F0=z['F0'];F1=8*(M-H)+2;F2=8*H+4;q=F0+F1+F2+1
    a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,ga,y=(z[n] for n in binary.CORE_NAMES)
    X=w*q;Y=s*q;delta=a*a+4*a+3;u=j*c-(2*r+1)
    result=[(B-1)*J+1-P,m+z['radix_beta']-B,sum(E)-J,
            r-F0-q*F1-q*q*F2,s-2*z['odd_half']-1,r+z['bound_beta']-X,
            ((X*Y)**2+X)*(Y*k)**2-tau*(tau+1),c-Y*k-eta,k-eta-zeta,
            k-r-1-h*X*Y,a-Y*(X+1),d-X-a*c-ga*(4*a+3),
            d*d-1-delta*c*c,(i*c*c)**2-delta*(f*f-1),
            (i*c*c)**2*(u*u-y*y)-(1-y*y),u+c-o*f]
    result += [sum((s-B*t)*E[i] for i,(s,t,_) in enumerate(edges))]
    result += [1+sum(E[i] for i,e in enumerate(edges) if e[2] == label)-z[f'Shat{label-1}']
               for label in range(1,9)]
    return result


def action_path(edges, indices):
    state=0
    for index in indices:
        source,target,_=edges[index]
        if source != state:
            return False
        state=target
    return state == 0


def direct_regex(codes, letters):
    # Independent word-break recognition; no edge/state representation used.
    positions={0}
    for pos in range(len(letters)+1):
        if pos not in positions:
            continue
        for token in [(0,)]+[tuple(code) for code in codes]:
            if tuple(letters[pos:pos+len(token)]) == token:
                positions.add(pos+len(token))
    return len(letters) in positions


def outer_fixture(packet, indices, B):
    m=packet['m'];t=len(indices);P=B**t;J=sum(B**j for j in range(t))
    E=[sum(B**j for j,e in enumerate(indices) if e==i) for i in range(m)]
    K=sum(P**i for i in range(m));H=sum(e*P**i for i,e in enumerate(E));M=J*K
    assert H & M == H
    q=1 << (8*M+6).bit_length()
    F1=8*(M-H)+2;F2=8*H+4;F0=q-1-F1-F2
    assert min(F0,F1,F2)>0 and F0&1
    assert (F0&F1)|(F0&F2)|(F1&F2)==0
    values={name:1 for name in packet['parameters']+packet['auxiliaries']}
    values.update(B=B,P=P,J=J,radix_beta=B-m,F0=F0)
    values.update({f'edge_hat{i}':e+1 for i,e in enumerate(E)})
    values.update({f'Shat{label-1}':1+sum(E[i] for i,e in enumerate(packet['edges']) if e[2]==label)
                   for label in range(1,9)})
    env=execute(packet['source'],values)
    assert env['q']==q and env['F1']==F1 and env['F2']==F2
    assert env['edge_word']==H and env['origin_mask']==M
    rr=residuals(packet,env)
    # Core coordinates are placeholders here. Full positivity is supplied
    # by the native binary53 theorem at this exact padded partition.
    assert rr[:3]==[0,0,0] and rr[17:]==[0]*8
    assert (rr[16]==0)==action_path(packet['edges'],indices)
    return values


def verify():
    rng=random.Random(258531)
    examples=[((1,),),((1,2),),((1,3),(2,4),(5,7,6,8)),((1,1,2),(2,3,2),(4,5))]
    packets=[build(macro_table(codes)) for codes in examples]
    random_residuals=0
    for packet in packets:
        polynomial,output=polynomial_source(packet)
        count=Counter('M' if op=='*' else 'A' for _,op,_,_ in polynomial)
        assert len(polynomial)==packet['operations']+74
        assert count=={'M':packet['multiplications']+25,'A':packet['additions_subtractions']+49}
        for _ in range(256):
            z={name:rng.randrange(1,14) for name in packet['parameters']+packet['auxiliaries']}
            env=execute(polynomial,z)
            assert residuals(packet,env)==manual_residuals(packet,z)
            assert env[output]==sum(r*r for r in manual_residuals(packet,z))
            random_residuals+=1
    path_cases=0;word_cases=0;outer_cases=0
    for codes,packet in zip(examples,packets):
        m=packet['m'];B=1 << m.bit_length()
        for t in range(1,5):
            selections=product(range(m),repeat=t) if m<=4 else [tuple(rng.randrange(m) for _ in range(t)) for _ in range(256)]
            language=set()
            for indices in selections:
                S=sum(packet['edges'][e][0]*B**j for j,e in enumerate(indices))
                T=sum(packet['edges'][e][1]*B**j for j,e in enumerate(indices))
                valid=action_path(packet['edges'],indices)
                assert (S==B*T)==valid
                if valid:
                    letters=tuple(packet['edges'][e][2] for e in indices)
                    assert direct_regex(codes,letters)
                    language.add(letters)
                path_cases+=1
            if m<=4:
                alphabet=sorted({e[2] for e in packet['edges']})
                for letters in product(alphabet,repeat=t):
                    assert (letters in language)==direct_regex(codes,letters)
                    word_cases+=1
        for _ in range(64):
            indices=tuple(rng.randrange(m) for _ in range(rng.randrange(1,9)))
            values=outer_fixture(packet,indices,B)
            assert all(v>0 for v in values.values())
            outer_cases+=1
    # An unbounded family of genuine hub paths omits every non-idle edge.
    for t in range(1,33):
        outer_fixture(packets[-1],(0,)*t,32)
        outer_cases+=1
    # The binary53 prefix handles unused field bits and all subset shapes.
    subsets=0
    for M in range(256):
        H=M
        while True:
            F1=8*(M-H)+2;F2=8*H+4
            q=1 << (8*M+6).bit_length();F0=q-1-F1-F2
            assert min(F0,F1,F2)>0 and F0&1
            assert F0+F1+F2==q-1
            assert not ((F0&F1)|(F0&F2)|(F1&F2))
            subsets+=1
            if H==0:break
            H=(H-1)&M
    # Necessity of a radix margin: B+1 low active bits carry into the next cell.
    B=4;J=1+B;E=[1]*(B+1)+[0]*3
    assert len(E)==8 and sum(E)==J and all(e&J==e for e in E)
    assert sum(e% B for e in E)==B+1
    # Scalar total/flow equations cannot substitute for sparse edge typing.
    B=8;P=B**2;J=1+B;E=[2,7,0,0]
    assert sum(E)==J and all(0<=e<P for e in E) and any(e&J!=e for e in E)
    # Dyadic B,P plus the paid repunit equation recover an integral duration.
    geometry=0
    for d in range(1,12):
        for ell in range(1,80):
            B=2**d;P=2**ell
            assert ((P-1)%(B-1)==0)==(ell%d==0)
            geometry+=1
    ledgers=[]
    for packet in packets:
        m=packet['m'];h=packet['h'];p=packet['projection_additions']
        assert packet['operations']==7*m+3*h+p+60
        ledgers.append({key:packet[key] for key in ('m','h','edges','operations','multiplications','additions_subtractions','projection_additions','source','comparisons','parameters','auxiliaries')})
    return dict(status='PASS_GROUP_REGULAR_MACRO_CONTROLLER',ledgers=ledgers,
                independently_expanded_full_residual_cases=random_residuals,
                edge_sequence_flow_cases=path_cases,independent_regular_language_cases=word_cases,
                positive_outer_extension_cases=outer_cases,subset_prefix_cases=subsets,
                dyadic_geometry_cases=geometry,comparisons=25,auxiliaries='m+22',
                conditional_operations='7m+3h+p+60, m=2^h',
                sum_of_squares_operations='7m+3h+p+134',
                external='B and P are powers of two; no scalar predicate for those assumptions is imported for free.',
                scope='Certifies an actual fixed hub macro controller and its eight Boolean one-hot-or-idle selector outputs. The universal subgroup table is not numerically transcribed. No complete universal bound follows.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
