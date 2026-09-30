"""Exact filtered paired FIFO66/71/74; no universal-controller claim."""
import argparse
from collections import Counter, deque
from itertools import product
import json
from pathlib import Path
import sympy as sp

import native_boolean_pair_fifo63 as paired
import input_bridge_boolean_ternary60 as boolean


FILTER = [('pf_H', '+', 'bt_append', 'F2'),
          ('pf_twiceH', '+', 'pf_H', 'pf_H'),
          ('pf_repunit', '+', 'pf_twiceH', 1)]
CONTROL = [('pf_weight0', '*', 'g0', 'F0'),
           ('pf_weight1', '*', 'g1', 'F1'),
           ('pf_weight2', '*', 'g2', 'F3'),
           ('pf_sum01', '+', 'pf_weight0', 'pf_weight1'),
           ('pf_total', '+', 'pf_sum01', 'pf_weight2')]
ALIGN = [('pf_time_blocks', '*', 'block_modulus', 'block_time'),
         ('pf_width_blocks', '*', 'block_modulus', 'block_width'),
         ('pf_aligned_width', '+', 'pf_width_blocks', 1)]


def source_check(controller=True, aligned=False):
    assert controller or not aligned
    base = paired.source_check(controller=False)
    parameters = base['positive_parameters']
    auxiliaries = base['positive_auxiliaries'] + (['block_time', 'block_width'] if aligned else [])
    z = {name: sp.Symbol(name) for name in parameters + auxiliaries}
    constants = {name: sp.Symbol(name) for name in ('g0', 'g1', 'g2', 'gap', 'block_modulus')}
    schedule = [tuple(row) for row in base['instructions']] + FILTER
    equalities = [tuple(row['equality']) for row in base['sources']] + [('pf_repunit', 'q')]
    polynomials = paired.independent_sources(z, controller=False)
    polynomials += [2*(z['F0']+z['F1']+z['F2'])+1-z['q']]
    if controller:
        schedule += CONTROL
        equalities += [('pf_total', 'gap')]
        polynomials += [constants['g0']*z['F0']+constants['g1']*z['F1']+
                        constants['g2']*z['F3']-constants['gap']]
    if aligned:
        schedule += ALIGN
        equalities += [('pf_time_blocks', 'pf_twiceH'), ('pf_aligned_width', 'W')]
        polynomials += [constants['block_modulus']*z['block_time']-
                        2*(z['F0']+z['F1']+z['F2']),
                        constants['block_modulus']*z['block_width']+1-z['W']]
    env = boolean.prior.execute(schedule, dict(z, **constants, n2=z['q']))
    u = 2*z['r']+1+z['j']*z['c']
    correction = polynomials[8]*(u*u-z['y_aux']**2)
    records = []
    for ix, ((left, right), polynomial) in enumerate(zip(equalities, polynomials)):
        adjust = correction if ix == 9 else 0
        assert sp.expand(env[left]-env[right]-polynomial-adjust) == 0, ix
        records.append(dict(equality=[left, right], source=str(sp.expand(polynomial)),
                            correction=str(sp.expand(adjust))))
    counts = Counter(row[1] for row in schedule)
    expected = 66+5*controller+3*aligned
    assert len(schedule) == expected
    assert counts['*'] == 32+3*controller+2*aligned
    assert counts['+']+counts['-'] == 34+2*controller+aligned
    assert len(equalities) == len(polynomials) == 19+controller+2*aligned
    assert len(parameters)+len(auxiliaries)-1 == 29+2*aligned
    # Recover the full carry identity using the filter and fixed endpoint.
    h,u0,u1,v0,v1,cs,cf,H = sp.symbols('h u0 u1 v0 v1 cs cf H')
    full = (cs+h*H+u0*(H-z['F0']-z['F1'])+u1*z['F3']+
            v0*z['F0']+v1*z['F1']-(2*H+1)*cf)
    reduced = (v0-u0)*z['F0']+(v1-u0)*z['F1']+u1*z['F3']+cs-cf
    assert sp.expand(full.subs(h, 2*cf-u0)-reduced) == 0
    return dict(operations=expected, multiplications=counts['*'],
                additions_subtractions=counts['+']+counts['-'], equations=len(equalities),
                positive_parameters=parameters, positive_auxiliaries=auxiliaries,
                positive_existentials_excluding_x=len(parameters)+len(auxiliaries)-1,
                fixed_constants=({'g0':'v0-u0','g1':'v1-u0','g2':'u1','gap':'cf-cs',
                                  'endpoint_condition':'2*cf=h+u0'} if controller else {}),
                block_alignment=('block_modulus=3^ell-1 for fixed ell>=2' if aligned else None),
                instructions=[list(row) for row in schedule], sources=records,
                scope='Exact filtered paired finite-machine relation; no universality theorem')


def digits(value, t):
    return tuple(value//3**j % 3 for j in range(t))


def word(bits):
    return sum(bit*3**j for j,bit in enumerate(bits))


def filter_checks():
    cases = admitted = 0
    for t in range(1,5):
        q = 3**t
        values = [word(bits) for bits in product((0,1), repeat=t)][1:]
        for fields in product(values, repeat=4):
            equality = 2*sum(fields[:3])+1 == q
            local = all(sum(fields[i]//3**j % 3 for i in range(3)) == 1 for j in range(t))
            assert equality == local
            if equality:
                assert sum(fields) < q
                admitted += 1
            cases += 1
    return dict(positive_boolean_field_tuples=cases, admitted=admitted, lengths=[1,4],
                scope='Filter and automatic joint bound; FIFO and parity are not assumed here')


LABELS = [(a0,a1,d0,d1) for a0,a1,d0,d1 in product((0,1), repeat=4)
          if a0+a1+d0 == 1]


def carry_checks():
    cases = admitted = 0
    # u0,u1,v0,v1,h,cs,cf; all satisfy the required fixed endpoint identity.
    configs = [(2,3,-2,4,-2,0,0), (3,-4,5,-2,1,-2,2),
               (-2,5,-3,4,0,1,-1), (0,0,0,0,0,0,0)]
    for t in range(1,6):
        q,H = 3**t,(3**t-1)//2
        for labels in product(LABELS, repeat=t):
            fields = [word(row[i] for row in labels) for i in range(4)]
            assert sum(fields[:3]) == H
            for u0,u1,v0,v1,h,cs,cf in configs:
                assert 2*cf == h+u0
                reduced = (v0-u0)*fields[0]+(v1-u0)*fields[1]+u1*fields[3] == cf-cs
                full = cs+h*H+u0*fields[2]+u1*fields[3]+v0*fields[0]+v1*fields[1] == q*cf
                c = cs
                integral = True
                for a0,a1,d0,d1 in labels:
                    numerator = c+h+u0*d0+u1*d1+v0*a0+v1*a1
                    if numerator % 3:
                        integral = False
                        break
                    c = numerator//3
                actual = integral and c == cf
                assert reduced == full == actual
                cases += 1
                admitted += actual
    return dict(local_words_and_controller_configs=cases, admitted=admitted,
                maximum_word_length=5, configs=[list(row) for row in configs],
                scope='All six local labels, including initial read11; zero fields allowed in this standalone identity check')


def positive_maps():
    examples = []
    for x in range(1,201):
        W,m = 3,1
        while W <= 6*x:
            W *= 3
            m += 1
        I0,I1 = boolean.split(2*x)
        if not I1:
            # An even positive all-0/1 word has at least two nonzero trits.
            place = next(3**j for j in range(m) if I0//3**j % 3)
            I0 -= place
            I1 = place
        Hm = (W-1)//2
        fields = [W*Hm,Hm-I0,I0+W*W*Hm,I1+W*(Hm-I0)]
        q,t = W**3,3*m
        assert I0>0 and I1>0 and I0+I1==2*x
        assert all(boolean.native_boolean(f,t) for f in fields)
        assert sum(fields[:3]) == (q-1)//2 and sum(fields)<q and sum(fields)%2==0
        assert fields[2] == I0+W*fields[0] and fields[3] == I1+W*fields[1]
        n0,n1 = I0,I1
        for j in range(t):
            a0,a1,d0,d1 = (f//3**j % 3 for f in fields)
            assert (n0%3,n1%3) == (d0,d1) and a0+a1+d0 == 1
            n0,n1 = n0//3+(W//3)*a0,n1//3+(W//3)*a1
        assert n0==n1==0
        if x in (1,2,10,200):
            examples.append(dict(x=x,W=W,q=q,initial=[I0,I1],fields=fields,
                                 alpha=q-sum(fields),width_beta=W-2*x,L=q//W))
    return dict(ordinary_positive_inputs=200,examples=examples,
                projection='Every positive x has a66 witness by three exact sweeps',
                kernel_extension='The proved positive Boolean55 converse supplies Pell coordinates; not materialized')


def controlled_witness():
    q,W,x = 81,3,1
    fields = [9,3,28,10]
    labels = list(zip(*(digits(f,4) for f in fields)))
    u0,u1,v0,v1,h,cs,cf = 2,3,-2,4,-2,0,0
    c,n0,n1 = cs,1,1
    carries = [c]
    for a0,a1,d0,d1 in labels:
        assert (d0,d1)==(n0%3,n1%3) and a0+a1+d0==1
        numerator = c+h+u0*d0+u1*d1+v0*a0+v1*a1
        assert numerator%3==0
        c = numerator//3
        carries.append(c)
        n0,n1 = n0//3+a0,n1//3+a1
    assert (c,n0,n1)==(cf,0,0) and carries==[0,1,1,0,0]
    assert -4*fields[0]+2*fields[1]+3*fields[3]==0
    assert all(boolean.native_boolean(f,4) for f in fields)
    assert sum(fields)<q and sum(fields)%2==0
    return dict(x=x,W=W,q=q,initial=[1,1],fields=fields,
                labels_append_then_read=[list(row) for row in labels],carries=carries,
                controller=dict(read_weights=[u0,u1],append_weights=[v0,v1],h=h,cs=cs,cf=cf),
                alpha=31,width_beta=1,L=27,
                kernel_extension='Exact full positive extension by Boolean55 theorem, not materialized')


def alignment_checks():
    cases = 0
    for ell in range(2,9):
        modulus = 3**ell-1
        for m,t in product(range(1,31), repeat=2):
            arithmetic = (3**m-1)%modulus == 0 and (3**t-1)%modulus == 0
            assert arithmetic == (m%ell==0 and t%ell==0)
            cases += 1
    return dict(exponent_pairs=cases,fixed_block_lengths=[2,8],tested_exponents=[1,30])


def terminal_bound_checks():
    # Complete finite-state searches for the listed initial words and constants.
    # The endpoint is inspected at every carry, including mismatched endpoints.
    configs = [(2,3,-2,4,-2,0), (3,2,5,4,-2,0),
               (-2,1,4,-3,1,1), (0,0,0,0,0,0)]
    states_checked = witnesses = mismatched = forced_tails = 0
    for m in range(1,5):
        W = 3**m
        for x in (1,2):
            if 2*x >= W:
                continue
            possibilities = [word(bits) for bits in product((0,1),repeat=m)]
            initial_pairs = [(i,2*x-i) for i in possibilities if i>0 and 2*x-i>0 and 2*x-i in possibilities]
            for u0,u1,v0,v1,h,cs in configs:
                G = abs(h)+abs(u0)+abs(u1)+abs(v0)+abs(v1)
                C = max(abs(cs),(G+1)//2)
                B = 2*C+abs(h+u0)
                for I0,I1 in initial_pairs:
                    first = (I0,I1,cs,0)
                    seen = {first:(0,())}
                    pending = deque([first])
                    while pending:
                        n0,n1,c,mask = state = pending.popleft()
                        length,tail = seen[state]
                        states_checked += 1
                        if n0==n1==0 and mask==15:
                            cf = c
                            assert length>2*m
                            witnesses += 1
                            delta = 2*cf-h-u0
                            assert all(label==(0,0,1,0) for label in tail)
                            assert W*abs(delta)<=B
                            forced_tails += 1
                            if delta:
                                assert 2*x<W<=B
                                mismatched += 1
                        d0,d1 = n0%3,n1%3
                        appends = ((0,0),) if d0 else ((1,0),(0,1))
                        for a0,a1 in appends:
                            numerator = c+h+u0*d0+u1*d1+v0*a0+v1*a1
                            if numerator%3:
                                continue
                            nxt_c = numerator//3
                            assert abs(nxt_c)<=C
                            label = (a0,a1,d0,d1)
                            nxt_mask = mask | sum(bit<<i for i,bit in enumerate(label))
                            nxt = (n0//3+(W//3)*a0,n1//3+(W//3)*a1,nxt_c,nxt_mask)
                            if nxt not in seen:
                                seen[nxt] = (length+1,(tail+(label,))[-m:])
                                pending.append(nxt)
    assert witnesses and mismatched and forced_tails==witnesses
    return dict(finite_reachable_states=states_checked,zero_queue_all_tracks_endpoints=witnesses,
                mismatched_endpoint_examples=mismatched,unconditional_forced_terminal_tails=forced_tails,
                widths_m=[1,4],ordinary_inputs=[1,2],configs=[list(row) for row in configs],
                scope='Finite supplementary checks; parametric proof gives uniform finite input set for mismatched endpoint')


def verify():
    return dict(status='PASS_FILTERED_PAIRED_FIFO66_71_74',
                sources=dict(filter66=source_check(False),controller71=source_check(),aligned74=source_check(True,True)),
                filter=filter_checks(),carry=carry_checks(),ordinary_maps=positive_maps(),
                controlled_witness=controlled_witness(),alignment=alignment_checks(),terminal_bound=terminal_bound_checks(),
                scope='Exact filtered finite-machine relation and scoped obstructions; no complete universal compiler',
                established_complete_universal_bound=76)


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=verify();path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(json.dumps({key:value for key,value in result.items() if key!='sources'},indent=2))
