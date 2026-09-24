#!/usr/bin/env python3
"""Complete fixed-index raw-input certificate: 88 operations, 36 witnesses."""
from pathlib import Path
import json
import sys
import sympy as sp

import explore_unique_start_cyclic as unique
import explore_raw_input_exponent_bridge as exponent
import round4_1980_operation_count as baseline
from round13_1980_certificate import verify_primitives

OUT = Path(__file__).with_suffix('.json')
NAMES = unique.NAMES + exponent.NEW_NAMES + ['Lend', 'betaend', 'Tend']
CONSTANTS = unique.CONSTANTS + ['CE']
SYM = {name: sp.Symbol(name) for name in NAMES + CONSTANTS + ['x']}
ADAPTER = [(name, op, left, 2 if right == 'c0' else right)
           for name, op, left, right in exponent.ADAPTER]
SCHEDULE = unique.SCHEDULE + ADAPTER + unique.PIN
EQUALITIES = [('raw_bound', 'q') if pair == ('bounded', 'q') else pair
              for pair in unique.EQUALITIES] + [
    ('kappa', 'index_rhs'), ('c', 'pell_gap'), ('mu2', 'norm_rhs'), ('mu', 'exponent_rhs'),
    ('C', 'endpoint_rhs'), ('endpoint_remainder_bound', 'W')]


def source_residuals():
    z = SYM
    sources = unique.source_residuals()
    sources[3] += z['x']+2
    t = z['x']+2
    A0 = z['a']+2
    D = A0*A0-1
    sources += [z['kappa']-t-z['delta']*(z['a']+1), z['c']-z['kappa']-z['phi'],
                z['mu']**2-1-D*z['kappa']**2,
                z['mu']-z['W']-z['kappa']*(A0-z['P'])-z['rho']*(D-(A0-z['P'])**2),
                z['C']-z['Lend']-z['CE']*z['W']*z['Tend'],
                z['Lend']+z['betaend']-z['W']]
    return sources


def verify_source():
    env = unique.previous.four.previous.fixed_environment(SYM)
    baseline.run_schedule(SCHEDULE, env)
    sources = source_residuals()
    u = SYM['j']*SYM['c']-(2*SYM['r']+1)
    correction = sources[14]*(u*u-SYM['y_aux']**2)
    records = []
    for i, ((left, right), source) in enumerate(zip(EQUALITIES, sources)):
        actual = sp.expand(env[left]-env[right])
        adjust = correction if i == 15 else sp.Integer(0)
        sign = 1 if sp.expand(actual-source-adjust) == 0 else -1
        assert sp.expand(actual-sign*source-adjust) == 0, i
        records.append(dict(index=i,equality=[left,right],source_sign=sign,
                            source=sp.sstr(sp.expand(source)),correction=sp.sstr(sp.expand(adjust))))
    primitives, counts = verify_primitives(SCHEDULE, env)
    assert len(primitives) == 88 and counts == {'+':41, '*':47}
    assert len(NAMES) == len(set(NAMES)) == 36
    assert len(sources) == len(EQUALITIES) == 23
    assert SCHEDULE[:67] == unique.SCHEDULE and SCHEDULE[-4:] == unique.PIN
    assert not any('c0' == operand for row in SCHEDULE for operand in row)
    assert sp.expand(env['raw_t']-SYM['x']-2) == 0
    assert sp.expand(env['packed']-SYM['B']*SYM['Tmarker']-SYM['q']*SYM['F']) == 0
    # All supplied fixed aliases depend exclusively on fixed compiler numerals.
    fixed_symbols = {SYM[name] for name in CONSTANTS}
    initial = unique.previous.four.previous.fixed_environment(SYM)
    aliases = {name:value for name,value in initial.items() if name not in SYM}
    for name, value in aliases.items():
        assert sp.sympify(value).free_symbols <= fixed_symbols, name
    return dict(operations=88,multiplications=47,additions_subtractions=41,
                positive_existential_unknown_count=36,positive_unknowns=NAMES,raw_parameters=['x>0'],
                equations=23,fixed_constants=CONSTANTS,fixed_offset=2,
                fixed_aliases={name:sp.sstr(value) for name,value in aliases.items()},
                primitive_instructions=primitives,sources=records,
                ledger={'unique_start':67,'raw_exponent_including_stronger_bound':17,'endpoint':4},
                complete_fixed_index_raw_input_universal_certificate=True,
                kernel_source_identical=True,source_equivalence_uses_only_preceding_norm_residual=True)


def verify_composed_interfaces():
    cc = unique.compile_rule(3, None)
    B, R = cc.B, cc.R
    CE = 2*R**2
    cases = rejected_wrong_inputs = 0
    max_q_bits = max_kappa_bits = 0
    for x in range(1, 6):
        t = x+2
        for h in (1, 2, 3):
            for extra in (1, 2):
                N = h*t+extra
                for fill in (0, 1):
                    states = [0]+[1]*(N-1)
                    states[h*t] = 2
                    rows = [tuple(int(j == state) for j in range(3))+
                            (fill if i else 0,)*(cc.m+1-3) for i,state in enumerate(states)]
                    cells = [cc.cell(row) for row in rows]
                    pack = lambda values: sum(value*B**i for i,value in enumerate(values))
                    q, P = B**N, B**h
                    C, Z = pack(cells), pack(cells)-2
                    J, D = (q-1)//(B-1), q-1
                    RR = pack([cells[(i-h)%N] for i in range(N)])
                    YY = pack([cells[(i-h-1)%N] for i in range(N)])
                    DC, DR, DY = cc.Ds
                    F = DC*C+DR*RR+DY*YY
                    zquot, remainder = divmod((DC+(DR+B*DY)*P)*C-F,D)
                    assert remainder == 0 and zquot > 0
                    r = (q*q-Z-q*F)*(q*q-1)+(cc.MC+q*cc.MF)*J
                    assert r%2 and q*q <= r < q**4 and r.bit_count() == 3*cc.d*N
                    assert Z & (cc.MC*J) == 0 and F & (cc.MF*J) == 0
                    values = dict(q=q,P=P,C=C,v=q//P,Jrep=J,align=(P-1)//(B-1),
                                  F=F,alpha=q-C-t,zquot=zquot,r=r,Tmarker=Z//B)
                    assert min(values.values()) > 0
                    env = unique.numeric_outer(values,cc)
                    assert env['bounded']+t == q
                    assert all(env[a] == env[b] for a,b in unique.OUTER_EQUALITIES if (a,b) != ('bounded','q'))
                    W = P**t
                    quotient, Lend = divmod(C,W)
                    Tend, remainder = divmod(quotient,CE)
                    assert remainder == 0
                    betaend = W-Lend
                    assert min(Lend,betaend,Tend) > 0 and W < C < q
                    env.update(CE=CE,W=W,Tend=Tend,Lend=Lend,betaend=betaend)
                    baseline.run_schedule(unique.PIN,env)
                    assert env['endpoint_rhs'] == C and env['endpoint_remainder_bound'] == W
                    # Exact bounded bridge instance on the same q,P,C,W. These
                    # moderate Pell parameters do not claim a full kernel tuple.
                    A0 = 10*q+11
                    J0 = t+5
                    mu,kappa = exponent.pell(A0,t)
                    c = exponent.pell(A0,J0)[1]
                    delta, remainder = divmod(kappa-t,A0-1)
                    assert remainder == 0
                    H = A0*A0-1-(A0-P)**2
                    rho, remainder = divmod(mu-W-kappa*(A0-P),H)
                    assert remainder == 0
                    phi = c-kappa
                    assert min(kappa,mu,delta,phi,rho) > 0
                    assert t < q and 0<t<J0<A0-1 and W<q<A0<H
                    env.update(x=x,a=A0-2,A=A0*A0-1,c=c,kappa=kappa,mu=mu,delta=delta,phi=phi,rho=rho)
                    baseline.run_schedule(ADAPTER,env)
                    assert env['raw_bound'] == q and env['index_rhs'] == kappa and env['pell_gap'] == c
                    assert env['mu2'] == env['norm_rhs'] and env['exponent_rhs'] == mu
                    # Holding the actual endpoint fixed, one different input
                    # cannot satisfy the exponent congruence with its true index.
                    wrong_t = t-1
                    bad_mu,bad_kappa = exponent.pell(A0,wrong_t)
                    assert (bad_mu-W-bad_kappa*(A0-P))%H != 0
                    rejected_wrong_inputs += 1
                    max_q_bits = max(max_q_bits,q.bit_length())
                    max_kappa_bits = max(max_kappa_bits,kappa.bit_length())
                    cases += 1
    return dict(cases=cases,rejected_wrong_raw_inputs=rejected_wrong_inputs,
                max_q_bits=max_q_bits,max_bridge_kappa_bits=max_kappa_bits,
                positive_outer_and_endpoint_and_bridge_coordinates=True,
                zero_and_all_dummy_fills=True,full_packed_kernel_tuples_materialized=False,
                scope='Composed exact outer, endpoint and bounded-Pell adapter examples; moderate independent bridge parameters, not full retained kernel witnesses')


def verify():
    return dict(status='PASS_FIXED_RAW_UNIVERSAL88',source=verify_source(),
                composed_interfaces=verify_composed_interfaces(),
                proof='../1980/FIXED_RAW_UNIVERSAL_88_PROOF.md',
                complete_fixed_index_raw_input_universal_certificate=True,
                proof_assistant_verified=False,
                scope='Mathematical fixed-index positive raw-input theorem; full symbolic source equivalence and bounded component/composition checks')


if __name__ == '__main__':
    result = verify()
    if sys.argv[1:] == ['--write']:
        OUT.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    else:
        assert not sys.argv[1:]
        assert result == json.loads(OUT.read_text(encoding='utf-8'))
    print(result['status'],result['source']['operations'],'operations;',
          result['composed_interfaces']['cases'],'composed interface examples')
