#!/usr/bin/env python3
"""17-op positive raw exponent adapter to marked67; W<q is external."""
from collections import Counter
from pathlib import Path
import json
import sys
import sympy as sp

import explore_three_cell_marked as base
import round4_1980_operation_count as baseline
from round13_1980_certificate import verify_primitives

OUT=Path(__file__).with_suffix('.json')
NEW_NAMES=['W','kappa','mu','delta','phi','rho']
NAMES=base.NAMES+NEW_NAMES
SYM={name:sp.Symbol(name) for name in NAMES+['x','c0']+base.CONSTANTS}
ADAPTER=[
    ('raw_t','+','x','c0'),('raw_bound','+','bounded','raw_t'),
    ('ap1','+','a',1),('index_product','*','delta','ap1'),
    ('index_rhs','+','raw_t','index_product'),('pell_gap','+','kappa','phi'),
    ('kappa2','*','kappa','kappa'),('scaled_kappa2','*','A','kappa2'),
    ('norm_rhs','+','scaled_kappa2',1),('mu2','*','mu','mu'),
    ('exponent_difference','-','ap1','Pm1'),
    ('difference2','*','exponent_difference','exponent_difference'),
    ('exponent_modulus','-','A','difference2'),
    ('modulus_multiple','*','rho','exponent_modulus'),
    ('difference_multiple','*','kappa','exponent_difference'),
    ('exponent_partial','+','W','difference_multiple'),
    ('exponent_rhs','+','exponent_partial','modulus_multiple')]
SCHEDULE=base.SCHEDULE+ADAPTER
EQUALITIES=[('raw_bound','q') if pair==('bounded','q') else pair for pair in base.EQUALITIES]+[
    ('kappa','index_rhs'),('c','pell_gap'),('mu2','norm_rhs'),('mu','exponent_rhs')]


def source_residuals():
    z=SYM;q,P,C,F,J=[z[name] for name in ('q','P','C','F','Jrep')]
    t=z['x']+z['c0'];A0=z['a']+2;D=A0*A0-1
    sources=[(z['B']-1)*J-q+1,P*z['v']-q,(z['B']-1)*z['align']-P+1,C+z['alpha']+t-q,
             (z['DC']+(z['DR']+z['B']*z['DY'])*P)*C-F-z['zquot']*(q-1),
             z['r']-(q*q-C-q*F)*(q*q-1)-(z['MC']+q*z['MF'])*J,
             C-2-z['B']*z['Tmarker']]+base.four.previous.source_residuals()[6:]
    sources += [z['kappa']-t-z['delta']*(z['a']+1),z['c']-z['kappa']-z['phi'],
                z['mu']**2-1-D*z['kappa']**2,
                z['mu']-z['W']-z['kappa']*(A0-P)-z['rho']*(D-(A0-P)**2)]
    return sources


def verify_source():
    env=base.four.previous.fixed_environment(SYM);baseline.run_schedule(SCHEDULE,env)
    sources=source_residuals();u=SYM['j']*SYM['c']-(2*SYM['r']+1)
    correction=sources[14]*(u*u-SYM['y_aux']**2);records=[]
    for i,((left,right),source) in enumerate(zip(EQUALITIES,sources)):
        actual=sp.expand(env[left]-env[right]);adjust=correction if i==15 else sp.Integer(0)
        sign=1 if sp.expand(actual-source-adjust)==0 else -1
        assert sp.expand(actual-sign*source-adjust)==0,i
        records.append(dict(index=i,equality=[left,right],source_sign=sign,
                            source=sp.sstr(sp.expand(source)),correction=sp.sstr(sp.expand(adjust))))
    primitives,counts=verify_primitives(SCHEDULE,env)
    assert len(ADAPTER)==17 and Counter(row[1] for row in ADAPTER)=={'+':8,'-':2,'*':7}
    assert len(primitives)==84 and counts=={'+':39,'*':45}
    assert len(NAMES)==len(set(NAMES))==33 and len(EQUALITIES)==len(sources)==21
    assert SCHEDULE[:67]==base.SCHEDULE
    assert sp.expand(env['exponent_difference']-(SYM['a']+2-SYM['P']))==0
    return dict(operations=84,multiplications=45,additions_subtractions=39,
                adapter_operations=17,adapter_multiplications=7,adapter_additions_subtractions=10,
                source_67_prefix_unchanged=True,positive_unknown_count_including_endpoint_W=33,
                positive_unknowns=NAMES,raw_parameters=['x'],fixed_offset='c0>=2; primary c0=3',
                equations=21,primitive_instructions=primitives,sources=records,
                external_unpriced_precondition='0<W<q from a separately counted endpoint interface',
                complete_raw_input_universal_certificate=False)


def pell(A,n):
    # Pair multiplication in Z[sqrt(A^2-1)] and binary powering.
    D=A*A-1
    def mul(p,q):return p[0]*q[0]+D*p[1]*q[1],p[0]*q[1]+p[1]*q[0]
    result=(1,0);power=(A,1)
    while n:
        if n&1:result=mul(result,power)
        n//=2
        if n:power=mul(power,power)
    return result


def verify_congruences():
    cases=indexcases=0
    for A in range(3,40):
        for t in range(1,20):
            mu,kappa=pell(A,t);assert mu*mu-(A*A-1)*kappa*kappa==1
            assert (kappa-t)%(A-1)==0;indexcases+=1
            for P in range(2,A):
                H=2*A*P-P*P-1
                assert H>0 and (mu-(A-P)*kappa-pow(P,t,H))%H==0
                cases+=1
    recovered=0
    for A in range(5,32):
        for J0 in range(2,A-1):
            for u in range(1,J0):
                kappa=pell(A,u)[1]
                possibilities=[t for t in range(1,J0) if (kappa-t)%(A-1)==0]
                assert possibilities==[u];recovered+=1
    return dict(exponent_congruence_cases=cases,index_congruence_cases=indexcases,
                exact_bounded_index_recoveries=recovered)


def verify_positive_examples():
    cases=aliases=0;records=[]
    for offset in (2,3,5):
        for x in range(1,6):
            t=x+offset
            for P in (2,3,5,16,32):
                W=P**t;q=W+1;A0=10*q+11;D=A0*A0-1;J0=t+5
                mu,kappa=pell(A0,t);c=pell(A0,J0)[1]
                H=D-(A0-P)**2
                delta,rem=divmod(kappa-t,A0-1);assert rem==0
                rho,rem=divmod(mu-W-kappa*(A0-P),H);assert rem==0
                phi=c-kappa
                assert min(delta,rho,phi,mu,kappa)>0
                assert 0<t<J0<A0-1 and t<q and 0<W<q<A0<H and P**t<A0
                values=dict(x=x,c0=offset,W=W,a=A0-2,Pm1=P-1,A=D,kappa=kappa,
                            delta=delta,phi=phi,mu=mu,rho=rho,bounded=q-t,c=c,q=q)
                env=dict(values);baseline.run_schedule(ADAPTER,env)
                assert env['raw_bound']==q and env['index_rhs']==kappa and env['pell_gap']==c
                assert env['mu2']==env['norm_rhs'] and env['exponent_rhs']==mu
                # Without the external upper bound, the congruence allows an alias.
                if rho>1:
                    Wbad=W+H;rhobad=rho-1
                    assert Wbad>q and rhobad>0 and mu==Wbad+kappa*(A0-P)+rhobad*H
                    aliases+=1
                records.append(dict(raw_x=x,offset=offset,base=P,index=t,
                                    pell_parameter_bits=A0.bit_length(),main_coordinate_bits=c.bit_length(),
                                    all_five_witnesses_positive=True))
                cases+=1
    return dict(cases=cases,smallest_raw_input_one_included=True,positive_out_of_range_aliases=aliases,
                records=records,
                scope='Exact bridge witnesses with moderate Pell parameters satisfying the bridge inequalities; not actual astronomical packed-kernel tuples')


def verify_slack():
    cases=0
    for B in (16,32,128):
        for h in (1,2,3):
            for t in range(3,10):
                P=B**h;W=P**t
                for extra in (1,2,4):
                    N=h*t+extra;q=B**N;J=(q-1)//(B-1)
                    for C in (2,2*J,(B-2)*J):
                        assert 0<C<q and W<q and q-C>=J+1 and J>=B**t>t
                        assert q-C-t>0;cases+=1
    return dict(typed_word_slack_cases=cases,endpoint_strict_bound_preserves_positive_alpha=True)


def verify():
    return dict(status='PASS_RAW_INPUT_EXPONENT_BRIDGE17',source=verify_source(),
                congruences=verify_congruences(),positive_examples=verify_positive_examples(),
                strengthened_slack=verify_slack(),proof='../1980/EXPLORATION_RAW_INPUT_EXPONENT_BRIDGE.md',
                complete_raw_input_universal_certificate=False,
                scope='Exact17-operation positive exponent adapter on top of67, conditional on separately paid W<q endpoint interface')


if __name__=='__main__':
    result=verify()
    if sys.argv[1:]==['--write']:
        OUT.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    else:
        assert not sys.argv[1:]
        assert json.loads(json.dumps(result))==json.loads(OUT.read_text(encoding='utf-8'))
    print(result['status'],result['source']['adapter_operations'],'additional operations;',
          result['positive_examples']['cases'],'positive bridge examples')
