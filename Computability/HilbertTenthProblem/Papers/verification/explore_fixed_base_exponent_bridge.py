#!/usr/bin/env python3
"""15-op fixed-base exponent adapter; helical tableau interface is external."""
from collections import Counter
from pathlib import Path
import json
import sys
import sympy as sp

import explore_fixed_raw_universal_84 as previous
import explore_raw_input_exponent_bridge as variable
import round4_1980_operation_count as baseline
from round13_1980_certificate import verify_primitives

OUT=Path(__file__).with_suffix('.json')
NAMES=list(previous.NAMES)
CONSTANTS=previous.CONSTANTS+['cell_bits']
SYM={name:sp.Symbol(name) for name in NAMES+CONSTANTS+['x']}
OUTER=[]
for row in previous.OUTER:
    if row[0]=='kp':row=('kp','*','DY','P')
    if row[0]=='kinner':row=('kinner','+','Kconstant','kp')
    OUTER.append(row)
CORE=list(previous.CORE)
ADAPTER=[
    ('raw_t','+','x',2),('scaled_t','*','cell_bits','raw_t'),
    ('raw_bound','+','bounded','scaled_t'),
    ('ap1','+','a',1),('index_product','*','delta','ap1'),
    ('index_rhs','+','scaled_t','index_product'),('pell_gap','+','kappa','phi'),
    ('kappa2','*','kappa','kappa'),('scaled_kappa2','*','A','kappa2'),
    ('norm_rhs','+','scaled_kappa2',1),('mu2','*','mu','mu'),
    ('modulus_multiple','*','rho','a4m5'),('difference_multiple','*','kappa','a'),
    ('exponent_partial','+','W','difference_multiple'),
    ('exponent_rhs','+','exponent_partial','modulus_multiple')]
SCHEDULE=OUTER+CORE+ADAPTER
EQUALITIES=list(previous.EQUALITIES)


def fixed_environment(values):
    return dict(values,Bm1=values['B']-1,
                Kconstant=values['DC']+values['B']*values['DR'])


def source_residuals():
    z=SYM;sources=list(previous.source_residuals())
    sources[3]=z['C']+z['alpha']+z['cell_bits']*(z['x']+2)-z['q']
    sources[4]=(z['DC']+z['B']*z['DR']+z['DY']*z['P'])*z['C']-z['F']-z['zquot']*(z['q']-1)
    sources[17]=z['kappa']-z['cell_bits']*(z['x']+2)-z['delta']*(z['a']+1)
    sources[20]=z['mu']-z['W']-z['a']*z['kappa']-z['rho']*(4*z['a']+3)
    return sources


def verify_source():
    env=fixed_environment(SYM);baseline.run_schedule(SCHEDULE,env)
    sources=source_residuals();u=SYM['j']*SYM['c']-(2*SYM['r']+1)
    correction=sources[14]*(u*u-SYM['y_aux']**2);records=[]
    for i,((left,right),source) in enumerate(zip(EQUALITIES,sources)):
        actual=sp.expand(env[left]-env[right]);adjust=correction if i==15 else sp.Integer(0)
        sign=1 if sp.expand(actual-source-adjust)==0 else -1
        assert sp.expand(actual-sign*source-adjust)==0,i
        records.append(dict(index=i,equality=[left,right],source_sign=sign,
                            source=sp.sstr(sp.expand(source)),correction=sp.sstr(sp.expand(adjust))))
    primitives,counts=verify_primitives(SCHEDULE,env)
    assert len(OUTER)==24 and len(CORE)==43 and len(ADAPTER)==15
    assert Counter(row[1] for row in ADAPTER)=={'+':8,'*':7}
    assert len(primitives)==82 and counts=={'+':38,'*':44}
    assert len(NAMES)==len(set(NAMES))==33 and len(EQUALITIES)==len(sources)==21
    assert CORE==previous.CORE
    assert sp.expand(env['scaled_t']-SYM['cell_bits']*(SYM['x']+2))==0
    assert sp.expand(env['exponent_rhs']-SYM['W']-SYM['a']*SYM['kappa']-(4*SYM['a']+3)*SYM['rho'])==0
    assert sp.expand(env['kinner']-SYM['DC']-SYM['B']*SYM['DR']-SYM['DY']*SYM['P'])==0
    used=set().union(*(expr.free_symbols for expr in sources))
    assert {SYM[name] for name in NAMES}<=used
    return dict(operations=82,multiplications=44,additions_subtractions=38,
                adapter_operations=15,adapter_multiplications=7,adapter_additions_subtractions=8,
                positive_unknowns=NAMES,positive_existential_unknown_count=33,equations=21,
                raw_parameters=['x>0'],fixed_constants=CONSTANTS,
                fixed_constraints=['B=2^cell_bits','cell_bits>=4'],
                primitive_instructions=primitives,sources=records,kernel_source_identical=True,
                complete_raw_input_universal_certificate=False,
                external_unpriced_interface='Fixed marked helical tableau equivalence with End at x+2')


def verify_congruences():
    cases=positive=0
    for A0 in range(4,65):
        a=A0-2;H=4*a+3;Delta=A0*A0-1
        for u in range(1,33):
            mu,kappa=variable.pell(A0,u)
            assert mu*mu-Delta*kappa*kappa==1
            assert (kappa-u)%(a+1)==0
            assert (mu-a*kappa-pow(2,u,H))%H==0
            if u>=2 and 2**u<A0:
                rho,rem=divmod(mu-a*kappa-2**u,H)
                assert rem==0 and rho>0;positive+=1
            cases+=1
    return dict(exact_base_two_congruence_cases=cases,positive_quotient_cases=positive)


def verify_helical_compositions():
    cc=previous.compile_rule(3,None);B,R,bits=cc.B,cc.R,cc.d
    cases=aliases=wrong_inputs=nondivisible_Z=0;max_q_bits=max_kappa_bits=0
    for x in range(1,4):
        t=x+2;u=bits*t
        for h in (1,2):
            for extra in (1,):
                N=t+h+extra;states=[1]+[2]*(N-1);states[t]=0
                for mode in (0,1,2):
                    rows=[tuple(int(j==state) for j in range(3))+
                          tuple(0 if mode==0 else 1 if mode==1 else (i+j)%2
                                for j in range(cc.m+2-3)) for i,state in enumerate(states)]
                    cells=[cc.cell(row) for row in rows]
                    pack=lambda values:sum(value*B**i for i,value in enumerate(values))
                    C=pack(cells);right=pack([cells[(i-1)%N] for i in range(N)])
                    nxt=pack([cells[(i-h)%N] for i in range(N)])
                    F=cc.Ds[0]*C+cc.Ds[1]*right+cc.Ds[2]*nxt
                    assert F==pack([cc.Ds[0]*cells[i]+cc.Ds[1]*cells[(i-1)%N]+cc.Ds[2]*cells[(i-h)%N] for i in range(N)])
                    q,P=B**N,B**h;W=B**t;Z=C-R-W;J,D=(q-1)//(B-1),q-1
                    assert W==2**u and 0<Z<C<q and 0<W<C<q and u<q
                    assert 0<F<q-1 and Z&(cc.MC*J)==0 and F&(cc.MF*J)==0
                    assert C<= (B-2)*J and q-C>=J+1 and J>=B**t>u
                    alpha=q-C-u;assert alpha>0
                    if Z%B:nondivisible_Z+=1
                    kR,rem=divmod(B*C-right,D);assert rem==0
                    kY,rem=divmod(P*C-nxt,D);assert rem==0
                    align=(P-1)//(B-1)
                    assert kR>=1 and kY>=align>=1
                    zquot=cc.Ds[1]*kR+cc.Ds[2]*kY
                    assert zquot>=cc.Ds[1]+cc.Ds[2]*align>0
                    r=(q*q-Z-q*F)*(q*q-1)+(cc.MC+q*cc.MF)*J
                    assert r%2 and q*q<=r<q**4 and r.bit_count()==3*bits*N
                    values=dict(q=q,P=P,C=C,Z=Z,v=q//P,Jrep=J,align=align,
                                F=F,alpha=alpha,zquot=zquot,r=r,W=W)
                    env=fixed_environment(dict(previous.constants(cc),cell_bits=bits,**values))
                    baseline.run_schedule(OUTER,env)
                    assert all(env[a]==env[b] for a,b in previous.OUTER_EQUALITIES if (a,b)!=('bounded','q'))
                    assert env['bounded']+u==q
                    # These moderate Pell parameters are independent of the
                    # huge packed r; this tests the shared outer/adapter interface.
                    A0=10*q+11;J0=u+5;a=A0-2;H=4*a+3
                    mu,kappa=variable.pell(A0,u)
                    next_mu,c=mu,kappa
                    for _ in range(J0-u):
                        next_mu,c=A0*next_mu+(A0*A0-1)*c,next_mu+A0*c
                    delta,rem=divmod(kappa-u,a+1);assert rem==0
                    rho,rem=divmod(mu-a*kappa-W,H);assert rem==0
                    phi=c-kappa;assert min(mu,kappa,delta,rho,phi)>0
                    assert 0<u<J0<a+1 and W<q<A0<H
                    env.update(x=x,a=a,A=A0*A0-1,a4m5=H,c=c,
                               kappa=kappa,mu=mu,delta=delta,phi=phi,rho=rho)
                    baseline.run_schedule(ADAPTER,env)
                    assert env['raw_bound']==q and env['index_rhs']==kappa and env['pell_gap']==c
                    assert env['mu2']==env['norm_rhs'] and env['exponent_rhs']==mu
                    assert (2**(u-bits)-W)%H!=0;wrong_inputs+=1
                    # Removing the strengthened raw bound permits large-input aliases.
                    # Adding a+1 to x increments u by cell_bits*(a+1).
                    assert delta>bits
                    assert kappa==bits*(x+(a+1)+2)+(delta-bits)*(a+1)
                    aliases+=1
                    max_q_bits=max(max_q_bits,q.bit_length());max_kappa_bits=max(max_kappa_bits,kappa.bit_length())
                    cases+=1
    assert nondivisible_Z>0
    return dict(cases=cases,nondivisible_Z_cases=nondivisible_Z,
                rejected_wrong_raw_inputs=wrong_inputs,positive_aliases_without_raw_bound=aliases,
                helical_offsets=[0,-1,'-h'],cell_bits=bits,max_q_bits=max_q_bits,
                max_bridge_kappa_bits=max_kappa_bits,full_packed_kernel_tuples_materialized=False,
                fixed_tableau_semantic_equivalence_tested=False,
                scope='Common q,P,C,Z,W and all outer/adapter equations; moderate Pell parameters, not full packed-kernel tuples')


def verify():
    return dict(status='PASS_FIXED_BASE_EXPONENT_BRIDGE15',source=verify_source(),
                congruences=verify_congruences(),helical_compositions=verify_helical_compositions(),
                proof='../1980/EXPLORATION_FIXED_BASE_EXPONENT_BRIDGE.md',
                complete_raw_input_universal_certificate=False,
                scope='Exact positive15-operation fixed-base bridge and conditional82 source; fixed helical tableau reduction external')


if __name__=='__main__':
    result=verify()
    if sys.argv[1:]==['--write']:
        OUT.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    else:
        assert not sys.argv[1:]
        assert result==json.loads(OUT.read_text(encoding='utf-8'))
    print(result['status'],result['source']['adapter_operations'],'additional operations;',
          result['helical_compositions']['cases'],'helical interface examples')
