#!/usr/bin/env python3
"""Complete76 certificate: reuse the main Pell power as temporal stride.

Checks are symbolic, sparse, and modular. Actual padded compiler words have
astronomical length and are supplied by proof, not numerically materialized.
"""
from itertools import product
from pathlib import Path
import argparse
import json
import sympy as sp
import explore_fixed_raw_universal_77 as previous

NAMES=[name for name in previous.NAMES if name not in ('P','v')]
CONSTANTS=list(previous.CONSTANTS)
SYM={name:previous.SYM[name] for name in NAMES+CONSTANTS+['x']}
TRANSPORT_NAMES={'kinner','innerC','local_rhs','local_rhs_sum'}
TRANSPORT=[(name,op,left,'wn2' if right=='P' else right)
           for name,op,left,right in previous.OUTER if name in TRANSPORT_NAMES]
OUTER=[row for row in previous.OUTER if row[0]!='Pv' and row[0] not in TRANSPORT_NAMES]
CORE=list(previous.CORE)
ADAPTER=[(name,op,'twice_cell_bits' if name=='scaled_t' else left,right)
         for name,op,left,right in previous.ADAPTER]
SCHEDULE=OUTER+CORE[:1]+TRANSPORT+CORE[1:]+ADAPTER
EQUALITIES=[pair for pair in previous.EQUALITIES if pair!=('Pv','q')]


def fixed_environment(values):
    env=previous.previous.previous.fixed_environment(values)
    env['twice_cell_bits']=2*values['cell_bits']
    return env


def source_residuals():
    old=previous.source_residuals();q,w=SYM['q'],SYM['w']
    return [sp.expand(source.subs({previous.SYM['P']:w*q**3,
                                 previous.SYM['cell_bits']:2*SYM['cell_bits']}))
            for index,source in enumerate(old) if index!=1]


def verify_source():
    env=fixed_environment(SYM)
    previous.previous.previous.previous.bridge.baseline.run_schedule(SCHEDULE,env)
    sources=source_residuals();U=SYM['j']*SYM['c']-(2*SYM['r']+1)
    correction=sources[12]*(U*U-SYM['y_aux']**2)
    records=[]
    for ix,((left,right),source) in enumerate(zip(EQUALITIES,sources)):
        actual=sp.expand(env[left]-env[right]);adjust=correction if ix==13 else sp.Integer(0)
        sign=1 if sp.expand(actual-source-adjust)==0 else -1
        assert sp.expand(actual-sign*source-adjust)==0,ix
        records.append(dict(index=ix,equality=[left,right],source_sign=sign,
                            source=sp.sstr(source),correction=sp.sstr(sp.expand(adjust))))
    primitives,counts=previous.previous.previous.previous.bridge.verify_primitives(SCHEDULE,env)
    assert len(primitives)==76 and counts=={'+':35,'*':41}
    assert len(NAMES)==30 and len(EQUALITIES)==len(sources)==19
    assert len(OUTER)+len(TRANSPORT)==19 and len(CORE)==43 and len(ADAPTER)==14
    assert CORE==previous.CORE
    used=set().union(*(s.free_symbols for s in sources))
    assert previous.SYM['P'] not in used and previous.SYM['v'] not in used
    assert {SYM[name] for name in NAMES}<=used
    assert sp.expand(env['raw_bound']-SYM['C']-SYM['alpha']-2*SYM['cell_bits']*SYM['x'])==0
    assert sp.expand(env['odd_index']-2*SYM['cell_bits']*SYM['x']-SYM['inner_bits'])==0
    assert sp.expand(env['innerC']-(SYM['DC']+SYM['B']*SYM['DR']+SYM['w']*SYM['q']**3)*SYM['C'])==0
    aliases={name:value for name,value in fixed_environment(SYM).items() if name not in SYM}
    assert all(sp.sympify(value).free_symbols<={SYM[name] for name in CONSTANTS} for value in aliases.values())
    return dict(operations=76,multiplications=41,additions_subtractions=35,
                positive_existential_unknown_count=30,positive_unknowns=NAMES,equations=19,
                fixed_constants=CONSTANTS,raw_parameters=['x>0'],
                primitive_instructions=primitives,sources=records,
                fixed_aliases={name:sp.sstr(value) for name,value in aliases.items()},
                ledger={'outer_including_relocated_transport':19,'retained_kernel':43,'input_bridge':14},
                removed_instruction=['Pv','*','P','v'],removed_coordinates=['P','v'],
                temporal_multiplier='wn2=w*q^3, recovered as 2^(2r+1)',
                exact_input_exponent='2*cell_bits*x+inner_bits',
                relocated_after_wn2=[list(row) for row in TRANSPORT])


def next_five_power(value):
    out=1
    while out<value:out*=5
    return out


def is_five_power(value):
    if value<1:return False
    while value%5==0:value//=5
    return value==1


class Compiled(previous.Compiled):
    pass


def compile_windows(windows,a):
    windows=tuple(tuple(w) for w in windows);k=len(windows)
    assert k>=2 and len(set(windows))==k and all(len(w)==9 for w in windows)
    assert all(0<=s<a for w in windows for s in w)
    A=1<<max(2,(k+1).bit_length());start=k+3*a
    payload={(r,c,s):start+(2-r)*3*a+(2-c)*a+s
             for r,c,s in product(range(3),range(3),range(a))}
    coeff={i:1 for i in range(k)};mu=A-2
    for j,((r,c,s),e) in enumerate(payload.items(),1):
        coeff[e]=A**j;mu+=A**j
        for i,w in enumerate(windows):
            if w[3*r+c]==s:coeff[i]+=A**j
    anchor_coeff=[]
    for j in range(1+9*a,1+9*a+4):
        value=A**j;anchor_coeff.append(value);mu+=value
        for i in range(k):coeff[i]+=value
    padding=0;m=2*mu.bit_count()+12*a+2;next_clause=1+9*a+4
    # One genuine dummy is needed for the completeness congruence control.
    while m+1<k+9*a+5:
        mu+=A**(next_clause+padding);padding+=1;m+=2
    dummy=tuple(range(start+9*a,start+9*a+(m+1-k-9*a-4)))
    assert dummy
    old_positions=tuple(range(k))+tuple(payload.values())+dummy
    anchor_unit=max(old_positions)+3*a+1
    anchors=tuple(mult*anchor_unit for mult in (1,3,9,27));positions=old_positions+anchors
    for e,value in zip(anchors,anchor_coeff):coeff[e]=value
    assert len(set(positions))==len(positions)==m+1
    E=max(positions);H=E+24*anchor_unit+3*a+1
    T1=H+2*E+a+1;T2=T1+2*E+1;high_degree=T2+E+1
    L=next_five_power(high_degree+E+1)
    target=max(2*(m+1)*(2*sum(coeff.values())+6),2*mu)+4
    radix_bits=next_five_power((target-1).bit_length())
    R=1<<radix_bits;d=radix_bits*L
    DCpoly={}
    for e in (3*a,H+a,8*anchor_unit,24*anchor_unit):previous.previous.add_term(DCpoly,e,1)
    for e,value in coeff.items():
        previous.previous.add_term(DCpoly,T1-e,value)
        previous.previous.add_term(DCpoly,T2-e,value)
    old_unit=(2*sum(c*pow(2,e,5) for e,c in DCpoly.items())-pow(2,H,5))%5
    high_correction=int(old_unit==0)
    if high_correction:previous.previous.add_term(DCpoly,high_degree,1)
    unit=(2*sum(c*pow(2,e,5) for e,c in DCpoly.items())-pow(2,H,5))%5
    assert unit!=0
    MFpoly={T1:mu,T2:mu}
    for r,c,s in product(range(2),range(3),range(a)):previous.previous.add_term(MFpoly,payload[r,c,s],1)
    for r,c,s in product(range(3),range(2),range(a)):previous.previous.add_term(MFpoly,H+payload[r,c,s],1)
    for e in anchors[2:]:previous.previous.add_term(MFpoly,e,1)
    assert sum(v.bit_count() for v in MFpoly.values())==m
    assert max(DCpoly)+E<L and max(MFpoly)<high_degree
    assert is_five_power(radix_bits) and is_five_power(L) and is_five_power(d)
    cc=Compiled(windows,a,A,coeff,mu,padding,m,positions,payload,dummy,anchors,
                anchor_unit,H,T1,T2,L,R,radix_bits,d,DCpoly,MFpoly)
    cc.high_correction=high_correction;cc.high_degree=high_degree
    cc.old_unit_mod5=old_unit;cc.unit_mod5=unit
    return cc


def verify_compiler(cc):
    result=previous.previous.verify_compiler(cc)
    K=len(cc.positions);E=max(cc.positions)
    assert K*(2*sum(cc.coeff.values())+6)<=cc.R//2-2
    assert cc.dummy and all(e not in cc.coeff for e in cc.dummy)
    assert len(cc.positions)==cc.m+1
    assert cc.high_degree>max(cc.MFpoly) and cc.high_degree+E<cc.L
    # Every optional-high-term/native-bit product lies above every test.
    high_checks=0
    for e in cc.positions:
        assert cc.high_degree+e not in cc.MFpoly
        assert cc.high_degree+e<cc.L;high_checks+=1
    # Native mask population and parity without allocating 2^d.
    allowed=[e for e in cc.positions if e!=1]
    assert len(allowed)==cc.m and 0 in allowed and 1 not in allowed
    assert min(cc.MFpoly)>0 and cc.d-cc.m>0
    dcmod=sum(c*pow(2,e,5) for e,c in cc.DCpoly.items())%5
    assert (2*dcmod-pow(2,cc.H,5))%5==cc.unit_mod5!=0
    # q=B^N and P0=B^h are2 mod5 for powers-of-five d,N,h.
    assert (1+2*(dcmod+2*pow(2,cc.H,5)+2))%5==cc.unit_mod5
    result.update(inner_bits_power_five=cc.radix_bits,cell_length_power_five=cc.L,
                  cell_bits_power_five=cc.d,high_correction=cc.high_correction,
                  high_degree=cc.high_degree,high_term_basis_checks=high_checks,
                  previous_unit_mod5=cc.old_unit_mod5,unit_mod5=cc.unit_mod5,
                  guaranteed_control_dummy=cc.dummy[0],native_mask_even=True,
                  full_mask_population=cc.d,
                  materialized_packed_word=False)
    return result


def verify_control_identities():
    q,B,hpow,Rpow,C,F,W,MC,MF,J,slot=sp.symbols('q B hpow Rpow C F W MC MF J slot')
    DC,DR=sp.symbols('DC DR')
    packed=lambda c,f:(q*q-(c-W)-q*f)*(q*q-1)+(MC+q*MF)*J
    change=sp.expand(packed(C+Rpow*slot,F+(DC+B*DR+hpow)*Rpow*slot)-packed(C,F))
    gamma=Rpow*(q*q-1)*(1+q*(DC+B*DR+hpow))
    assert sp.expand(change+gamma*slot)==0
    X,z,t=sp.symbols('X z t')
    old=(DC+B*DR+hpow)*C-F-z*(q-1)
    new=(DC+B*DR+X)*C-F-(z+t*C)*(q-1)
    assert sp.expand((new-old).subs(X,hpow+t*(q-1)))==0
    ranges=[]
    for h in (1,5,25,125):
        for H in (25,125,625):
            N=h*H;maximum=4*(N//5-1)
            assert maximum+1<N and maximum+h<N and 1+h<N
            assert 1 not in range(0,maximum+1,4)
            ranges.append(dict(width=h,height=H,N=N,maximum_control_cell=maximum))
    return dict(exact_symbolic_dummy_change=sp.sstr(change),
                factor_gamma=sp.sstr(gamma),transport_quotient_identity=True,
                internal_slot_ranges=ranges,
                scope='Identities and slot geometry; no full compiler word or Pell power materialized')


def verify_doubled_bridge():
    records=[]
    for b,L in ((1,1),(1,5),(5,1),(5,5)):
        d=b*L
        for x in (1,2,3):
            u=2*d*x+b;W=2**u;a=2**(u+3);A=a+2;Delta=A*A-1
            mu,kappa=previous.pell(A,u);_,c=previous.pell(A,u+2)
            delta,rem=divmod(kappa-u,Delta);assert rem==0 and delta>0
            rho,rem=divmod(mu-a*kappa-W,4*a+3);assert rem==0 and rho>0
            phi=c-kappa;assert phi>0 and u%2==1 and d%2==1
            assert mu*mu==1+Delta*kappa*kappa
            assert kappa==2*d*x+b+delta*Delta
            assert c==kappa+phi and mu==W+a*kappa+rho*(4*a+3)
            assert W==2**b*(2**d)**(2*x)
            records.append(dict(b=b,L=L,d=d,x=x,actual_index=u,positive=True))
    return dict(positive_doubled_input_cases=len(records),examples=records,
                scope='Exact bridge tuples with odd power-of-five cell widths; not asserted to be full packed kernels')


def verify():
    alphabets=[([(0,)*9,(1,)*9],2),
               ([previous.previous.previous.cyclic_window([1,0,0],i,1) for i in range(3)],2),
               (list(product(range(2),repeat=9))[:100],2),
               ([(0,)*9,(1,)*9,(2,)*9],3),
               (list(product(range(2),repeat=9))[:3],2)]
    compilers=[verify_compiler(compile_windows(windows,a)) for windows,a in alphabets]
    # The correction branch is fixed-compiler dependent, never input dependent.
    corrections={record['high_correction'] for record in compilers}
    assert corrections=={0,1}
    import explore_five_adic_dummy_control as control
    control_result=control.verify()
    control_saved=json.loads(Path(control.__file__).with_suffix('.json').read_text(encoding='utf-8'))
    assert json.loads(json.dumps(control_result))==control_saved
    return dict(status='PASS_FIXED_RAW_UNIVERSAL76',source=verify_source(),
                compilers=compilers,control_identities=verify_control_identities(),
                delta_bridge=previous.verify_delta_bridge(),
                doubled_input_bridge=verify_doubled_bridge(),
                five_adic_dependency=control_result,
                proof='../1980/FIXED_RAW_UNIVERSAL_76_PROOF.md',
                review='Author and two independent complete proof/source reviews pass; fresh exact receipt checks pass',
                scope='Complete fixed-index raw-input certificate. Full padding and positive Pell witnesses are proved parametrically; finite evidence is symbolic, sparse and modular, not a materialized astronomical full tuple.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true')
    args=parser.parse_args();result=verify();receipt=Path(__file__).with_suffix('.json')
    normalized=json.loads(json.dumps(result))
    if args.write:receipt.write_text(json.dumps(normalized,indent=2)+'\n',encoding='utf-8')
    else:assert normalized==json.loads(receipt.read_text(encoding='utf-8'))
    print(result['status'],result['source']['operations'],result['source']['multiplications'],result['source']['additions_subtractions'])
    print(result['compilers'])
