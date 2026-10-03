"""Reject the same-cost U=j*(i*c^2)-J repair of the weakened kernel."""
import argparse
import json
from math import gcd
from pathlib import Path
import sympy as sp
import explore_pell_kernel_squared_congruence as prior
import explore_dyadic_balanced_wrong_index as balanced

weak=prior.weakened
pell=prior.pell_power


def source_audit():
    old=weak.previous
    rows=[(name,op,left,'ic2' if name=='jc' else right)
          for name,op,left,right in weak.SCHEDULE]
    c,i,j,r,y=(old.SYM[n] for n in ('c','i','j','r','y_aux'))
    sources=[sp.expand(source.subs(j,j*i*c)) for source in weak.source_residuals()]
    env=old.fixed_environment(old.SYM)
    bridge=old.previous.previous.previous.previous.bridge
    bridge.baseline.run_schedule(rows,env)
    U=j*i*c*c-2*r-1;correction=sources[12]*(U*U-y*y)
    records=[]
    for ix,((left,right),source) in enumerate(zip(weak.EQUALITIES,sources)):
        actual=sp.expand(env[left]-env[right]);adjust=correction if ix==13 else 0
        sign=1 if sp.expand(actual-source-adjust)==0 else -1
        assert sp.expand(actual-sign*source-adjust)==0,ix
        records.append(dict(index=ix,equality=[left,right],source_sign=sign,
                            source=str(source),correction=str(sp.expand(adjust))))
    primitives,counts=bridge.verify_primitives(rows,env)
    assert len(primitives)==75 and counts=={'*':40,'+':35}
    assert [ix for ix,(a,b) in enumerate(zip(sources,weak.source_residuals())) if a!=b]==[13,14]
    positions={row[0]:ix for ix,row in enumerate(rows)}
    assert positions['ic2']<positions['jc']
    return dict(operations=75,multiplications=40,additions_subtractions=35,
                equations=19,positive_coordinates=len(weak.NAMES),
                changed_instruction=['jc','*','j','ic2'],acyclic=True,
                primitive_instructions=primitives,sources=records,
                scope='Exact source only; no complete75 soundness or false-input claim')


def parameters(A,p,J):
    d,c=pell(A,p);Delta=A*A-1
    f=2*d*d-1;R=2*Delta*c*d;K=R*R;i=4*Delta*Delta*d*d
    sigma=(-1)**((p-1)//2);g=gcd(p,K)
    assert A>=2 and p>=3 and p%2==J%2==1 and 0<J<c
    assert K%16==0 and gcd(4*p,K)==4*g
    assert J%g==0 and (J-p-1-sigma)%8==0
    rhs=-sigma*J-p;modulus=K//(4*g)
    assert rhs%(4*g)==0 and modulus%4==0
    t=(rhs//(4*g))*pow(p//g,-1,modulus)%modulus
    s=p+4*p*t
    assert (sigma*s+J)%K==0 and (-1)**t==-sigma
    assert K==i*c*c==Delta*(f*f-1) and R>f>2*c
    if c.bit_length()<4096:
        assert weak.q_mod(K,(s-1)//2,K)==-J%K
        assert weak.q_mod(K,(s-1)//2,f)==-c%f
    return dict(A=A,p=p,J=J,d=d,c=c,Delta=Delta,f=f,R=R,K=K,i=i,
                sigma=sigma,g=g,modulus=modulus,t=t,s=s)


def criterion_audit():
    admitted=excluded=parity_excluded=0
    for A in range(2,10):
        for p in range(3,16,2):
            d,c=pell(A,p);Delta=A*A-1;K=(2*Delta*c*d)**2
            sigma=(-1)**((p-1)//2);g=gcd(p,K)
            for J in range(3,min(c,34),2):
                wanted=J%g==0 and (J-p-1-sigma)%8==0
                rhs=-sigma*J-p;divisor=gcd(4*p,K)
                if rhs%divisor:
                    actual=False
                else:
                    modulus=K//divisor
                    t=(rhs//divisor)*pow(4*p//divisor,-1,modulus)%modulus
                    actual=(-1)**t==-sigma
                    parity_excluded+=not actual
                assert actual==wanted
                if wanted:parameters(A,p,J);admitted+=1
                else:excluded+=1
    materialized=[]
    for A,p,J in ((4,3,27),(2,7,63)):
        z=parameters(A,p,J);assert z['t']==2 and z['s']==J and p!=J
        chi,y=pell(z['R'],z['s']);U,rem=divmod(chi,z['R'])
        j,jrem=divmod(U+J,z['K']);o,orem=divmod(U+z['c'],z['f'])
        assert rem==jrem==orem==0 and min(U,y,j,o)>0
        assert U==j*z['K']-J==o*z['f']-z['c']
        assert z['K']*(U*U-y*y)==1-y*y
        materialized.append(dict(A=A,p=p,J=J,t=z['t'],auxiliary_index=z['s'],
                                 U_bits=U.bit_length(),all_repaired_auxiliary_equations=True))
    return dict(admitted=admitted,excluded=excluded,parity_only_exclusions=parity_excluded,
                criterion='gcd(p,K)|J and J=p+1+(-1)^((p-1)/2) mod8',materialized=materialized)


def primary_attachment():
    main=balanced.check_case(59,211,16)
    p,J=329,539;X,Y=1<<329,1<<91;a=Y*(X+1);A=a+2
    z=parameters(A,p,J)
    assert gcd(p,z['c'])==gcd(p,z['Delta'])==gcd(p,z['d'])==1
    assert z['K']%32==16 and z['t']%2==1
    u,W=3,8;mu,kappa=pell(A,u)
    delta,rem1=divmod(kappa-u,z['Delta'])
    rho,rem2=divmod(mu-a*kappa-W,4*a+3);phi=z['c']-kappa
    assert rem1==rem2==0 and min(delta,rho,phi)>0
    assert mu*mu==1+z['Delta']*kappa*kappa
    return dict(q=16,r=269,intended_index=J,actual_index=p,
                seven_main_equations=main['seven_nonauxiliary_residuals'],
                all_main_coordinates_positive=main['all_nonauxiliary_coordinates_positive'],
                gcd_p_c_Delta_d=1,K_bits=z['K'].bit_length(),
                CRT_modulus_bits=z['modulus'].bit_length(),t_bits=z['t'].bit_length(),
                auxiliary_index_bits=z['s'].bit_length(),t_odd=True,
                whole_coefficient_congruence=True,auxiliary_outputs_materialized=False,
                actual_binomial_valuation=main['binomial_two_adic_valuation'],
                required_valuation=main['required_valuation'],
                numerical_bridge=dict(u=u,W=W,all_four_equations=True),
                scope='Full wrong-index kernel and numerical bridge; no actual compiled outer witness')


def verify():
    return dict(status='PASS_WHOLE_COEFFICIENT_CONGRUENCE_REPAIR_REFUTATION',
                source=source_audit(),criterion=criterion_audit(),primary=primary_attachment(),
                canonical_complete76_completeness='Preserved parametrically via Q_J(K)=-J modK and j=(U+J)/K',
                established_complete_universal_bound=76,original_full75_soundness='OPEN')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=verify();path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(json.dumps(dict(status=result['status'],criterion=result['criterion'],primary=result['primary']),indent=2))
