"""A positive supplied q-F coordinate does not recover the old F bound.

The literal86 candidate has complete positive zeros at an explicit scalar
mask contract with R>q^4, C=0 and negative input Pell root.  No actual
compiled program or false-membership assertion is supplied.
"""
import argparse
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from math import gcd,lcm
import json
from pathlib import Path
import random
import sympy as sp

import complete75_normalized_strong87 as parent
import complete75_weakened86_infinite_outer_family as intervals
from complete75_weakened86_auxiliary_sign_lift import pell_mod

P0=27689153732231122698612582020560843427585236025554359211783055917956507500708943
STEP=316199877967503874326528000
CONCRETE_P=27689153732231122698612582020560843428479406560240872014501246148159455756452943
CONCRETE_N=18909695711339583511386628105482078268425333847339916462699118496112267748786728
CONCRETE_T=2827864894933348


@lru_cache(None)
def sources():
    _,old,pairs,_=parent.sources()
    assert [r for r in old if r[0]=='q_minus_F']==[('q_minus_F','-','q','F')]
    assert [n for n,_,a,b in old if 'F' in (a,b)]==['q_minus_F']
    alias=lambda v:'F' if v=='q_minus_F' else v
    rows=[(n,op,alias(a),alias(b)) for n,op,a,b in old if n!='q_minus_F']
    polynomial=rows+[('polynomial','-','eight_units',1)]
    assert len(rows)==85 and len(polynomial)==86
    assert Counter('M' if op=='*' else 'A' for _,op,_,_ in polynomial)=={'M':48,'A':38}
    free=set(parent.RETAINED+parent.eliminated.baseline.prior.CONSTANTS+['x','Bm1','Kconstant','twice_cell_bits'])
    for n,op,a,b in rows:
        assert n not in free and op in ('+','-','*')
        assert all(type(v)is int or v in free for v in (a,b));free.add(n)
    nodes={n:(a,b) for n,_,a,b in polynomial};needed=set();todo=['polynomial']
    while todo:
        n=todo.pop()
        if isinstance(n,str) and n in nodes and n not in needed:
            needed.add(n);todo.extend(nodes[n])
    assert needed==set(nodes)
    return rows,pairs,polynomial


def source_identity_audit():
    rng=random.Random(860025);rows,pairs,poly=sources();old=parent.sources()[3];counts=Counter()
    for case in range(384):
        signed=case>=192;draw=lambda:rng.randrange(-7,8) if signed else rng.randrange(1,10)
        v={n:draw() for n in parent.RETAINED+['x']}
        B=(16,32,128,256)[case%4]
        v.update(B=B,DC=3,DR=5,MC=B-2,MF=4,cell_bits=B.bit_length()-1,inner_bits=3)
        q=(B-1)*v['Jrep']+1
        if case<48:v['F']=q+case+1
        restored=dict(v,F=q-v['F'])
        a=parent.eliminated.run(poly,parent.eliminated.fixed_inputs(v))
        b=parent.eliminated.run(old,parent.eliminated.fixed_inputs(restored))
        assert a['polynomial']==b['polynomial']
        assert all(a[n]==b[n] for n,_,_,_ in rows)
        assert b['q_minus_F']==v['F']
        counts['complete_register_factor_output_identities']+=1;counts['signed_assignments']+=signed
        counts['positive_new_assignments_nonpositive_old_F']+=not signed and restored['F']<=0
    return dict(certificate=dict(operations=85,multiplications=48,additions_subtractions=37,equations=1,witnesses=19),
        polynomial=dict(operations=86,multiplications=48,additions_subtractions=38,degree=203,witnesses=19),
        retained_coordinates=parent.RETAINED,comparisons=pairs,source=poly,checks=dict(counts),
        coordinate_meaning='The supplied F now denotes QF=q-F_old; exact inverse F_old=q-F may be negative.')


def degree_audit():
    z=sp.Symbol('z');records=[]
    for B,shift in ((16,0),(128,1)):
        slopes={n:1+(j+shift)%4 for j,n in enumerate(parent.RETAINED+['x'])}
        slopes.update(tau_gap=7,eta=1,zeta=2,F=3,Z=1,alpha=1,x=1)
        vals={n:sp.Poly(slopes[n]*z+j+1,z) for j,n in enumerate(parent.RETAINED+['x'])}
        d=B.bit_length()-1
        fixed=dict(B=B,DC=3,DR=5,MC=B-2,MF=4,cell_bits=d,inner_bits=3)
        e=parent.eliminated.run(sources()[2],parent.eliminated.fixed_inputs(dict(vals,**fixed)))
        degrees=[sp.Poly(e[n],z).degree() for n in parent.FACTOR_NAMES]
        assert degrees==list(parent.FACTOR_DEGREES)
        Q=(B-1)*slopes['Jrep'];k=slopes['eta']+slopes['zeta'];C=slopes['F']-slopes['Z']-slopes['alpha']-2*d*slopes['x']
        top=32*Q**135*slopes['h']**2*(slopes['rho']+slopes['sigma'])*slopes['delta']**2*slopes['i']**4*k**12*slopes['w']**17*slopes['s']**28*C*(2*slopes['tau_gap']-k)
        actual=sp.Poly(e['polynomial'],z)
        assert actual.degree()==203 and top and actual.LC()==top
        records.append(dict(B=B,factor_degrees=degrees,degree=203,leading_coefficient=str(top)))
    return dict(fixtures=records,highest_form='Parent normalized87 highest form with C_top=F-Z-alpha-2*d*x; no q term in C_top.')


def seed():
    q,B,d,x,b,MC,MF=16,16,4,1,1,6,12
    X,Y,alpha=32768,4096,3;E=X*Y;a=Y*(X+1);A=a+2;H=4*a+3;Delta=A*A-1;P=2*X*Y*Y+1
    M=q*q-1;u=2*d*x+b;U=alpha+2*d*x;mask=MC+q*(MF+B-1)
    chi_v,psi_v=parent.pell(A,u);Fv=chi_v+a*psi_v
    delta,rem=divmod(psi_v-u,Delta);assert rem==0 and delta>0
    T=2753268;assert pow(2,T,H)==1
    rho0=2;Z0=Fv+H*rho0
    assert (Z0+U-1)%(q-1)==0
    assert gcd(H,q-1)==3
    raw_step=M*(q-1)*H*((q-1)//3)
    R0=M*((q-1)*Z0+q*U)+mask
    common=gcd(T,raw_step);assert common==3 and (15-R0)%common==0
    z0=((15-R0)//common)*pow(raw_step//common,-1,T//common)%(T//common)
    p0=R0+raw_step*z0;step=lcm(T,raw_step,E,4);N=E//2;n0=((p0+1)//2)%N
    assert p0==P0 and step==STEP and z0==143215 and n0==14238248
    assert p0%4==3 and p0>max(q**4,2*X) and P%E==1
    assert A<P<2*A*A-1 and (P*P-1)&-(P*P-1)==2**41
    assert MC%4==2 and MF%8==4 and MC.bit_count()+MF.bit_count()==d and max(MC,MF)<B-1
    return dict(q=q,B=B,cell_bits=d,input=x,inner_bits=b,MC=MC,MF=MF,X=X,Y=Y,E=E,a=a,A=A,H=H,Delta=Delta,P=P,M=M,
        alpha=alpha,U=U,mask=mask,input_index=u,input_chi=chi_v,input_psi=psi_v,Fv=Fv,delta=delta,
        main_return_period=T,rho0=rho0,Z0=Z0,R0=R0,raw_step=raw_step,crt_gcd=common,crt_index=z0,
        p0=p0,step=step,n_modulus=N,n_residue=n0)


def progression_audit(d):
    rng=random.Random(861516);counts=Counter()
    for t in [0,1,2,CONCRETE_T]+[rng.randrange(10**40) for _ in range(124)]:
        p=d['p0']+d['step']*t
        Z,rem=divmod(p-d['mask']-d['M']*d['q']*d['U'],d['M']*(d['q']-1));assert rem==0
        rho,rem=divmod(Z-d['Fv'],d['H']);assert rem==0 and rho>=2
        zplus,rem=divmod(Z+d['U']-1,d['q']-1);assert rem==0 and zplus>0
        assert p%4==3 and p>d['q']**4 and 0<rho*d['H']<Z<p
        assert pow(2,p,d['H'])==d['X']
        assert (2*d['n_residue']-p-1)%d['E']==0
        n=d['n_residue']+d['n_modulus']*(t+1)
        assert pell_mod(d['P'],n,d['E'])[1]==n%d['E']
        assert Z+d['U']>d['q']
        counts['complete_modular_progression_cases']+=1
    # These are independent inequality fixtures, not claimed complete zeros.
    for A in (3,4,7,19,d['A']):
      for p in range(2,35):
        chi,c=parent.pell(A,p);prev=parent.pell(A,p-1)[1]
        assert c>=2*p and chi-(A-2)*c==2*c-prev>c
        counts['linear_vs_Pell_growth_cases']+=1
    return dict(counts)


def concrete_certificate(d,bits):
    p,n=CONCRETE_P,CONCRETE_N
    assert p==d['p0']+d['step']*CONCRETE_T
    assert n%d['n_modulus']==d['n_residue'] and n<p<2*n and p%4==3
    ar=intervals.IntegerIntervals(bits)
    c=ar.pell(d['A'],p)[1];k=ar.mul(ar.exact(2),ar.pell(d['P'],n)[1])
    lo=ar.mul(k,ar.exact(d['Y']));hi=ar.mul(k,ar.exact(d['Y']+1))
    assert ar.compare(c[0],lo[1])>0 and ar.compare(c[1],hi[0])<0
    cbits=c[0][0].bit_length()+c[0][1];assert cbits==c[1][0].bit_length()+c[1][1]
    return dict(precision_bits=bits,p=p,n=n,progression_index=CONCRETE_T,c_interval=c,kY_interval=lo,kY_plus_k_interval=hi,
        exact_c_bit_length=cbits,both_strict_ratios_certified=True,
        scope='Integer interval certificate for exact Pell recipes; the huge Pell coordinates are not materialized.')


def divide(a,b):
    return a/b if isinstance(a,sp.Basic) or isinstance(b,sp.Basic) else Fraction(a)/Fraction(b)


def mapped_values(d,p,c,k,first_root,main_root,f,i,V,y,DC=3,DR=5):
    Z=divide(p-d['mask']-d['M']*d['q']*d['U'],d['M']*(d['q']-1))
    rho=divide(Z-d['Fv'],d['H']);gamma=divide(main_root-d['a']*c-d['X'],d['H'])
    return dict(Jrep=1,F=Z+d['U'],alpha=d['alpha'],zplus=divide(Z+d['U']-1,d['q']-1),
        f=f,h=divide(k-p-1,d['E']),i=i,j=divide(V+p,c),o=divide(V+c,f),s=1,w=8,
        tau_gap=first_root-d['X']*d['Y']**2*k,eta=c-k*d['Y'],zeta=k*(d['Y']+1)-c,
        y_aux=y,Z=Z,delta=d['delta'],rho=rho,sigma=gamma-rho,
        x=1,B=16,DC=DC,DR=DR,MC=6,MF=12,cell_bits=4,inner_bits=1)


def full_family_source_audit(d):
    p,c,k,U,D,f,i,V,y,DC,DR=sp.symbols('p c k U D f i V y DC DR',nonzero=True)
    values=mapped_values(d,p,c,k,U,D,f,i,V,y,DC,DR)
    env=parent.eliminated.run(sources()[2],parent.eliminated.fixed_inputs(values));Delta=d['Delta'];L=d['X']*d['Y']**2
    expected=dict(norm_first=U*U-L*(L+1)*k*k,norm_main=D*D-Delta*c*c,norm_input=sp.Integer(1),
        norm_aux=Delta**2*i*i*c**4*(V*V-y*y)+y*y,norm_index=sp.Integer(1),norm_transport=sp.Integer(1),
        norm_strong=f*f-Delta*i*i*c**4,norm_linear=sp.Integer(1))
    for name,want in expected.items():assert sp.cancel(env[name]-want)==0,name
    assert sp.cancel(env['marked_rhs'])==0 and sp.cancel(env['r_lhs']-p)==0
    assert sp.cancel(env['exponent_rhs']+d['input_chi'])==0
    assert sp.cancel(env['index_rhs']-d['input_psi'])==0
    assert sp.cancel(env['polynomial']-(sp.prod(expected[n] for n in parent.FACTOR_NAMES)-1))==0
    rng=random.Random(864855);counts=Counter()
    for signed in (False,True):
      for _ in range(96):
        nums=[rng.randrange(1,8)*(-1 if signed and rng.randrange(2) else 1) for _ in range(9)]
        pp,cc,kk,uu,dd,ff,ii,vv,yy=nums
        vals=mapped_values(d,*nums);rational=mapped_values(d,*map(Fraction,nums))
        assert vals==rational and not any(isinstance(v,float) for v in vals.values())
        actual=parent.eliminated.run(sources()[2],parent.eliminated.fixed_inputs(vals))
        scalar=[uu*uu-L*(L+1)*kk*kk,dd*dd-Delta*cc*cc,1,Delta**2*ii*ii*cc**4*(vv*vv-yy*yy)+yy*yy,
                1,1,ff*ff-Delta*ii*ii*cc**4,1]
        assert [actual[n] for n in parent.FACTOR_NAMES]==scalar
        product=1
        for v in scalar:product*=v
        assert actual['polynomial']==product-1
        counts['formal_full_source_factor_output_maps']+=1;counts['signed_maps']+=signed
    return dict(all_eight_symbolic_factor_identities=True,complete_symbolic_output_identity=True,
        source_zero_factors=[1]*8,checks=dict(counts),
        scope='Arbitrary exact rational identities corroborate the full source map; positive integer full zeros follow from the theorem and canonical auxiliary lift.')


def verify():
    d=seed();certificates=[concrete_certificate(d,bits) for bits in (384,512)]
    for key in ('c_interval','kY_interval','kY_plus_k_interval'):
        assert intervals.IntegerIntervals.compare(certificates[1][key][0],certificates[0][key][0])>=0
        assert intervals.IntegerIntervals.compare(certificates[1][key][1],certificates[0][key][1])<=0
    return dict(status='PASS_POSITIVE_COMPLEMENT86_SCALAR_OBSTRUCTION',source=source_identity_audit(),degree=degree_audit(),
        seed=d,progressions=progression_audit(d),concrete_certificates=certificates,full_source=full_family_source_audit(d),
        witness_recipe=dict(p='p0+step*t',n='n_residue mod E/2, satisfying the two strict Pell ratios',c='psi_A(p)',k='2*psi_P(n)',
            Z='(p-mask-M*q*(alpha+2d*x))/(M*(q-1))',F_new='Z+alpha+2d*x',rho='(Z-Fv)/H',
            gamma='(chi_A(p)-a*c-X)/H',sigma='gamma-rho',auxiliary='m=2*c*p, f=chi_A(m), i=psi_A(m)/c^2; T=Delta*psi_A(m); V=chi_T(p)/T, y=psi_T(p), j=(V+p)/c, o=(V+c)/f'),
        theorem='Explicit scalar-mask-contract candidate86 has infinitely many full positive19-coordinate zeros with all eight factors1, R>q^4, C=0 and negative input root; the exact restored old F is negative.',
        limitations='No actual universal program or false-membership input is instantiated. This refutes automatic positive restoration of F and the claimed inherited bound, not all86 circuits or by itself the candidate accepted-language theorem.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['source']['polynomial'])
