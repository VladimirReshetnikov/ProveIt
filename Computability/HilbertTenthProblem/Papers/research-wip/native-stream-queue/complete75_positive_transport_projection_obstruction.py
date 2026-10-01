"""Exact87 positive-C projection; full all-input obstruction proved in the note.
Finite outer checks never materialize X=2**R or the strong auxiliary tower.
"""
import argparse
from collections import Counter
from math import comb,lcm
import json
from pathlib import Path
import random
import complete75_coupled_index_linear88 as parent

RETAINED=['Cpositive' if n=='F' else n for n in parent.RETAINED]
eliminated=parent.eliminated


def sources():
    _,old,pairs,_=parent.sources();nodes={n:(op,a,b) for n,op,a,b in old}
    assert nodes.pop('marked_rhs')==('-','C_after_alpha','scaled_t')
    assert nodes['q_minus_F']==('-','q','F')
    assert nodes['q_minus_FZ']==('-','q_minus_F','Z')
    assert nodes['C_after_alpha']==('-','q_minus_FZ','alpha')
    nodes['C_after_alpha']=('+','Cpositive','scaled_t')
    nodes['q_minus_FZ']=('+','C_after_alpha','alpha')
    nodes['q_minus_F']=('+','q_minus_FZ','Z')
    alias=lambda a:'Cpositive' if a=='marked_rhs' else a
    nodes={n:(op,alias(a),alias(b)) for n,(op,a,b) in nodes.items()}
    done=set(RETAINED+eliminated.baseline.prior.CONSTANTS+['x','Bm1','Kconstant','twice_cell_bits'])
    active,source=set(),[]
    def visit(n):
        if isinstance(n,int) or n in done:return
        assert n not in active
        active.add(n);op,a,b=nodes[n];visit(a);visit(b)
        source.append((n,op,a,b));active.remove(n);done.add(n)
    for a,b in pairs:visit(a);visit(b)
    assert len(source)==len(nodes)==86
    return source,pairs,source+[('polynomial','-','eight_units',1)]


def period_scale(d):
    t=1
    for j in range(1,d+1):t=lcm(t,j)
    D=t
    while D%2==0:D//=2
    while t//D<8:t*=2
    M=t//D
    assert t%d==0 and M>=8 and M&(M-1)==0 and pow(2,t,D)==1%D
    return t,D,M


def outer(x,d,b,MC,MF,DC,DR):
    assert x>0 and d>=4 and b>=1 and b%2
    B,K0=1<<d,DC+(1<<d)*DR
    assert 0<MC<B-1 and 0<MF<B-1 and K0>0
    t,D,M=period_scale(d);q=1<<t;J=(q-1)//(B-1)
    assert (B-1)*J+1==q
    mask=(MC+q*(MF+B-1))*J
    eD=(MC+MF+B-1)*J%D
    e=next(eD+D*j for j in range(4) if (eD+D*j)%4==3)
    assert 0<e<4*D<t
    Z=q+(e-MC*J-1)%M+1
    u=2*d*x+b;W=1<<u;C=W+Z
    ar=1-(K0+(1<<e))*C-C-Z-2*d*x
    alpha0=(ar-1)%(q-1)+1
    F0=q-C-Z-alpha0-2*d*x
    R0=(q*q-Z-q*F0)*(q*q-1)+mask
    stride=q*(q*q-1)*(q-1)
    assert stride%t==0 and R0%t==e and F0<0
    L0=R0//stride+1;deficit=stride*L0-R0
    assert 0<deficit<=stride
    threshold=max(u,3*q+1,3*t,e)
    N=max(3*t+2+(deficit-1).bit_count(),deficit.bit_length()+1,
          L0.bit_length()+1,threshold.bit_length()+1)
    L=(1<<N)-L0;alpha=alpha0+(q-1)*L
    F=q-C-Z-alpha-2*d*x
    R=(q*q-Z-q*F)*(q*q-1)+mask
    assert L>0 and R==stride*(1<<N)-deficit==R0+stride*L
    assert R.bit_count()==(stride-1).bit_count()+N-(deficit-1).bit_count()
    assert R.bit_count()>=3*t+2 and R%4==3 and R%t==e and R>threshold
    assert min(q,J,C,Z,alpha)>0 and F<0 and C-Z==W
    assert pow(2,R,q-1)==1<<e
    reduced=(K0+(1<<e))*C+q-F-1
    assert reduced%(q-1)==0 and reduced>0
    return locals()


def pell(A,n):
    D=A*A-1;x,y,a,b=1,0,A,1
    while n:
        if n&1:x,y=x*a+D*y*b,x*b+y*a
        a,b=a*a+D*b*b,2*a*b;n//=2
    return x,y


def fresh_main(R):
    assert R>=7 and R%4==3
    r,X=(R-1)//2,1<<R
    numerator=sum(comb(2*r,r+j)*X**j for j in range(r+1))
    assert numerator%2==0
    Y=numerator//2;E,a=X*Y,Y*(X+1);A,H=a+2,4*a+3
    root,c=pell(A,R);tau,halfk=pell(2*X*Y*Y+1,r+1);k=2*halfk
    eta=c-k*Y;zeta=k-eta
    h,rem=divmod(k-R-1,E);assert rem==0
    gamma,rem=divmod(root-X-a*c,H);assert rem==0
    gap=tau-X*Y*Y*k
    assert min(Y,eta,zeta,h,gamma,gap)>0
    assert gap*gap+E*(k*Y)*(2*gap-k)==1 and root*root-(A*A-1)*c*c==1
    assert (Y&-Y).bit_length()-1==r.bit_count()-1
    return locals()


def source_checks():
    source,pairs,poly=sources();old=parent.sources()[3]
    rng=random.Random(87147);negative=0
    for case in range(512):
        v={n:rng.randrange(1,9) if case<384 else rng.randrange(-8,9) for n in RETAINED+['x']}
        B=rng.choice((16,32,64,256));d=B.bit_length()-1
        fixed=dict(B=B,DC=3,DR=5,MC=B-2,MF=4,cell_bits=d,inner_bits=3)
        q=(B-1)*v['Jrep']+1
        restored={n:a for n,a in v.items() if n!='Cpositive'}
        restored['F']=q-v['Cpositive']-v['Z']-v['alpha']-2*d*v['x']
        a=eliminated.run(poly,eliminated.fixed_inputs({**v,**fixed}))
        b=eliminated.run(old,eliminated.fixed_inputs({**restored,**fixed}))
        assert all(a[n]==b[n] for n,_,_,_ in source)
        assert a['Cpositive']==b['marked_rhs'] and a['polynomial']==b['polynomial']
        negative+=restored['F']<=0
    counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in poly)
    assert counts=={'M':47,'A':40}
    return dict(certificate_operations=len(source),polynomial_operations=len(poly),
        multiplications=47,additions_subtractions=40,positive_witnesses=19,
        comparisons=pairs,polynomial_schedule=poly,source_identities=512,
        nonpositive_restored_F=negative,coordinate_map='F_old=q-Cpositive-Z-alpha-2*d*x')


def verify():
    periods=[(d,*period_scale(d)) for d in range(4,97)];fixtures=[]
    for d in (4,5,6,7,8):
      for MC,MF in (((1<<d)-2,4),((1<<d)-6,12)):
       for x in (1,2,5):
        p=outer(x,d,3,MC,MF,3,5)
        assert MC%4==2 and MF%8==4 and MC.bit_count()+MF.bit_count()==d
        fixtures.append(dict(x=x,d=d,MC=MC,MF=MF,t=p['t'],e=p['e'],
            R_bits=p['R'].bit_length(),R_population=p['R'].bit_count(),
            required_population=3*p['t']+2,alpha_bits=p['alpha'].bit_length(),
            F_negative=p['F']<0,outer_congruences=True,full_Pell_tower_materialized=False))
    mains=[];inputs=0
    for R in (7,11,15,19,23,27,31,35):
        p=fresh_main(R)
        for u in range(3,R,2):
            mu,kappa=pell(p['A'],u)
            delta,rem=divmod(kappa-u,p['A']*p['A']-1);assert rem==0
            rho,rem=divmod(mu-p['a']*kappa-(1<<u),p['H']);assert rem==0
            sigma=p['gamma']-rho
            assert min(delta,rho,sigma)>0 and mu==(1<<u)+p['a']*kappa+rho*p['H']
            inputs+=1
        mains.append(dict(R=R,main_bits=p['c'].bit_length(),both_ratios=True,
                          valuation=p['r'].bit_count()-1))
    p=fresh_main(31)
    assert 31>2**4 and p['X']%8==p['Y']%8==0
    auxiliary=[]
    for A,R in ((3,3),(4,3),(5,3),(6,3),(2,7)):
        _,c=pell(A,R);D=A*A-1;m=2*c*R;f,psi=pell(A,m);T=D*psi
        i,rem=divmod(T,c*c);assert rem==0 and i>0
        chi,y=pell(T,R);V,rem=divmod(chi,T);assert rem==0
        o,rem=divmod(V+c,f);assert rem==0
        j,rem=divmod(V+R,c);assert rem==0
        assert min(o,j,y)>0 and T*T==D*(f*f-1)
        assert T*T*(V*V-y*y)+y*y==1 and V==o*f-c==j*c-R
        auxiliary.append(dict(A=A,R=R,m=m,root_bits=V.bit_length()))
    return dict(status='PASS_POSITIVE_C_PROJECTION_ALL_INPUT_OBSTRUCTION',
        source=source_checks(),period_scales=periods,outer_fixtures=fixtures,
        fresh_half_binomial_cases=mains,positive_input_splits=inputs,
        canonical_auxiliary_cases=auxiliary,
        scope='Exact87 rewrite rejected by full parametric positive all-input theorem; finite masks are not claimed to encode histories.',
        compiler_scope='Every actual fixed complete75 compiler; its constants remain fixed independently of x.')


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true')
    args=parser.parse_args();result=verify();path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==json.loads(json.dumps(result))
    print(result['status'])
    print('87=47M+40A;512 source identities;',len(result['outer_fixtures']),'outer fixtures;',result['positive_input_splits'],'input splits')

if __name__=='__main__':main()
