"""Complete universal87: normalize the strong auxiliary coefficient.

The positive input projection is unchanged; completeness reconstructs the
five canonical auxiliary coordinates rather than inverting every old tuple.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import random
import sympy as sp
import complete75_coupled_index_linear88 as parent

eliminated=parent.eliminated
RETAINED=parent.RETAINED
FACTOR_NAMES=parent.FACTOR_NAMES
FACTOR_DEGREES=(14,22,42,64,9,5,38,9)


def sources():
    original,old,pairs,_=parent.sources()
    nodes={n:(op,a,b) for n,op,a,b in old}
    assert nodes.pop('f_square_minus_one')==('-','L16',1)
    assert nodes['R16']==('*','A','f_square_minus_one')
    assert nodes['strong_difference']==('-','ic22','R16')
    assert nodes['norm_strong']==('+','strong_difference',1)
    # Historical names retained: ic2=t=i*c^2, ic22=t^2,
    # strong_difference=Delta*t^2, R16=Delta^2*t^2.
    nodes['strong_difference']=('*','A','ic22')
    nodes['norm_strong']=('-','L16','strong_difference')
    nodes['R16']=('*','A','strong_difference')
    done=set(RETAINED+eliminated.baseline.prior.CONSTANTS+['x','Bm1','Kconstant','twice_cell_bits'])
    active,source=set(),[]
    def visit(n):
        if isinstance(n,int) or n in done:return
        assert n not in active
        active.add(n);op,a,b=nodes[n];visit(a);visit(b)
        source.append((n,op,a,b));active.remove(n);done.add(n)
    for a,b in pairs:visit(a);visit(b)
    assert len(source)==len(nodes)==86
    return original,source,pairs,source+[('polynomial','-','eight_units',1)]


def pell(A,n):
    D=A*A-1;x,y,u,v=1,0,A,1
    while n:
        if n&1:x,y=x*u+D*y*v,x*v+y*u
        u,v=u*u+D*v*v,2*u*v;n//=2
    return x,y


def verify_source():
    _,source,pairs,polynomial=sources();_,old,oldpairs,oldpoly=parent.sources()
    before={n:(op,a,b) for n,op,a,b in old};after={n:(op,a,b) for n,op,a,b in source}
    assert before.keys()-after.keys()=={'f_square_minus_one'} and not after.keys()-before.keys()
    assert {n for n in after if after[n]!=before[n]}=={'R16','strong_difference','norm_strong'}
    counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in polynomial)
    assert counts=={'M':48,'A':39} and pairs==oldpairs==[('eight_units',1)]
    rng=random.Random(87203);negative_mu=0;signed=0
    for case in range(512):
        v={n:rng.randrange(1,9) if case<384 else rng.randrange(-8,9) for n in RETAINED+['x']}
        B=rng.choice((16,32,64,256));d=B.bit_length()-1
        fixed=dict(B=B,DC=3,DR=5,MC=B-2,MF=4,cell_bits=d,inner_bits=3)
        new=eliminated.run(polynomial,eliminated.fixed_inputs({**v,**fixed}))
        if case<4:
            v['F']+=2*abs(new['exponent_rhs'])+1
            new=eliminated.run(polynomial,eliminated.fixed_inputs({**v,**fixed}))
        Delta=new['A'];restored={**v,'i':Delta*v['i']}
        oldenv=eliminated.run(oldpoly,eliminated.fixed_inputs({**restored,**fixed}))
        c,V,y=new['R10a'],new['aux_u_rhs'],v['y_aux'];t=v['i']*c*c
        N=v['f']*v['f']-Delta*t*t;K=Delta*Delta*t*t
        assert new['norm_strong']==N and new['R16']==K
        assert oldenv['norm_strong']==1+Delta*(1-N)
        assert new['norm_aux']==oldenv['norm_aux']+Delta*(1-N)*(V*V-y*y)
        expected=[oldenv[n] for n in FACTOR_NAMES]
        expected[3]=K*(V*V-y*y)+y*y;expected[6]=N
        product=1
        for factor in expected:product*=factor
        assert [new[n] for n in FACTOR_NAMES]==expected and new['polynomial']==product-1
        assert all(new[n]==oldenv[n] for n in FACTOR_NAMES if n not in ('norm_aux','norm_strong'))
        signed+=case>=384;negative_mu+=new['exponent_rhs']<0
    return dict(certificate=dict(operations=86,multiplications=48,additions_subtractions=38,equations=1,witnesses=19),
        polynomial=dict(operations=87,multiplications=48,additions_subtractions=39,degree=203,witnesses=19),
        changed_registers=['R16','strong_difference','norm_strong'],deleted_register='f_square_minus_one',
        unchanged_literal_gates=83,retained_positive_witnesses=RETAINED,comparisons=pairs,
        polynomial_schedule=polynomial,complete_factor_identities=512,signed_cases=signed,
        negative_computed_input_roots=negative_mu,
        soundness_coordinate_map='i_old=Delta*i_new; all other coordinates unchanged')


def verify_degree():
    polynomial=sources()[3];z=sp.Symbol('z');records=[]
    for B,d,shift in ((16,4,0),(64,6,1),(256,8,2)):
        scales={n:1+(j+shift)%4 for j,n in enumerate(RETAINED+['x'])}
        scales.update(tau_gap=5,eta=1,zeta=2,Jrep=2,x=1)
        values={n:sp.Poly(scales[n]*z+j+1,z) for j,n in enumerate(RETAINED+['x'])}
        fixed=dict(B=B,DC=3,DR=5,MC=B-2,MF=4,cell_bits=d,inner_bits=3)
        env=eliminated.run(polynomial,eliminated.fixed_inputs({**values,**fixed}))
        factors=[sp.Poly(env[n],z) for n in FACTOR_NAMES]
        assert tuple(f.degree() for f in factors)==FACTOR_DEGREES
        Q=(B-1)*scales['Jrep'];k=scales['eta']+scales['zeta']
        C=Q-scales['F']-scales['Z']-scales['alpha']-2*d*scales['x']
        top=(32*Q**135*scales['h']**2*(scales['rho']+scales['sigma'])*scales['delta']**2
             *scales['i']**4*k**12*scales['w']**17*scales['s']**28*C*(2*scales['tau_gap']-k))
        actual=sp.Poly(env['polynomial'],z)
        assert top and actual.degree()==203 and actual.LC()==top
        records.append(dict(B=B,cell_bits=d,scales=scales,factor_degrees=FACTOR_DEGREES,
                            exact_degree=203,leading_coefficient=str(top)))
    return dict(fixtures=records,highest_homogeneous_term=
        '32*(B-1)^135*Jrep^135*h^2*(rho+sigma)*delta^2*i^4*(eta+zeta)^12*w^17*s^28*C_top*(2*tau_gap-eta-zeta)',
        C_top='(B-1)*Jrep-F-Z-alpha-2*cell_bits*x')


def canonical(A,R):
    Delta=A*A-1;chi,c=pell(A,R);m=2*c*R;f,psi=pell(A,m)
    # Exact Pell composition, with a separately computed short exponent.
    second=pell(chi,2*c)[1]
    assert psi==c*second and second%c==0
    i,rem=divmod(psi,c*c);assert rem==0 and i>0
    t=i*c*c;T=Delta*t
    chiT,y=pell(T,R);V,rem=divmod(chiT,T);assert rem==0
    o,rem=divmod(V+c,f);assert rem==0
    j,rem=divmod(V+R,c);assert rem==0
    assert min(f,i,j,o,y,V)>0
    assert f*f-Delta*t*t==1 and T*T==Delta*(f*f-1)
    assert T*T*(V*V-y*y)+y*y==1 and V==o*f-c==j*c-R
    return dict(A=A,R=R,c=c,m=m,normalized_i_bits=i.bit_length(),f_bits=f.bit_length(),
                y_bits=y.bit_length(),V_bits=V.bit_length(),all_five_auxiliaries_positive=True)


def verify():
    residues=[]
    for a in range(4):
      for f in range(4):
       for t in range(4):
        Delta=(a+2)**2-1;N=f*f-Delta*t*t
        assert N%4!=3
        residues.append((a,f,t,N%4))
    composition=0
    for A in range(2,13):
      for R in range(3,24,4):
        chi,c=pell(A,R)
        # Modulo c the parameter has square one, hence psi(2c)=0.
        assert (chi*chi-1)%c==0
        assert (2*c*pow(chi,2*c-1,c))%c==0
        composition+=1
    cases=[canonical(A,3) for A in range(2,11)]+[canonical(2,7)]
    return dict(status='PASS_COMPLETE75_NORMALIZED_STRONG87',source=verify_source(),degree=verify_degree(),
        negative_unit_mod4_cases=residues,canonical_composition_residue_cases=composition,
        full_canonical_auxiliary_cases=cases,
        scope='Same positive ordinary-input projection as complete coupled88 under all fixed compiler hypotheses. Completeness uses fresh canonical auxiliary witnesses, not a tuple bijection.')


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true')
    args=parser.parse_args();result=verify();path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==json.loads(json.dumps(result))
    print(result['status']);print(result['source']['polynomial'])

if __name__=='__main__':main()
