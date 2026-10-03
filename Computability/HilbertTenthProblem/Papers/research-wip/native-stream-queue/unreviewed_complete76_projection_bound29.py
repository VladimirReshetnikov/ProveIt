"""Complete76 projection-bound rewrite:29 positive witnesses and18 equations."""
import argparse
from collections import Counter
import json
from pathlib import Path
import sys
import sympy as sp

VERIFICATION=Path(__file__).resolve().parents[2]/'verification'
sys.path.insert(0,str(VERIFICATION))
import explore_fixed_raw_universal_76 as original


NAMES=[name for name in original.NAMES if name not in ('phi','rho')]+['input_sigma']
SYM={name:original.SYM[name] for name in NAMES if name!='input_sigma'}
SYM['input_sigma']=sp.Symbol('input_sigma')
SYM.update({name:original.SYM[name] for name in original.CONSTANTS+['x']})


def source_check():
    schedule=[]
    for row in original.SCHEDULE:
        name,op,left,right=row
        if name=='pell_gap':continue
        if name=='modulus_multiple':left='input_sigma'
        if name=='exponent_rhs':right='gam'
        schedule.append((name,op,left,right))
    schedule.append(('input_projection_left','+','mu','modulus_multiple'))
    equalities=[]
    for left,right in original.EQUALITIES:
        if right=='pell_gap':continue
        if (left,right)==('mu','exponent_rhs'):left='input_projection_left'
        equalities.append((left,right))
    old=original.source_residuals()
    sources=old[:16]+[old[17]]
    H=4*SYM['a']+3
    sources += [SYM['mu']+SYM['input_sigma']*H-SYM['W']-SYM['a']*SYM['kappa']-SYM['ga']*H]
    env=original.fixed_environment(SYM)
    original.previous.previous.previous.previous.bridge.baseline.run_schedule(schedule,env)
    U=SYM['j']*SYM['c']-(2*SYM['r']+1)
    correction=sources[12]*(U*U-SYM['y_aux']**2)
    records=[]
    for ix,((left,right),source) in enumerate(zip(equalities,sources)):
        actual=sp.expand(env[left]-env[right]);adjust=correction if ix==13 else 0
        sign=1 if sp.expand(actual-source-adjust)==0 else -1
        assert sp.expand(actual-sign*source-adjust)==0,ix
        records.append(dict(index=ix,equality=[left,right],source_sign=sign,
                            source=str(sp.expand(source)),correction=str(sp.expand(adjust))))
    primitives,counts=original.previous.previous.previous.previous.bridge.verify_primitives(schedule,env)
    assert len(primitives)==76 and counts=={'+':35,'*':41}
    assert len(NAMES)==29 and len(equalities)==len(sources)==18
    assert all(row[0]!='pell_gap' for row in schedule)
    assert not any(arg in ('phi','rho') for row in schedule for arg in row[2:])
    used=set().union(*(p.free_symbols for p in sources))
    assert {SYM[name] for name in NAMES}<=used
    assert original.SYM['phi'] not in used and original.SYM['rho'] not in used
    aliases={name:value for name,value in original.fixed_environment(SYM).items() if name not in SYM}
    assert all(sp.sympify(value).free_symbols<={SYM[name] for name in original.CONSTANTS} for value in aliases.values())
    rho=original.SYM['rho'];sigma=SYM['input_sigma'];gamma=SYM['ga']
    old_projection=old[18]
    assert sp.expand(sources[-1].subs(sigma,gamma-rho)-old_projection)==0
    assert sp.expand(old_projection.subs(rho,gamma-sigma)-sources[-1])==0
    return dict(operations=76,multiplications=41,additions_subtractions=35,
                positive_existential_unknown_count=29,positive_unknowns=NAMES,equations=18,
                fixed_constants=original.CONSTANTS,raw_parameters=['x>0'],
                primitive_instructions=primitives,sources=records,
                fixed_aliases={name:str(value) for name,value in aliases.items()},
                ledger=dict(unchanged_outer=19,unchanged_kernel=43,input_bridge=14),
                removed_coordinate='phi',replaced_coordinate={'rho':'input_sigma=ga-rho'},
                removed_equation='c=kappa+phi',
                projection='mu+input_sigma*H=W+a*kappa+ga*H',
                scope='Complete equivalent universal source; operation bound remains76')


def pell(A,n):
    # Binary multiplication in Z[sqrt(A^2-1)], independent of old fixtures.
    D=A*A-1;x,y=1,0;u,v=A,1
    while n:
        if n&1:x,y=x*u+D*y*v,x*v+y*u
        n//=2
        if n:u,v=u*u+D*v*v,2*u*v
    return x,y


def E(A,n):
    x,y=pell(A,n)
    return x-(A-2)*y


def growth_checks():
    cases=monotone=0
    for A in range(2,16):
        seq=[(1,0),(A,1)]
        for n in range(2,20):
            seq.append((2*A*seq[-1][0]-seq[-2][0],2*A*seq[-1][1]-seq[-2][1]))
        assert all(pell(A,n)==seq[n] for n in range(len(seq)))
        values=[x-(A-2)*y for x,y in seq]
        assert values[0]==1 and values[1]==2
        for n in range(1,19):
            assert values[n+1]-values[n]==(4*A-3)*seq[n][1]-seq[n-1][1]>0
            monotone+=1
        for u in range(1,13):
            gap=seq[u+2][1]-2*seq[u][1]
            assert gap>(4*A*A-2*A-3)*seq[u][1]>A
            for p in range(u+2,20):
                assert values[p]-values[u]>gap>A
                cases+=1
    return dict(Pell_parameters=[2,15],independent_binary_vs_recurrence_checks=14*20,
                monotonic_steps=monotone,strict_projection_gaps=cases)


def bridge_fixture(a,q,p,u,prepower=False):
    A=a+2;D=A*A-1;H=4*a+3;X=2**p;W=2**u
    assert a>X>q>W and 3<=u<p<a+1 and u%2==p%2==1
    mu,kappa=pell(A,u);d,c=pell(A,p)
    gamma,rem=divmod(d-a*c-X,H);assert rem==0 and gamma>0
    rho,rem=divmod(mu-a*kappa-W,H);assert rem==0 and rho>0
    delta,rem=divmod(kappa-u,D);assert rem==0 and delta>0
    phi=c-kappa;sigma=gamma-rho
    assert phi>0 and sigma>0
    assert mu*mu==1+D*kappa*kappa
    assert kappa==u+delta*D
    assert mu+sigma*H==W+a*kappa+gamma*H
    assert c==kappa+phi and mu==W+a*kappa+rho*H
    assert (gamma-sigma)==rho
    assert E(A,p)-E(A,u)>A>X
    if prepower:
        r=(p-1)//2
        assert q>=16 and q*q<=r<q**4 and r%2==1 and 2*q<p
    return dict(q=q,main_index=p,input_index=u,a_bit_length=a.bit_length(),
                kappa_bit_length=kappa.bit_length(),c_bit_length=c.bit_length(),
                sigma_bit_length=sigma.bit_length(),all_bridge_coordinates_positive=True,
                matches_numerical_full_prekernel_bounds=prepower,
                materialized_full_compiler_or_kernel=False)


def bridge_checks():
    fixtures=[]
    for u,p,q in ((3,19,16),(3,27,16),(5,131,64),(7,515,256)):
        for multiplier in (2,3):
            fixtures.append(bridge_fixture(multiplier*2**p,q,p,u))
    for q,p in ((16,515),(32,2051)):
        fixtures.append(bridge_fixture(2*2**p,q,p,3,True))
    return dict(exact_positive_bridge_tuples=len(fixtures),fixtures=fixtures,
                scope='Main/input Pell projections and both positive maps. Full compiler, binomial-floor and auxiliary kernel equations are not asserted for these finite fixtures.')


def verify():
    return dict(status='PASS_COMPLETE76_PROJECTION_BOUND29',source=source_check(),
                growth=growth_checks(),bridge=bridge_checks(),
                theorem='Equivalent complete universal76 source with29 positive witnesses and18 equations',
                established_complete_operation_bound=76,
                scope='Full source audit and parametric positive equivalence; no75-operation claim or materialized full compiler tableau')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=verify();receipt=Path(__file__).with_suffix('.json')
    normalized=json.loads(json.dumps(result))
    if args.write:receipt.write_text(json.dumps(normalized,indent=2)+'\n')
    else:assert json.loads(receipt.read_text())==normalized,'receipt mismatch'
    print(json.dumps({key:value for key,value in normalized.items() if key!='source'},indent=2))
