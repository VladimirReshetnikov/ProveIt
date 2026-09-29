"""Formal100 schedule; full program/carry soundness remains OPEN."""
from pathlib import Path
import json
import sympy as sp
import explore_doubled_grid_complements as old
import explore_unbounded_nozero_grid_fields as lower

SYM={k:v for k,v in old.SYM.items() if k!='Z'}
SUB={old.SYM['Z']:old.SYM['H']-old.SYM['Dzero']}
OUTER_NAMES=[n for n in old.OUTER_NAMES if n!='Z']


def build():
    ops,pairs,source,origins=old.build()
    dropped=origins.index(21)
    ops=[r for r in ops if r[0]!='zero_flag_sum']
    keep=[i for i in range(len(source)) if i!=dropped]
    return ops,[pairs[i] for i in keep],[sp.expand(source[i].subs(SUB,simultaneous=True)) for i in keep],[origins[i] for i in keep]


def verify_certificate():
    ops,pairs,source,origins=build();env=dict(SYM)
    old.old.ALIGNED.baseline.run_schedule(ops,env)
    primitive,counts=old.old.ALIGNED.verify_primitives(ops,env)
    assert len(primitive)==100 and counts=={'+':45,'*':55}
    assert len(source)==len(pairs)==22 and len(OUTER_NAMES+old.CORE_NAMES)==34
    q=SYM['q'];X=SYM['Km']+q*q*(SYM['Dzero']+q*q*(SYM['A0']+q*q*(SYM['A1']+q*q*(SYM['PC']+q*q*SYM['PV']))))
    u=2*SYM['r']+1+SYM['j']*SYM['c'];records=[]
    for i,((left,right),poly,origin) in enumerate(zip(pairs,source,origins)):
        correction=0
        if origin==9:correction=source[origins.index(0)]*X+source[origins.index(3)]
        if origin==18:correction=source[origins.index(17)]*(u*u-SYM['y_aux']**2)
        assert sp.expand(env[left]-env[right]-poly-correction)==0,(i,origin)
        records.append(dict(index=i,old_index=origin,equality=[left,right],source=sp.sstr(poly),correction=sp.sstr(correction)))
    assert not any(old.SYM['Z'] in p.free_symbols for p in source)
    return dict(status='PASS_ARITHMETIC_ONLY',operations=100,primitive_histogram=counts,
                unknown_count=34,positive_unknowns=OUTER_NAMES+old.CORE_NAMES,equations=22,
                primitive_instructions=primitive,equalities=pairs,residuals=records,
                scope='Exact100 schedule and22 source comparisons only. This does not establish universality or sound field recovery after deleting positive Z.')


def verify_doubled_lower_obstruction():
    q,H,k,A0,A1,Kp,Km=sp.symbols('q H k A0 A1 Kp Km')
    t=k*(q+H)
    original=[Kp,Km,-q,q+H,t-A0,A0,t-A1,A1]
    normalized=[Kp,Km,0,H-1,k*H-A0+1,A0+k,k*H-A1,A1+k]
    doubled_original=[2*f for f in original];doubled_normalized=[2*f for f in normalized]
    assert sp.expand(sum((a-b)*q**i for i,(a,b) in enumerate(zip(doubled_original,doubled_normalized))))==0
    # Exact homogeneity of every lower source, including the strengthened
    # input bound. The source of the actual source values is still raw 2x.
    x,R,W,J,v,alpha=sp.symbols('x R W J v alpha')
    D=q+H
    residuals=[q-2*J-1,q-W*v,W-R**3,H*(R-1)-2*J,Kp+Km-H,
               6*t-(R-3)*D,W*(A0+A1+Kp-Km)-(A0+A1-2*x)]
    doubled=[q-2*J-1,q-W*v,W-R**3,2*H*(R-1)-4*J,2*Kp+2*Km-2*H,
             12*t-(R-3)*2*D,W*(2*A0+2*A1+2*Kp-2*Km)-(2*A0+2*A1-4*x)]
    assert all(sp.expand(a-factor*b)==0 for a,b,factor in zip(doubled,residuals,[1,1,1,2,2,2,2]))
    cases=[]
    for m in (4,6,8):
        c=lower.case(m);R0=3**m;k0=(R0-3)//6;x0=(k0+1)//2
        assert 4*x0<R0
        q0=R0**c['height'];h0=(q0-1)//(R0-1);H0=2*h0;t0=2*k0*(q0+h0)
        assert q0%4==1 and H0%4==0 and (2*H0+2*t0)%4==0
        cases.append(dict(width=m,radix=R0,input=x0,height=c['height'],
                          doubled_lower_masks=8,positive_input_slack=R0-4*x0,
                          formal_Z='-2*q',formal_D='H_doubled+2*q',
                          conditional_complete_packed_index_even=True,
                          inherited_exact_lower_residuals=c['exact_lower_residuals'],
                          scope='Fresh undoubled exact lower case plus the exact homogeneous doubling identity. Program and complete packed-kernel equations are not supplied.'))
    return dict(status='PASS_SCOPED_LOWER_OBSTRUCTION',symbolic_doubled_packing_identities=1,
                homogeneous_source_identities=7,cases=cases,
                scope='All eight lower masks and raw input/time equations can pass with D>q and reconstructed Z<0. This excludes local-only bound recovery; it is not a full100 counterexample.')


def verify():
    return dict(status='OPEN_DOUBLED_ZERO_GRID_100',arithmetic=verify_certificate(),
                lower_obstruction=verify_doubled_lower_obstruction(),
                proof='../1980/EXPLORATION_DOUBLED_ZERO_GRID_OPEN.md',
                scope='Formal100 candidate remains OPEN. The general Pell bootstrap survives, but joint controller/carry recovery or a full false-code family is unresolved. No improvement of the verified101 architecture or universal90 frontier is claimed.')


if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print(result['arithmetic']['primitive_histogram']);print(result['lower_obstruction'])
