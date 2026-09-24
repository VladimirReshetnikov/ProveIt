"""Scoped grid-repunit reparameterization: an exact100-operation tie."""
from pathlib import Path
import json
import sympy as sp
import explore_state_top_doubled_grid as old

B0=old.old.old.B0
ZON=old.old.old.ZON
PROGRAM=old.PROGRAM
SYM={k:v for k,v in old.SYM.items() if k!='zgrid'}
SYM['Ggrid']=sp.Symbol('Ggrid')


def build():
    prior,pairs,source,origins=old.build()
    ops=[];pairs=list(pairs);source=list(source)
    for name,op,a,b in prior:
        if name=='grid_width':continue
        if name=='grid_width_product':a,b=B0-1,'Ggrid'
        if name=='paired_grid_coefficient':op,a,b='-','paired_grid_shift',ZON
        if name=='paired_high':b='grid_base'
        ops.append((name,op,a,b))
        if name=='paired_grid_heads':ops.append(('grid_base','+','Ggrid','paired_grid_heads'))
    wi=origins.index(26)
    pairs[wi]=('grid_width_product','twice_J')
    source[wi]=(B0-1)*SYM['Ggrid']-2*SYM['Jrep']
    fields=old.conceptual_fields()
    fields[8]=SYM['Ggrid']-ZON*SYM['H']-SYM['PV']
    raw=sum(f*SYM['q']**i for i,f in enumerate(fields))
    source[origins.index(9)]=sp.expand(2*SYM['r']+1-SYM['q']**12-raw)
    return ops,pairs,source,origins,raw


def verify_source():
    ops,pairs,source,origins,raw=build();env=dict(SYM)
    old.old.old.ALIGNED.baseline.run_schedule(ops,env)
    primitive,counts=old.old.old.ALIGNED.verify_primitives(ops,env)
    assert len(primitive)==100 and counts=={'+':45,'*':55}
    assert len(source)==len(pairs)==22
    q=SYM['q'];X=SYM['Km']+q*q*(SYM['Dzero']+q*q*(SYM['A0']+q*q*(SYM['A1']+q*q*(SYM['PV']+q*q*SYM['PC']))))
    geometry=source[origins.index(0)];sign=source[origins.index(3)]
    assert sp.expand(env['raw_packed']-raw+geometry*X+sign)==0
    u=2*SYM['r']+1+SYM['j']*SYM['c']
    for (a,b),s,origin in zip(pairs,source,origins):
        correction=geometry*X+sign if origin==9 else 0
        if origin==18:correction=source[origins.index(17)]*(u*u-SYM['y_aux']**2)
        assert sp.expand(env[a]-env[b]-s-correction)==0,origin
    former=old.build()[2][old.build()[3].index(9)]
    assert sp.expand(source[origins.index(9)].subs(SYM['Ggrid'],(ZON+old.SYM['zgrid'])*SYM['H'])-former)==0
    return dict(operations=100,multiplications=55,additions=45,positive_unknowns=34,
                equations=22,geometry_delta_additions=-1,packing_delta_additions=1,
                exact_source_comparisons=len(source),
                scope='Arithmetic certificate only; semantic equivalence is not established for this reparameterization.')


def verify_factoring():
    q,J,G,X,H,t,S,Z,b=sp.symbols('q J G X H t S Z b')
    direct=J*X+(1+q*q)*(H+q**4*t)+q**8*(G+H*(q*q*S-Z))
    fused=G*(b*X/2+q**8)+(1+q*q)*(H+q**4*t)+q**8*H*(q*q*S-Z)
    assert sp.expand(direct-fused-X*(J-b*G/2))==0
    return dict(direct_geometry=[2,3],old_geometry=[2,4],direct_high_base=[3,2],old_high_base=[3,1],
                direct_JX_plus_high=[4,3],fused_JX_plus_high=[5,3],
                convention='Pairs give multiplication and addition counts. Shared q2/q4/q8 and the independent low block are excluded from both last comparisons. The fixed integer b/2 is a numeral.',
                scope='These explicit layouts do not save an operation; no lower bound on arbitrary straight-line programs is asserted.')


def verify_small_geometry():
    # This is a partial tuple: neither route nor packed/Pell equations are imposed.
    R=27;W=R**3;q=R**4;J=q-1;H=2*J//(R-1);G=2*J//(B0-1)
    A0=A1=2;x=1;D=1;t=4;Kp=(H-4)//2;Km=(H+4)//2
    residuals=[q-J-1,q-W*(q//W),W-R**3,H*(R-1)-2*J,
               (B0-1)*G-2*J,Kp+Km-H,6*t-(R-3)*D,
               W*(A0+A1+Kp-Km)-(A0+A1-4*x),4*x+(R-4*x)-R]
    assert all(v==0 for v in residuals)
    assert min(R,W,q,J,H,G,A0,A1,x,D,t,Kp,Km,R-4*x)>0
    assert (R-1)%(B0-1)!=0 and G-ZON*H<0
    X=Km+q*q*(D+q*q*(A0+q*q*(A1+q*q*(1+q*q))))
    P=J*X+(1+q*q)*(H+q**4*t)+q**8*(G+H*(q*q*PROGRAM['S']-ZON))
    assert P<0
    return dict(R=R,q=q,H=H,G=G,x=x,checked_partial_residuals=len(residuals),
                row_grid_alignment=False,allowed_grid_difference_negative=True,factored_packing_negative=True,
                scope='A geometry/sign/top/time/input tuple with C=V=1 for evaluating P. It does not satisfy a full route or packed/Pell certificate and is not a counterexample to full semantic soundness.')


def verify():
    return dict(status='SCOPED_GRID_REPUNIT_TIE',source=verify_source(),factoring=verify_factoring(),
                review='Author and independent scoped proof/source review and fresh verification PASS without findings.',
                partial_tuple=verify_small_geometry(),proof='../1980/EXPLORATION_GLOBAL_GRID_REPUNIT_LEDGER.md',
                scope='No99-operation reduction. Exact100 arithmetic tie and two changed pretyping obligations only.')


if __name__=='__main__':
    r=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(r,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(r,indent=2))
