#!/usr/bin/env python3
"""A formal116 direct-delta schedule fails its unchanged native junk mask."""
from pathlib import Path
import json
import sympy as sp
import explore_complement_zero_serial_composition as old
from explore_native_ternary_ripple import native


def build():
    ops,pairs,source=old.build();c=old.PROGRAM;z=old.SYM
    changed=[]
    for name,op,left,right in ops:
        if name=='raw_Kplus':continue
        if name=='WK':right=2*c['K']
        if name=='route_coeff':right=2*c['g']
        if name=='route_final':left=2*c['g']*c['I']
        if name=='sign_output':right='delta'
        if name=='nozero_output':left=2*c['hz']
        changed.append((name,op,left,right))
    source=list(source)
    source[-1]=(2*z['R']*c['K']-2*c['g'])*z['PC']-4*c['g']*c['I']*z['Jrep'] \
        -z['R']*(z['PV']+c['hs']*(z['FKplus']-z['FKminus'])
                  +2*c['hz']*(z['FZbar']-z['Jrep']))
    return changed,pairs,source


def verify_arithmetic():
    ops,pairs,source=build();z=old.SYM;env=dict(z)
    old.old.old.old.old.aligned.baseline.run_schedule(ops,env)
    primitives,counts=old.old.old.old.old.aligned.verify_primitives(ops,env)
    assert len(primitives)==116 and counts=={'+':60,'*':56}
    u=z['j']*z['c']+2*z['r']+1
    for index,((left,right),polynomial) in enumerate(zip(pairs,source)):
        correction=source[17]*(u*u-z['y_aux']**2) if index==18 else 0
        assert sp.expand(env[left]-env[right]-polynomial-correction)==0,index
    # The raw routing equation is repaired by exactly this affine junk map.
    V,Vnew,H,Kp,Km,J,hs=sp.symbols('V Vnew H Kp Km J hs')
    assert sp.expand((2*V+hs*H)+hs*(Kp-Km)-2*(V+hs*(Kp-J))
                     +hs*(Kp+Km-2*J-H))==0
    return dict(operations=116,primitive_histogram=counts,equations=len(source),
                positive_unknowns=len(old.OUTER_NAMES+old.CORE_NAMES),
                primitive_instructions=primitives,
                source_residuals=[sp.sstr(p) for p in source],
                scope='Formal arithmetic only. This is NOT a verified history or universal system.')


def least_trit(value):
    assert value>0
    index=0
    while value%3==0:value//=3;index+=1
    return index,value%3


def verify_obstruction():
    c=old.PROGRAM;R=c['Rmin'];J=(R-1)//2;ell=c['B']
    rows=[]
    for i,j in c['edges']:
        label=int(c['signs'][i]==1);nozero=1-c['zeros'][i]
        V=c['K']*3**c['a'][i]-c['g']*3**c['a'][j]-c['hs']*label-c['hz']*nozero
        assert V>0 and native(J+V,ell)
        exponent,digit=least_trit(V)
        assert digit==1 and exponent<=c['d']<c['d']+c['bs']
        Vnew=2*V+c['hs']
        assert Vnew<R and (Vnew//3**exponent)%3==2
        assert ((J+Vnew)//3**exponent)%3==0
        assert not native(J+Vnew,ell)
        delta=2*label-1
        assert Vnew+c['hs']*delta+2*c['hz']*nozero==2*(V+c['hs']*label+c['hz']*nozero)
        rows.append(dict(edge=[i,j],least_junk_trit=exponent,
                         doubled_junk_digit=2,native_adapter_digit=0))
    simple=0
    for width in range(1,9):
        q=3**width;rep=(q-1)//2
        for bits in range(1,1<<width):
            V=sum(((bits>>i)&1)*3**i for i in range(width))
            exponent,_=least_trit(V)
            assert ((rep+2*V)//3**exponent)%3==0
            assert not native(rep+2*V,width)
            simple+=1
    # A two-position encoding exists, so no blanket impossibility is claimed.
    repairs=[]
    for bit in (0,1):
        value=5+2*bit
        assert native(value,2)
        repairs.append(dict(bit=bit,value=value,trits=[value%3,value//3]))
    return dict(fixed_program_edges=rows,nonzero_boolean_words=simple,
                two_trit_repairs=repairs,
                scope='Every canonical fixed-ROM row fails the proposed unchanged PNV mask. The general proof covers every nonempty correctly coded history. No malformed full-system counterexample or general ROM lower bound is claimed.')


def verify():
    return dict(status='PASS_DIRECT_DELTA_NATIVE_JUNK_OBSTRUCTION',
                arithmetic=verify_arithmetic(),obstruction=verify_obstruction(),
                proof='../1980/EXPLORATION_SIGNED_OPCODE_JUNK_OBSTRUCTION.md')


if __name__=='__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print(result['arithmetic']['operations'],result['arithmetic']['primitive_histogram'])
    print(result['obstruction'])
