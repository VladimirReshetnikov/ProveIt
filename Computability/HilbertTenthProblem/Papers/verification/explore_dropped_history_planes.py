#!/usr/bin/env python3
"""Exact arithmetic and counterexamples for two unsound five-plane edits."""
from pathlib import Path
import json
import sympy as sp
import round40_1980_moving_frame_components as old
import round43_1980_direct_history_length as direct
from round13_1980_certificate import verify_primitives
from explore_aligned_boolean_tableaux import local_planes, bitplane, digits


def certificate(drop):
    if drop == 'B':
        schedule=[('packed' if name=='pack7' else name,op,l,r)
                  for name,op,l,r in old.SCHEDULE if name not in ('pack8','packed')]
        expected=84
    else:
        schedule=[(name,op,l,'Zw' if name=='pack2' else r)
                  for name,op,l,r in old.SCHEDULE if name not in ('Bh','pack0','pack1')]
        expected=83
    env=dict(old.SYM)
    old.previous.baseline.run_schedule(schedule,env)
    source=old.source_residuals()
    z=old.SYM; Q=z['q']**2
    if drop=='B':
        packed=z['Dw']+Q*(z['Xw']+Q*(z['Ew']+Q*(z['Zw']+Q*(z['Bw']+z['hrow']))))
    else:
        packed=z['Bw']+Q*(z['Dw']+Q*(z['Xw']+Q*(z['Ew']+Q*z['Zw'])))
    source[10]=z['r']-(Q**8-packed)*3*z['lam']-2*z['lam']
    aux=2*z['r']+1+z['j']*z['c']
    correction=source[18]*(aux**2-z['y_aux']**2)
    for index,((l,r),residual) in enumerate(zip(old.EQUALITIES,source)):
        actual=sp.expand(env[l]-env[r])
        adjustment=correction if index==19 else 0
        assert sp.expand(actual-residual-adjustment)==0 or (
            adjustment==0 and sp.expand(actual+residual)==0)
    primitives,counts=verify_primitives(schedule,env)
    assert len(primitives)==expected
    return dict(operations=expected,primitive_histogram=counts,equations=21,
                positive_unknowns=31,primitive_instructions=primitives,
                equalities=old.EQUALITIES)


def check_tuple(width,height,B,I,F,drop):
    W,Q=4**width,4**(width*height)
    H=(Q-1)//(W-1)
    # Splitting the normalized integer digits proves exact local equalities.
    C=B//4
    def split(value):
        ds=digits(value,width*height)
        return (sum((d%2)*4**i for i,d in enumerate(ds)),
                sum((d//2)*4**i for i,d in enumerate(ds)))
    X,D=split(B+C); Z,E=split(4*B+D)
    Y=X+D-E
    assert B==4*C and B+C==X+2*D and 4*B+D==Z+2*E and Y+E==X+D
    assert I+W*Y==C+Q*F
    alpha=Q-4*B-B-C; alphaI=W-I
    assert min(B,C,X,D,Z,E,Y,alpha,alphaI,I,F)>0 and F<W
    q,v,quot=2**(width*height),2**width,2**(width*(height-1))
    assert q==v*quot and Q-1==H*(W-1)
    fields=(D,X,E,Z,B+H) if drop=='B' else (B,D,X,E,Z)
    assert all(0<field<Q and bitplane(field) for field in fields)
    if drop=='B': assert not bitplane(B)
    else: assert any((B//W**j)%4 for j in range(height)) and not bitplane(B+H)
    packed=0
    for field in reversed(fields): packed=field+Q*packed
    L,n0=Q**8,Q**6
    lam=(L-1)//3
    r=(L-packed)*(L-1)+2*lam
    assert 0<packed<Q**5<Q**6 and packed%2==r%2==0
    assert n0*n0<r<Q**16<n0**3
    assert r.bit_count()==3*((L.bit_length()-1)//2)==(Q**12).bit_length()-1
    return dict(width=width,height=height,Q=Q,W=W,H=H,q=q,v=v,quot=quot,
                B=B,C=C,D=D,X=X,E=E,Z=Z,Y=Y,I=I,F=F,
                alpha=alpha,alphaI=alphaI,packed_fields=fields,
                input_boolean=bitplane(I),B_boolean=bitplane(B),
                B_plus_H_boolean=bitplane(B+H),r_even=True,
                exact_popcount=r.bit_count(),r_bit_length=r.bit_length(),
                pell_extension='General positive construction applies; astronomical Pell witnesses are not materialized.')


def further_local_deletions():
    cases=[('D',3,4,1,2,1,16),('X',5,84,73,16,16,320),
           ('E',5,84,65,20,50,256),('Z',5,84,65,20,1,354)]
    result=[]
    for omitted,width,B,X,D,E,Z in cases:
        Q=W=4**width; v=2**width; C=I=B//4; Y=F=X+D-E
        H=1; alpha=Q-4*B-B-C; alphaI=v-I
        assert B+C==X+2*D and 4*B+D==Z+2*E and Y+E==X+D
        assert I+W*Y==C+Q*F and min(B,C,X,D,E,Z,Y,I,F,alpha,alphaI)>0
        values=dict(D=D,X=X,E=E,Z=Z,T=B+H)
        assert not bitplane(values[omitted])
        kept=[name for name in ('D','X','E','Z','T') if name!=omitted]
        if omitted=='D': kept=['Z','X','E','T']
        assert all(bitplane(values[name]) and values[name]<Q for name in kept)
        assert bitplane(I) and I<v and 4*Y<Q
        P=0
        for name in reversed(kept): P=values[name]+Q*P
        L,n0=Q**8,Q**6; lam=(L-1)//3
        r=(L-P)*(L-1)+2*lam
        assert P%2==r%2==0 and n0*n0<r<n0**3
        assert r.bit_count()==(Q**12).bit_length()-1
        result.append(dict(omitted=omitted,width=width,height=1,Q=Q,W=W,v=v,
                           H=H,B=B,C=C,D=D,X=X,E=E,Z=Z,Y=Y,I=I,F=F,
                           alpha=alpha,alphaI=alphaI,packed_field_order=kept,
                           input_boolean=True,strong_input_bound=True,
                           popcount=r.bit_count(),r_even=True))
    return result


def c_for_row_start_certificate():
    """The tempting 80-operation edit replaces top B+H by supplied C."""
    schedule=[(name,op,'Cw' if left=='Bh' else left,'Cw' if right=='Bh' else right)
              for name,op,left,right in direct.SCHEDULE if name!='Bh']
    env=dict(direct.SYM)
    direct.baseline.run_schedule(schedule,env)
    source=direct.source_residuals()
    z=direct.SYM;q=z['q']
    P=z['Dw']+q*z['Xw']+q**2*z['Ew']+q**3*z['Zw']+q**7*z['Cw']
    source[9]=z['r']-(q**8-P)*3*z['lam']-2*z['lam']
    aux=2*z['r']+1+z['j']*z['c']
    correction=source[17]*(aux**2-z['y_aux']**2)
    for index,((left,right),residual) in enumerate(zip(direct.EQUALITIES,source)):
        actual=sp.expand(env[left]-env[right])
        adjustment=correction if index==18 else 0
        assert sp.expand(actual-residual-adjustment)==0 or (
            adjustment==0 and sp.expand(actual+residual)==0)
    primitives,counts=verify_primitives(schedule,env)
    assert len(primitives)==80 and counts=={'+':36,'*':44}
    assert len(source)==len(direct.EQUALITIES)==20
    return dict(operations=80,primitive_histogram=counts,equations=20,
                positive_unknowns=30,primitive_instructions=primitives,
                equalities=direct.EQUALITIES,
                packing='D+qX+q^2E+q^3Z+q^7C',
                source_residuals_verified=20)


def c_for_row_start_counterexample():
    width,height=3,3
    W,v,q,H=64,8,262144,4161
    B,C,I,F=87316,21829,5,16
    D,X,E,Z,Y=21764,65617,21504,328020,65877
    quot=q//v;alphaI=v-I
    assert q==W**height and W==v*v and q==v*quot
    assert q-1==H*(W-1) and I+alphaI==v
    assert B==4*C and B+C==X+2*D and 4*B+D==Z+2*E and Y+E==X+D
    assert I+W*Y==C+q*F
    assert min(B,C,I,F,D,X,E,Z,Y,quot,alphaI,H)>0
    assert all(bitplane(value) for value in (C,D,X,E,Z,I,F))
    assert max(C,D,X,E)<q and q<=Z<2*q and Y<q
    assert [B//W**j%4 for j in range(height)]==[0,0,1]
    assert not bitplane(B+H)
    R=D+q*X+q*q*E+q**3*Z
    P=R+q**7*C;L=q**8;n0=q**6;scale=q**12
    lam=(L-1)//3;r=(L-P)*(L-1)+2*lam
    assert 0<R<q**7 and P//q**7==C and 0<P<L
    assert bitplane(P) and P%2==r%2==0
    assert n0>=64 and n0*n0<r<q**16<n0**3
    assert r.bit_count()==scale.bit_length()-1==216

    # Finite zero-exterior Rule110, evaluated without the packed alignment.
    initial=4*I
    def bit(i):
        return 0 if i<0 else initial//4**i%4
    raw_successor=sum((bit(i)+bit(i+1)-bit(i)*bit(i+1)*(bit(i-1)+1))*4**i
                      for i in range(6))
    forced_height=(F.bit_length()-1)//2-(I.bit_length()-1)//2
    assert forced_height==1 and raw_successor==21 and raw_successor!=F
    return dict(width=width,height=height,Q=q,W=W,q=q,v=v,quot=quot,H=H,
                B=B,C=C,I=I,F=F,D=D,X=X,E=E,Z=Z,Y=Y,alphaI=alphaI,
                retained_fields=['D','X','E','Z','C'],
                input_boolean=True,strong_input_bound=True,
                row_start_digits=[0,0,1],Z_extra_top_digit=True,
                lower_gap_bound=True,packed_boolean=True,packed_below_L=True,
                r_even=True,exact_popcount=r.bit_count(),r_bit_length=r.bit_length(),
                forced_true_endpoint_height=forced_height,true_one_step_F=raw_successor,
                endpoint_relation=False,
                pell_extension='Every premise of the unchanged 43-operation positive necessity construction holds. Astronomical Pell witnesses are not materialized.')


def verify():
    return dict(status='EXACT_ARITHMETIC_WITH_SEMANTIC_COUNTEREXAMPLES',
                drop_B=dict(certificate=certificate('B'),
                            counterexample=check_tuple(5,2,85328,852,68,'B')),
                drop_B_plus_H=dict(certificate=certificate('Bh'),
                                  counterexample=check_tuple(2,3,340,5,1,'Bh')),
                further_guarded_local_deletions=further_local_deletions(),
                replace_B_plus_H_with_C=dict(certificate=c_for_row_start_certificate(),
                                           counterexample=c_for_row_start_counterexample()),
                scope='Two unguarded five-plane edits fail; four additional tuples defeat every individual local-plane deletion under the strengthened I<v guard; the direct-length 80-operation C-for-B+H replacement also admits a full positive false endpoint. No universal-system counterexample is claimed.')


if __name__=='__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status'])
    for name in ('drop_B','drop_B_plus_H'):
        row=result[name]
        print(name,row['certificate']['operations'],row['certificate']['primitive_histogram'],row['counterexample'])
    row=result['replace_B_plus_H_with_C']
    print('replace_B_plus_H_with_C',row['certificate']['operations'],
          row['certificate']['primitive_histogram'],row['counterexample'])
