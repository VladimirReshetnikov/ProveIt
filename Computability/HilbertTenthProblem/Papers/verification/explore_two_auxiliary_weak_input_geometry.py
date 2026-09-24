#!/usr/bin/env python3
"""Exact79 arithmetic for a refuted weaker input/order-geometry candidate."""
from pathlib import Path
import json
import sympy as sp

import round44_1980_two_auxiliary_history as valid
import round4_1980_operation_count as baseline
from round13_1980_certificate import verify_primitives

PARAMETERS=['I','F']
OUTER_NAMES=['q','W','quot','hrow','d_geom','Bw','Cw','Yw','Uw','Vw',
             'alpha','alphaI','lam']
CORE_NAMES=valid.CORE_NAMES
NAMES=PARAMETERS+OUTER_NAMES+CORE_NAMES
SYM={name:sp.Symbol(name) for name in NAMES}
OUTER=[]
for row in valid.OUTER:
    if row[0] in ('v2','W'):
        continue
    if row[0]=='vq':
        row=('vq','*','W','quot')
    OUTER.append(row)
    if row[0]=='Wm1':
        OUTER.append(('seven_geom','*',7,'d_geom'))
SCHEDULE=OUTER+valid.CORE
EQUALITIES=[('Ibound','W') if left=='Ibound' else (left,right)
            for left,right in valid.EQUALITIES]
EQUALITIES.insert(2,('Wm1','seven_geom'))


def source_residuals():
    z=SYM
    q,W,quot,H,dg,B,C,Y,U,V,alpha,alphaI,lam=[z[name] for name in OUTER_NAMES]
    a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,ga,y=[z[name] for name in CORE_NAMES]
    L,scale=q**6,q**10
    P=U+q*V+q*q*Y+q**3*(B+H)
    Up,Yp=w*scale,s*scale
    Dpell=a*a+4*a+3
    K,aux_u=Dpell*(f*f-1),2*r+1+j*c
    return [q-W*quot,q-1-H*(W-1),W-1-7*dg,B-8*C,
            15*B+4*Y-C-2*U-3*V,C+2*U+3*V+alpha-q,
            z['I']+alphaI-W,z['I']+W*Y-C-q*z['F'],
            7*lam+1-L,r-(L-P)*7*lam-6*lam,
            Up*Yp*Yp*(Up*Yp*Yp+1)*k*k-tau*(tau+1),
            c-Yp*k-eta,k-eta-zeta,k-r-1-h*Up*Yp,
            a-Yp*(Up+1),d-Up-a*c-ga*(4*a+3),
            d*d-Dpell*c*c-1,(i*c*c)**2-Dpell*(f*f-1),
            K*(aux_u*aux_u-y*y)-(1-y*y),aux_u-c-o*f]


def boolean(n):
    if n<0:return False
    while n:
        n,digit=divmod(n,8)
        if digit>1:return False
    return True


def verify():
    env=dict(SYM)
    baseline.run_schedule(SCHEDULE,env)
    source=source_residuals()
    z=SYM
    aux_u=2*z['r']+1+z['j']*z['c']
    correction=source[17]*(aux_u**2-z['y_aux']**2)
    records=[]
    for index,((left,right),residual) in enumerate(zip(EQUALITIES,source)):
        actual=sp.expand(env[left]-env[right])
        adjustment=correction if index==18 else 0
        if sp.expand(actual-residual-adjustment)==0:
            sign=1
        else:
            assert adjustment==0 and sp.expand(actual+residual)==0
            sign=-1
        records.append({'index':index,'equality':[left,right],
                        'source_sign':sign,'source':sp.sstr(sp.expand(residual)),
                        'actual':sp.sstr(actual),'correction':sp.sstr(adjustment)})
    primitives,counts=verify_primitives(SCHEDULE,env)
    assert len(OUTER)==36 and len(valid.CORE)==43
    assert len(primitives)==79 and counts=={'+':34,'*':45}
    assert len(OUTER_NAMES+CORE_NAMES)==30
    assert len(source)==len(records)==len(EQUALITIES)==20
    assert all(row.free_symbols <= set(SYM.values()) for row in source)
    assert set(NAMES) <= {operand for row in SCHEDULE for operand in row[2:]} | {
        operand for pair in EQUALITIES for operand in pair}

    values=dict(q=1073741824,W=32768,hrow=32769,quot=32768,d_geom=4681,
                Bw=19108416,Cw=2388552,Yw=17039432,Uw=151031872,Vw=16777224,
                I=29256,F=520,alpha=718957856,alphaI=3512)
    q=values['q'];W=values['W']
    assert q==8**10 and W==8**5
    P=values['Uw']+q*values['Vw']+q*q*values['Yw']+q**3*(values['Bw']+values['hrow'])
    L,scale=q**6,q**10
    values['lam']=(L-1)//7
    values['r']=(L-P)*(L-1)+6*values['lam']
    substitution={SYM[name]:value for name,value in values.items()}
    outer_values=[int(row.subs(substitution)) for row in source[:10]]
    assert outer_values==[0]*10
    assert all(value>0 for value in values.values())
    fields=[values['Uw'],values['Vw'],values['Yw'],values['Bw']+values['hrow']]
    assert all(boolean(field) and field<q for field in fields)
    assert 0<P<q**4
    r=values['r']
    assert r%2==0 and r.bit_count()==300
    assert scale==1<<300
    assert q**10<r<q**15 and q**20>2*r+1
    assert not boolean(values['I']) and not boolean(values['Bw'])
    I_digits=[values['I']//8**j%8 for j in range(5)]
    B_digits=[values['Bw']//8**j%8 for j in range(10)]
    assert I_digits==[0,1,1,1,7]
    assert B_digits==[0,0,1,1,1,7,0,1,1,0]
    return {'status':'REFUTED_WEAK_INPUT_ORDER_GEOMETRY',
            'arithmetic_status':'PASS','semantic_status':'REFUTED',
            'operations':79,'primitive_histogram':counts,
            'positive_unknowns':OUTER_NAMES+CORE_NAMES,'unknown_count':30,
            'parameters':PARAMETERS,'equations':20,
            'primitive_instructions':primitives,'equalities':EQUALITIES,
            'source_residual_checks':records,
            'counterexample':{name:str(value) if name in ('r','lam') else value
                              for name,value in values.items()},
            'counterexample_outer_residuals':outer_values,
            'packed_P':str(P),'I_digits_low_first':I_digits,
            'B_digits_low_first':B_digits,'mask_fields_Boolean_and_bounded':True,
            'r_even':True,'r_popcount':300,'binomial_valuation_threshold':300,
            'full_positive_Pell_extension':'Proved from exact even-r, power and binomial hypotheses; huge Pell coordinates are not instantiated.',
            'proof_note':'../1980/EXPLORATION_WEAK_INPUT_ORDER_GEOMETRY.md',
            'scope':'Refutes the proposed79-operation relation on arbitrary positive I,F. Does not refute a variant with separately enforced Boolean I. The valid80 source is unchanged.'}


if __name__=='__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status'],result['operations'],result['primitive_histogram'],
          result['unknown_count'],'unknowns;',result['equations'],'equations',flush=True)
