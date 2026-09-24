#!/usr/bin/env python3
"""Exact rejected79 schedule and a full-positive-extension counterexample.

The finite calculation checks all outer witnesses and every symbolic source
residual.  It verifies hypotheses of the existing positive Pell construction;
it deliberately does not materialize those enormous Pell witnesses.
"""
from pathlib import Path
from math import isqrt
import json
import sympy as sp

import round44_1980_two_auxiliary_history as previous
import round4_1980_operation_count as baseline
from round13_1980_certificate import verify_primitives

PARAMETERS=['I','F']
OUTER_NAMES=['q','v','quot','hrow','Bw','Cw','Yw','Uw','Vw','alphaI','lam']
CORE_NAMES=previous.CORE_NAMES
NAMES=PARAMETERS+OUTER_NAMES+CORE_NAMES
SYM={name:sp.Symbol(name) for name in NAMES}
OUTER=[
    ('Q2','*','q','q'),
    ('Q3','*','Q2','q'),
    ('Lbig','*','Q2','Q2'),
    ('n2','*','Lbig','Q3'),
    ('vq','*','v','quot'),
    ('v2','*','v','v'),
    ('W','*','v2','v2'),
    ('Qm1','-','q',1),
    ('Wm1','-','W',1),
    ('row_geom','*','hrow','Wm1'),
    ('sixteenC','*',16,'Cw'),
    ('thirtyoneB','*',31,'Bw'),
    ('fourY','*',4,'Yw'),
    ('life_lhs','+','thirtyoneB','fourY'),
    ('twoU','*',2,'Uw'),
    ('threeV','*',3,'Vw'),
    ('life_rhs0','+','Cw','twoU'),
    ('life_rhs','+','life_rhs0','threeV'),
    ('Ibound','+','I','alphaI'),
    ('WY','*','W','Yw'),
    ('time_lhs','+','I','WY'),
    ('QF','*','q','F'),
    ('time_rhs','+','Cw','QF'),
    ('Bh','+','Bw','hrow'),
    ('pack0','*','q','Bh'),
    ('pack1','+','Yw','pack0'),
    ('pack2','*','q','pack1'),
    ('pack3','+','Vw','pack2'),
    ('pack4','*','q','pack3'),
    ('packed','+','Uw','pack4'),
    ('fifteen_lam','*',15,'lam'),
    ('mask_scale','+','fifteen_lam',1),
    ('packing_gap','-','Lbig','packed'),
    ('r_product','*','packing_gap','fifteen_lam'),
    ('fourteen_lam','*',14,'lam'),
    ('r_lhs','+','r_product','fourteen_lam'),
]
CORE=previous.CORE
SCHEDULE=OUTER+CORE
EQUALITIES=[
    ('q','vq'),('Qm1','row_geom'),('Bw','sixteenC'),
    ('life_lhs','life_rhs'),('Ibound','v'),
    ('time_lhs','time_rhs'),('mask_scale','Lbig'),('r','r_lhs'),
]+previous.EQUALITIES[9:]


def source_residuals():
    z=SYM
    q,v,quot,H,B,C,Y,U,V,alphaI,lam=[z[name] for name in OUTER_NAMES]
    a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,ga,y=[z[name] for name in CORE_NAMES]
    W,L,scale=v**4,q**4,q**7
    P=U+q*V+q*q*Y+q**3*(B+H)
    Up,Yp=w*scale,s*scale
    Dpell=a*a+4*a+3
    K,aux_u=Dpell*(f*f-1),2*r+1+j*c
    return [
        q-v*quot,
        q-1-H*(W-1),
        B-16*C,
        31*B+4*Y-C-2*U-3*V,
        z['I']+alphaI-v,
        z['I']+W*Y-C-q*z['F'],
        15*lam+1-L,
        r-(L-P)*15*lam-14*lam,
        Up*Yp*Yp*(Up*Yp*Yp+1)*k*k-tau*(tau+1),
        c-Yp*k-eta,
        k-eta-zeta,
        k-r-1-h*Up*Yp,
        a-Yp*(Up+1),
        d-Up-a*c-ga*(4*a+3),
        d*d-Dpell*c*c-1,
        (i*c*c)**2-Dpell*(f*f-1),
        K*(aux_u*aux_u-y*y)-(1-y*y),
        aux_u-c-o*f,
    ]


def radix_digits(value, radix=16):
    result=[]
    while value:
        value,digit=divmod(value,radix)
        result.append(digit)
    return result


def verify():
    need=baseline.need
    env=dict(SYM)
    histogram=baseline.run_schedule(SCHEDULE,env)
    source=source_residuals()
    z=SYM; aux_u=2*z['r']+1+z['j']*z['c']
    correction=source[15]*(aux_u**2-z['y_aux']**2)
    records=[]
    need(len(source)==len(EQUALITIES)==18,'18 complete source equations')
    for index,((left,right),residual) in enumerate(zip(EQUALITIES,source)):
        actual=sp.expand(env[left]-env[right])
        adjustment=correction if index==16 else sp.Integer(0)
        if sp.expand(actual-residual-adjustment)==0:
            sign=1
        elif adjustment==0 and sp.expand(actual+residual)==0:
            sign=-1
        else:
            raise AssertionError('fresh source mismatch at '+str(index))
        records.append(dict(index=index,equality=[left,right],source_sign=sign,
                            source=sp.sstr(sp.expand(residual)),actual=sp.sstr(actual),
                            correction=sp.sstr(sp.expand(adjustment))))
    primitives,counts=verify_primitives(SCHEDULE,env)
    need(len(OUTER)==36 and len(CORE)==43,'36 outer and43 retained instructions')
    need(len(primitives)==79 and counts=={'+':33,'*':46},'exact79 arithmetic')
    need(len(OUTER_NAMES+CORE_NAMES)==28,'28 positive unknowns')
    need(all(p.free_symbols<=set(SYM.values()) for p in source),'declared source inputs')
    need(set(NAMES)<={x for row in SCHEDULE for x in row[2:]}|
         {x for pair in EQUALITIES for x in pair},'all supplied inputs used')
    need(sp.expand(env['n2']-z['q']**7)==0,'scale q7')
    need(sp.expand(env['W']-z['v']**4)==0,'row radix v4')

    values=dict(I=1,F=250609653,q=16777216,v=4,quot=4194304,
                hrow=65793,Bw=8208,Cw=513,Yw=16423954219010,
                Uw=14706018353152,Vw=12094593474557,alphaI=3)
    q=values['q']; W=values['v']**4; L=q**4; scale=q**7
    P=values['Uw']+q*values['Vw']+q*q*values['Yw']+q**3*(values['Bw']+values['hrow'])
    values['lam']=(L-1)//15
    values['r']=(L-P)*(L-1)+14*values['lam']
    subs={SYM[name]:value for name,value in values.items()}
    outer_residuals=[int(p.subs(subs)) for p in source[:8]]
    need(outer_residuals==[0]*8,'eight exact outer equations')
    need(all(value>0 for value in values.values()),'all supplied finite values positive')
    numeric_env=dict(values)
    baseline.run_schedule(OUTER,numeric_env)
    need(all(numeric_env[left]==numeric_env[right] for left,right in EQUALITIES[:8]),
         'actual outer schedule accepts tuple')
    ca,cb,cc=876547,720894,978944
    T0=1052945
    need(values['Uw']==q*ca and values['Vw']==q*cb-ca and
         values['Yw']==q*cc-cb and values['Bw']+values['hrow']+cc==T0,
         'all three explicit carries telescope')
    need(P==q**3*T0 and 0<P<L,'packed Boolean word below L')
    need(set(radix_digits(P))<={0,1},'full packed mask is Boolean')
    need(set(radix_digits(values['F']))-{0,1},'output parameter is not Boolean')
    n0=isqrt(scale); r=values['r']; J=2*r+1
    need(n0*n0==scale and n0>=64,'actual integral square scale')
    need(n0*n0<r<n0**3,'original positive Pell range')
    need(r%2==0 and P%2==0,'half-parameter parity')
    need(scale&(scale-1)==0,'scale power of two')
    need(r.bit_count()==scale.bit_length()-1,'exact central-binomial valuation')
    need(J>scale.bit_length()-1,'first exponential divisible by scale')
    return dict(status='COUNTEREXAMPLE_PASS',arithmetic_operations=79,
                primitive_histogram=counts,histogram=histogram,
                positive_unknowns=OUTER_NAMES+CORE_NAMES,unknown_count=28,equations=18,
                primitive_instructions=primitives,equalities=EQUALITIES,residuals=records,
                tuple=values,W=W,P=P,L=L,T0=T0,carries=[ca,cb,cc],
                outer_residuals=outer_residuals,output_radix16_digits=radix_digits(values['F']),
                pell_extension=dict(scale=scale,n0=n0,r_even=True,
                                    n0_squared_below_r=True,r_below_n0_cubed=True,
                                    central_binomial_valuation=r.bit_count(),
                                    scale_binary_exponent=scale.bit_length()-1,
                                    enormous_witnesses_materialized=False,
                                    justification='Original square-scale positive Pell necessity, with even r.'),
                proof_note='../1980/EXPLORATION_RADIX16_DELETED_HISTORY_BOUND.md',
                scope='This exact tuple refutes the radix16 four-field edit with deleted field bound. All79 primitive operations and18 source residuals are checked symbolically; eight outer equations are checked numerically. The full positive Pell extension is proved in the note, not materialized. The published80 system is unchanged.')


if __name__=='__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status'],result['arithmetic_operations'],result['primitive_histogram'])
    print('18 symbolic source comparisons;8 exact outer equations;positive Pell-extension hypotheses PASS')
