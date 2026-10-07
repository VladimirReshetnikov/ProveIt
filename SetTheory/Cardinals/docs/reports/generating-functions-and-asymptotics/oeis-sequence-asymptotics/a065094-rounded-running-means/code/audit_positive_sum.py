#!/usr/bin/env python3
"""Independent N=10000 audit using finite positive sums and division remainders.

No call to the primary factorial-scaled three-term recurrence is made here.
The published A endpoints and widths are checked against independent fractions.
The transformed C and c endpoints are checked by the primary rational certificate.
"""
from fractions import Fraction as F
from math import factorial
from pathlib import Path
import json
import sys
sys.dont_write_bytecode=True
ROOT=Path(__file__).absolute().parent.parent
sys.path.insert(0,str(ROOT))
from verify_manifest import load_json,read_regular


def check(condition,message):
    if not condition:
        raise ArithmeticError(message)


def positive_sum_state(N):
    check(type(N) is int and N>=2,'N must be an integer at least 2')
    fact=factorial(N-1)
    pterm=fact;P=pterm
    for j in range(1,N):
        numerator=pterm*(N-j)
        check(numerator%(j*j)==0,'nonintegral P finite-sum term')
        pterm=numerator//(j*j);P+=pterm
    check(pterm==1,'incorrect P terminal term')
    tterm=N*fact;T=tterm
    for j in range(1,N):
        numerator=tterm*(N-j)
        check(numerator%(j*(j+1))==0,'nonintegral T finite-sum term')
        tterm=numerator//(j*(j+1));T+=tterm
    check(tterm==1,'incorrect T terminal term')
    return fact,P,T


def validate_certificate(cert,state=None):
    check(type(cert.get('N')) is int and cert['N']==10000 and cert.get('digits')==70,'unexpected certificate precision')
    N=cert['N']
    fact,P,T=positive_sum_state(N) if state is None else state
    results={}
    for mode in ('floor','ceiling'):
        a=S=1;prefix=[1]
        for n in range(1,N):
            quotient,remainder=divmod(S,n)
            a+=quotient+(mode=='ceiling' and remainder!=0)
            S+=a
            if len(prefix)<50:prefix.append(a)
        saved=cert['sequences'][mode]
        check(a==int(saved['a_N']) and S==int(saved['sum_N']),'final sequence state mismatch')
        check(prefix==saved['prefix'],'published prefix mismatch')
        l,u=(-1,0) if mode=='floor' else (0,1)
        lower=F((S+N*l)*fact,T);upper=F((S+N*u)*fact,T)
        check(0<lower<upper,'invalid independent interval')
        check(F(saved['A'][0])<=lower<upper<=F(saved['A'][1]),'A endpoints fail independent enclosure')
        check(upper-lower==F(N*fact,T),'independent width mismatch')
        check(upper-lower<=F(saved['width_A_upper']),'published width too narrow')
        check(lower==min(F((a+l)*fact,P),F((S+N*l)*fact,T)),'lower cone selection mismatch')
        check(upper==max(F((a+u)*fact,P),F((S+N*u)*fact,T)),'upper cone selection mismatch')
        results[mode]={'exact_state':'PASS','positive_finite_sum':'PASS','amplitude_enclosure':'PASS',
                       'cone_selection':'PASS','width_upper':'PASS'}
    return {'status':'PASS','N':N,'arithmetic':'integer and Fraction only',
            'independent_P_and_T_positive_sum':True,'sequences':results}


if __name__=='__main__':
    cert=load_json(read_regular(ROOT/'certificates/amplitude_certificate.json'))
    print(json.dumps(validate_certificate(cert),indent=2,sort_keys=True))
