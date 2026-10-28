#!/usr/bin/env python3
"""Exact weighted ten-group certificate for the 9/4 rectangular backend.

The source data contains the existing fixed nine plans and rational mixing
weights; the finite support certificate uses the stronger rectangular backend.
Only Python's standard library is required. All acceptance is exact.
"""
from fractions import Fraction
from itertools import combinations
from pathlib import Path
import json
import verify_new_backend as backend


def require(condition, message):
    if not condition:
        raise ValueError(message)


def certify(data):
    r=data['r']; plans=data['plans']; weights=data['weights']
    q=len(plans); W=sum(weights)
    require(r==10 and q==9,'Unexpected fixedmenu')
    require(len(weights)==q and all(type(w) is int and w>0 for w in weights),
            'Invalid fixedweights')
    require(W==data['weight_sum'],'Weightdenominator differs')
    menus=[backend.supports(r,p) for p in plans]
    require(all(len(m)==72 for m in menus),'Wrong support count')
    norms=[[backend.dot(v,v) for v in menu] for menu in menus]
    pairs=[]; count=0
    for i,j in combinations(range(q),2):
        wi,wj=weights[i],weights[j]
        best=None; witness=None
        for k,v in enumerate(menus[i]):
            for ell,w in enumerate(menus[j]):
                value=wi*wi*norms[i][k]+wj*wj*norms[j][ell]
                value+=2*(q-1)*wi*wj*backend.dot(v,w)
                if best is None or value>best:
                    best,witness=value,[k,ell]
                count+=1
        pairs.append({'i':i,'j':j,'maximum':best,'witness':witness})
    beta_squared=Fraction(2*sum(p['maximum'] for p in pairs),
                           (q-1)*W*W*backend.SCALE*backend.SCALE*r*r)
    require(beta_squared==Fraction(data['beta_squared']),
            'Declared squaredcoefficient differs from exhaustivecertificate')
    require([p['maximum'] for p in pairs]==data['pair_maxima'],
            'Pair maxima differ from stored certificate')
    return {'status':'PASS','groups':r,'plans':q,'weights':weights,
            'beta_squared':str(beta_squared),'pair_choices_checked':count,
            'pair_maxima':pairs}


def negative_controls(result):
    rejected=[]

    def must_reject(name, action):
        try:
            action()
        except ValueError:
            rejected.append(name)
        else:
            raise ValueError('Invalid certificate accepted: '+name)

    true=Fraction(result['beta_squared'])
    def check_bound(bound):
        require(true<=bound,'Proposed bound is below the exact required value')
    must_reject('squared_bound_lowered_by_1e-12',
                lambda:check_bound(true-Fraction(1,10**12)))

    original=backend.WEIGHTS[:]
    try:
        backend.WEIGHTS=[w for w in original if 0 not in w]
        must_reject('input_output_supports_removed',backend.verify_backend_supports)
    finally:
        backend.WEIGHTS=original[:]
    try:
        target=next(i for i,w in enumerate(original)
                    if w==(21_400_107,21_400_107,0))
        backend.WEIGHTS[target]=(21_400_108,21_400_107,0)
        must_reject('support_coefficient_altered',backend.verify_backend_supports)
    finally:
        backend.WEIGHTS=original[:]
    require(len(rejected)==3,'Negativecontrols incomplete')
    return rejected


def main():
    data_path = Path(__file__).resolve().parent.parent / 'data' / 'new_backend_weighted10.json'
    data = json.loads(data_path.read_text())
    result=certify(data)
    result['negative_controls_rejected']=negative_controls(result)
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
