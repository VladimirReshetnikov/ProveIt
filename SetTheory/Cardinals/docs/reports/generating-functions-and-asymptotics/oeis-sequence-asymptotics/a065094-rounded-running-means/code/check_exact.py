#!/usr/bin/env python3
"""Exact official-data, finite Laguerre, sum and symbolic Casoratian checks."""
from fractions import Fraction as F
from math import factorial,comb
from pathlib import Path
import json
import sys
sys.dont_write_bytecode=True
ROOT=Path(__file__).absolute().parent.parent
sys.path.insert(0,str(ROOT))
from verify_manifest import load_json,read_regular
from certify_amplitudes import check


def sequence(mode,N):
    check(mode in ('floor','ceiling') and type(N) is int and N>=1,'invalid sequence request')
    a=total=1
    arr=[a]
    for n in range(1,N):
        a+=(total+(n-1 if mode=='ceiling' else 0))//n
        total+=a
        arr.append(a)
    return arr


def check_bfile(text,mode):
    rows=[]
    for line in text.splitlines():
        if line.strip() and not line.lstrip().startswith('#'):
            row=line.split()
            check(len(row)==2,'b-file must have two columns')
            rows.append(tuple(map(int,row)))
    check([r[0] for r in rows]==list(range(1,1001)),'b-file index coverage')
    check([r[1] for r in rows]==sequence(mode,1000),'official b-file terms disagree')
    return len(rows)


def check_casoratian(P,Q,maximum):
    for n in range(1,maximum+1):
        value=tuple(n*(P[n+1]*Q[n][j]-P[n]*Q[n+1][j]) for j in (0,1))
        check(value==(0,1),f'Casoratian mismatch at {n}')


def exact_checks(root=ROOT):
    prefixes=load_json(read_regular(root/'data/oeis_prefixes.json'))
    check(set(prefixes)=={'A065094','A065095'},'official prefix inventory')
    lengths={}
    for sid,mode in [('A065094','floor'),('A065095','ceiling')]:
        expected=prefixes[sid]['terms']
        check(isinstance(expected,list) and len(expected)>=20 and all(type(v) is int for v in expected), 'invalid official prefix')
        check(sequence(mode,len(expected))==expected,'official prefix mismatch: '+sid)
        lengths[sid]=len(expected)
        check_bfile(read_regular(root/('data/b'+sid[1:]+'.txt')).decode('ascii'),mode)
    P=[F(0),F(1)];S=[F(0),F(1)]
    for n in range(1,151):
        P.append(P[n]+S[n]/n);S.append(S[n]+P[n+1])
    for n in range(1,151):
        check(P[n]==sum((F(comb(n-1,k),factorial(k)) for k in range(n)),F(0)),f'Laguerre explicit {n}')
        check(S[n]==n*(P[n+1]-P[n]),f'sum identity {n}')
    # Q_n=u_n*q+v_n, treating q=exp(1) E1(1) as a formal indeterminate.
    Q=[(F(0),F(0)),(F(1),F(0)),(F(2),F(-1))]
    for n in range(2,151):
        Q.append(tuple(2*Q[n][j]-F(n-1,n)*Q[n-1][j] for j in (0,1)))
    check_casoratian(P,Q,150)
    return {'status':'PASS','arithmetic':'integer and Fraction only',
            'official_prefix_lengths':lengths,'bfile_terms_per_sequence':1000,
            'Laguerre_finite_sum_n_max':150,'sum_identity_n_max':150,'symbolic_Casoratian_n_max':150}


if __name__=='__main__':
    print(json.dumps(exact_checks(),indent=2,sort_keys=True))
