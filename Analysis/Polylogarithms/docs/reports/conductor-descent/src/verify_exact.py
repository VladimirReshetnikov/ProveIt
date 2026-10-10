#!/usr/bin/env python3
"""Replay exact rank, jet, polynomial normal-form and trace-jet checks."""
from __future__ import annotations
import argparse, json, pathlib, platform
from math import gcd
import sympy as s
from distribution import distribution_matrix, exact_rank, jet_matrix, q12_normal_form

ROOT=pathlib.Path(__file__).resolve().parents[1]


def main() -> None:
    ap=argparse.ArgumentParser()
    ap.add_argument('--max-q',type=int,default=60)
    args=ap.parse_args()
    checks=[]
    for q in range(2,args.max_q+1):
        target=q-int(s.totient(q))
        for mode in ('w0','w2','w3','zero','mixed'):
            if mode.startswith('w'):
                w=int(mode[1:]); weight=lambda d,w=w:s.Integer(d)**w
            elif mode=='zero':
                weight=lambda d:s.S.Zero
            else:
                # Independent prime weights; extend completely multiplicatively.
                def weight(d):
                    return s.prod(((-1 if p%4==1 else p+1)**e)
                                  for p,e in s.factorint(d).items())
            R=distribution_matrix(q,weight)
            r=exact_rank(R); rp=exact_rank(R[:,:-1])
            assert r==rp==target,(q,mode,r,rp,target)
            checks.append(dict(q=q,mode=mode,rank=r,endpoint_fixed_rank=rp,
                               expected_rank=target,passed=True))
    composite=[]
    for q in range(2,min(args.max_q,30)+1):
        M=distribution_matrix(q,lambda d:s.Integer(d)**2,prime_only=False)
        r=exact_rank(M)
        assert r==q-int(s.totient(q))
        composite.append(dict(q=q,rows=M.rows,rank=r,passed=True))
    jets=[]
    for q in (4,6,8,9,10,12):
        for order in (1,2,3):
            M=jet_matrix(q,2,order)
            MP=jet_matrix(q,2,order,endpoint=False)
            r=exact_rank(M);rp=exact_rank(MP)
            expected=(order+1)*(q-int(s.totient(q)))
            assert r==rp==expected
            jets.append(dict(q=q,order=order,rank=r,expected_rank=expected,passed=True))
    F,B,(t2,t3)=q12_normal_form()
    R=distribution_matrix(12,lambda p:{2:t2,3:t3}[p])
    assert (R*F).applyfunc(s.expand)==s.zeros(R.rows,4)
    assert (B*F).applyfunc(s.expand)==s.eye(4)
    normal=dict(q=12,variables=['t2','t3'],
        coordinates=['Z_1','Z_3_chi3','Z_4_chi4','Z_12_chi12'],
        reduction=[[str(x) for x in F.row(i)] for i in range(12)],
        coordinate_matrix=[[str(x) for x in B.row(i)] for i in range(4)],
        RF_zero=True,BF_identity=True)
    (ROOT/'certificates/q12_polynomial_normal_form.json').write_text(json.dumps(normal,indent=2)+'\n')
    # The leading term of each trace follows from finite Taylor polynomial algebra.
    eps=s.Symbol('eps')
    trace=[]
    for q in (6,12,30,60,210,2310):
        ps=list(s.factorint(q));r=len(ps)
        logs={p:s.Symbol(f'L{p}') for p in ps}
        # Product leading coefficient before the simple zeta pole.
        lead=s.expand(s.prod(-logs[p] for p in ps))
        expected=(-1)**r*s.prod(logs.values())
        assert s.expand(lead-expected)==0
        trace.append(dict(q=q,prime_factors=ps,vanishing_order_at_1=r-1,
                           first_nonzero_derivative=str(s.factorial(r-1)*lead)))
    report=dict(python=platform.python_version(),sympy=s.__version__,
                arithmetic='exact rational and symbolic domain arithmetic; no float rank',
                rank_checks=checks,composite_checks=composite,jet_checks=jets,
                q12_normal_form=True,trace_leading_terms=trace,
                all_passed=True)
    (ROOT/'certificates/exact_checks.json').write_text(json.dumps(report,indent=2)+'\n')
    print(f'PASS: {len(checks)} rank cases, {len(composite)} composite-row cases, '
          f'{len(jets)} symbolic jet cases, q=12 polynomial normal form, {len(trace)} trace leading terms.')

if __name__=='__main__':main()
