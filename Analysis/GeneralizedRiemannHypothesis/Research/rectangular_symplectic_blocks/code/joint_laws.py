#!/usr/bin/env python3
"""Exact joint law of ordinary nullity and translated-Gram nullity.

The mixed moments use an isometric restriction and an independent smaller
rectangular matrix. The direct-enumeration program checks this separately.
"""
from fractions import Fraction as F
from pathlib import Path
import csv
import json
from exact_laws import qbin, subspace_type, emb, laws, gamma, theta, dec, exact_string


def joint_law(q,a,b):
    base=laws(q,a,b)
    # Mixed Gaussian moments, using only the even index for the alternating variable.
    moments={}
    for j in range(0,b+1,2):
        types=[]
        for s in range(j//2+1):
            n=subspace_type(q,b,j,s)
            if not n:
                continue
            shift=2*j-2*s
            weight=F(n*emb(q,a,j,s),q**((a+b)*j-j*j))
            if weight: types.append((shift,weight))
        moments[j]=[sum((weight*F(qbin(q,b-shift,i),q**((a-shift)*i))
                         for shift,weight in types),F(0)) for i in range(b+1)]
    # Invert the rank variable first.
    intermediate={}
    for j,arr in moments.items():
        p=[F(0)]*(b+1)
        for i in range(b,-1,-1):
            p[i]=arr[i]-sum((qbin(q,k,i)*p[k] for k in range(i+1,b+1)),F(0))
        assert all(v>=0 for v in p)
        intermediate[j]=p
    # Invert on the even nullity grid in the second variable.
    joint=[[F(0)]*(b+1) for _ in range(b+1)]
    for k in range(b+1):
        for j in range(b,-1,-2):
            joint[k][j]=intermediate[j][k]-sum((qbin(q,l,j)*joint[k][l]
                                              for l in range(j+2,b+1,2)),F(0))
    assert all(x>=0 for row in joint for x in row)
    assert sum(map(sum,joint))==1
    assert [sum(row) for row in joint]==base['rank_iid']
    assert [sum(joint[k][l] for k in range(b+1)) for l in range(b+1)]==base['defect']
    dependence=sum((abs(joint[k][l]-base['rank_iid'][k]*base['defect'][l])
                    for k in range(b+1) for l in range(b+1)),F(0))/2
    return dict(q=q,a=a,b=b,joint=joint,dependence_tv=dependence)


def main():
    out=Path(__file__).resolve().parents[1]/'results'
    cases=[(2,2,2),(2,4,2),(2,4,4),(2,6,2),(3,2,2),(3,4,2)]
    cases += [(2,b+d,b) for b in (2,4,6,8,12,16,24) for d in (0,2,6,16)]
    cases += [(q,b+d,b) for q in (3,4) for b in (2,4,8,12) for d in (2,6)]
    cases=list(dict.fromkeys(cases))
    rows=[]; detail=[]
    for q,a,b in cases:
        x=joint_law(q,a,b)
        lead=2*q*theta(q,80)*gamma(q,160)/((q-1)*gamma(q,a-b)*q**a)
        rows.append(dict(q=q,a=a,b=b,joint_tv=dec(x['dependence_tv']),leading=dec(lead),
                         ratio=dec(x['dependence_tv']/lead),
                         scaled_error=dec((x['dependence_tv']-lead)*q**(a+b))))
        if (q,a,b) in cases[:6] or (q,a,b)==(2,26,24):detail.append(exact_string(x))
    with (out/'joint_table.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
    (out/'joint_exact.json').write_text(json.dumps(detail,indent=2)+'\n')
    (out/'joint_verification.json').write_text(json.dumps({'status':'PASS','cases':len(cases),
        'checks':['nonnegative joint mass','normalization','both marginals'],'arithmetic':'exact rational'},indent=2)+'\n')
    print('PASS:',len(cases),'exact joint distributions')
    for x in rows:
        if (x['q'],x['a'],x['b'])==(2,26,24):print(json.dumps(x))


if __name__=='__main__':main()
