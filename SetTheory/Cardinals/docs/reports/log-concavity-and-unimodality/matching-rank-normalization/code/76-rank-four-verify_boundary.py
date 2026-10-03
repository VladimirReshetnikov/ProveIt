"""Exact checks for the complete 2 by s stability boundary."""
from itertools import combinations
from math import comb
from fractions import Fraction
from pathlib import Path
import json
from verify_complete_core import match

def graph_check(s,n,m):
    left=n+2;right=s+m;total=left+right
    rows=[(1<<right)-1]*2+[(1<<s)-1]*n
    actual=set();p=[0]*(min(left,right)+1)
    for I in range(1<<left):
        ix=[i for i in range(left) if I>>i&1]
        for cols in combinations(range(right),len(ix)):
            J=sum(1<<j for j in cols)
            if match(tuple(rows[i]&J for i in ix)):
                actual.add((((1<<left)-1)^I)|(J<<left));p[len(ix)]+=1
    U={0,1}|set(range(left+s,total))
    expected={sum(1<<i for i in B) for B in combinations(range(total),left) if len(set(B)&U)<=2}
    assert actual==expected,(s,n,m)
    M=m+2;N=n+s;r=n+2
    c0=comb(N,r);c1=M*comb(N,r-1);c2=comb(M,2)*comb(N,r-2)
    disc=c1*c1-4*c0*c2
    criterion=M*(n+2)*s-2*(M-1)*(n+1)*(s-1)
    assert (disc>=0)==(criterion>=0)
    assert (disc==0)==(criterion==0)
    while len(p)>1 and p[-1]==0:p.pop()
    return p

if __name__=='__main__':
    for s in range(2,5):
        for n in range(5):
            for m in range(5):graph_check(s,n,m)
    p=graph_check(3,6,6)
    assert p==[1,36,333,974,1005,300]
    points=list(map(Fraction,[-2,-1]))+[Fraction(-1,2),Fraction(-1,5),Fraction(-1,20),Fraction(0)]
    values=[sum(a*t**k for k,a in enumerate(p)) for t in points]
    assert values==[Fraction(-51),Fraction(29),Fraction(-33,16),Fraction(21,25),Fraction(-1329,16000),Fraction(1)]
    assert 288**2-4*9*2352==-1728
    report={'small_graphs_checked':75,'additional_17_vertex_graph':True,'basis_identity':True,'stability_threshold':True,'unit_coefficients':p,'root_certificate':[[str(t),str(v)] for t,v in zip(points,values)],'block_diagonal_discriminant':-1728}
    Path(__file__).with_name('boundary_verification.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
