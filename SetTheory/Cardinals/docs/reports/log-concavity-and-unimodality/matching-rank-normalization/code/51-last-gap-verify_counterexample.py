"""Exact verification of the rank-49 separation counterexample. No dependencies."""
from math import comb
from fractions import Fraction as Q
from pathlib import Path
import json

def C(n,k):return comb(n,k) if 0<=k<=n else 0
def multiply(x,y):
    out=[Q(0)]*(len(x)+len(y)-1)
    for i,a in enumerate(x):
        for j,b in enumerate(y):out[i+j]+=a*b
    return out
def evaluate(p,w):
    out=0
    for v in p[::-1]:out=out*w+v
    return out
def coeff_polynomial(k):
    return [sum(C(14,i)*C(38,k-i)*C(35,j)*C(624,k-j)
                for i in range(15) if i+j>=k) for j in range(36)]

def main():
    D=C(38,35)*C(624,12)
    normalized={46:(32,[Q(8801172765,2),Q(32499495),Q(136955,2),Q(27846,613)]),
       47:(33,[Q(72736965),Q(299880),Q(273)]),
       48:(34,[Q(1258425,2),Q(1071)]),49:(35,[Q(14382,7)])}
    for k,(shift,p) in normalized.items():
        expected=[Q(0)]*shift+[D*v for v in p]
        assert coeff_polynomial(k)==expected
    q=[68528424519495225,331783888454280,673931488920,496441140,-13]
    for k,shift,factor,poly in [(47,66,Q(882,613),q),
                               (48,68,Q(89964),[48443370,47940,1])]:
        x=multiply(coeff_polynomial(k),coeff_polynomial(k))
        y=multiply(coeff_polynomial(k-1),coeff_polynomial(k+1))
        gap=[k*(49-k)*u-(k+1)*(50-k)*v for u,v in zip(x,y)]
        assert gap==[Q(0)]*shift+[factor*D*D*v for v in poly]
    assert evaluate(q,40000000)==-1506688736346303933404280504775
    assert evaluate(q,38189137)==358201675329747057329792
    assert evaluate(q,38189138)==-365864633482267706996743
    p=[evaluate(coeff_polynomial(k),40000000) for k in range(50)]
    gaps=[k*(49-k)*p[k]**2-(k+1)*(50-k)*p[k-1]*p[k+1] for k in range(1,49)]
    assert [k for k,v in enumerate(gaps,1) if v<0]==[47]
    V=[sum(C(14,s-i)*C(38,35-i) for i in range(s+1)) for s in range(4)]
    assert V==[8436,191919,2303028,19575738]
    limits=[]
    for s in [1,2]:
        L=s*(49-s)*(15-s)*V[s]**2
        R=(s+1)*(50-s)*(14-s)*V[s-1]*V[s+1]
        limits.append([L,L-R])
    assert limits[0][1]==0
    assert limits[1]==[6481412197854048,-10607875937568]
    L,delta=limits[1]
    assert delta*(623-12)+L>=0>delta*(624-12)+L
    result={'shape':[14,35,38,624],'rank':49,'vertices':711,'edges':10556,
      'weight':40000000,'negative_gap_indices':[47],
      'q_ascending':q,'q_at_weight':evaluate(q,40000000),
      'first_integer_weight':38189138,'q_before':evaluate(q,38189137),
      'q_at_first':evaluate(q,38189138),'D':D,'full_coefficients':p,
      'limiting_profile':V,'limiting_gap_data':limits}
    path=Path(__file__).resolve().parent/'data'/'verification.json'
    path.parent.mkdir(exist_ok=True)
    path.write_text(json.dumps(result,indent=2)+'\n')
    print('PASS: four coefficient identities, both gap factorizations, integer thresholds and all 48 gaps')

if __name__=='__main__':main()
