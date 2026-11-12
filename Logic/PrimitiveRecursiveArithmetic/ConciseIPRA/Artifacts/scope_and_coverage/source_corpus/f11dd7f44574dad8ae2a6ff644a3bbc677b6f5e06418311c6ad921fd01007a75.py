"""Independent standard-model check of literal self-seeded source macros.
This is finite transcription evidence, not a proof of metatheory.
"""
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parent

def F(n,h):
    out=1+h(0)
    for _ in range(n):out=h(out)
    return out

def eps(a,b):return int(a==b)
def D(n,a):return F(n,lambda v:a)
def neg(b):return eps(b,0)
def band(b,c):return eps(D(b,eps(c,0)),0)
def bor(b,c):return neg(band(neg(b),neg(c)))
def mux(c,p,q):return bor(band(c,p),band(neg(c),q))
def W(a):return F(a,lambda v:D(eps(v+1,a),v))
def P(a):return 0 if a<2 else 1 if a==2 else W(a)
def C(n,a):return F(n,lambda v:D(eps(v,a+2),v))
def L(a,n):return eps(C(n,a),a+2)
def Q(n):return F(n,lambda v:v+2)
def Sel(cap,c,a,d):
    return W(W(F(cap,lambda v:D(mux(c,eps(v,a+2),eps(v,d+2)),v))))

def bounded_iter(n,a,b,h):
    B=b+2
    seed=C(a,b)
    def update(u):
        return Sel(B,eps(u,2),C(h(0),b),
                   Sel(B,eps(u,3),C(h(1),b),C(h(W(W(u))),b)))
    def H(u):
        return Sel(B+2,eps(u,0),B,
                   Sel(B+2,eps(u,B+1),B+2,
                       Sel(B+2,eps(u,B+2),seed,update(u))))
    out=F(n+2,H)
    return P(P(out))

def main():
    rows=[]
    def check(group,args,got,want):
        if got!=want:raise AssertionError((group,args,got,want))
        rows.append({'group':group,'arguments':args,'actual':got,'expected':want})
    for n in range(20):
        check('predecessor',[n],P(n),max(0,n-1))
        check('double_offset',[n],Q(n),2*n+3)
        for a in range(12):
            check('capped_count',[n,a],C(n,a),2+min(n,a))
            check('order',[a,n],L(a,n),int(a<=n))
    for cap in range(2,10):
        for a in range(2,cap+1):
            for d in range(2,cap+1):
                for c in (0,1):check('selector',[cap,c,a,d],Sel(cap,c,a,d),a if c else d)
    for b in range(4):
        for a in (0,1,3,5):
            for name,h in [('zero',lambda v:0),('identity',lambda v:v),('successor',lambda v:v+1),('double_offset',Q),('large_constant',lambda v:9)]:
                want=min(a,b)
                for n in range(4):
                    check('bounded_iteration',[n,a,b,name],bounded_iter(n,a,b,h),want)
                    want=min(h(want),b)
    counts={}
    for row in rows:counts[row['group']]=counts.get(row['group'],0)+1
    result={'status':'PASS','expectations':len(rows),'counts':counts,'scope':'Finite standard-model checks of literal source macros. This does not prove universal soundness, nonstandard-domain round trips, or bi-interpretability.','rows':rows}
    (ROOT/'source_macro_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='rows'},indent=2))

if __name__=='__main__':main()
