#!/usr/bin/env python3
"""Independent finite-torus checks of the literal coefficient evaluator."""
from pathlib import Path
import sys,json,random
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'compiler'));sys.path.insert(0,str(ROOT/'geometry'));sys.path.insert(0,str(ROOT/'gates'))
import literal_loader as ll
import periodic_router as pr
import check_gates as gg


def require(ok,detail):
    if not ok:raise AssertionError(detail)

class Small:
    def __init__(self):
        self.N=2;self.es=(pr.Edge(0,'R',1,'L',-2,1),pr.Edge(1,'R',0,'L',2,1))
        self.M=len(self.es);self.B=48*(self.N+1);self.P=(7*self.B,4*self.B,336*self.M+84)
    def edges(self):return iter(self.es)

def main():
    c=Small();support,_,periods=pr.compile_support(['WIRE']*2,list(c.edges()),False)
    cases=set(support)
    for p in support:
        for d in pr.STEP:
            cases.add(tuple((p[i]+d[i])%periods[i] for i in range(3)))
    checked=0
    for p in sorted(cases):
        require(ll.background_height(p,c)==support.get(p,0),('coefficient mismatch',p))
        checked+=1
    # Exact all-axis period invariance, including negative representatives.
    rng=random.Random(811)
    for p in rng.sample(sorted(cases),min(500,len(cases))):
        v=tuple(p[i]+rng.randrange(-2,3)*periods[i] for i in range(3))
        require(ll.background_height(v,c)==support.get(p,0),('period mismatch',p,v))
    actual=ll.Circuit()
    for i in (0,21,33,34,34+actual.A-1,34+actual.A,34+actual.A+actual.O-1,34+actual.A+actual.O,actual.N-1):
        kind=ll.kind_at(actual,i)
        for dx in range(-14,15):
            for dy in range(-14,4):
                point=(24+48*i+dx,24+dy,0)
                require(ll.background_height(point,actual)==pr.primitive(kind).get((dx,dy,0),0),('fixed gate mismatch',i,point))
    pair_cases=0
    for ell in ('','0','1','01010'):
        for r in ('','0','1','100100'):
            seeds=ll.tape_pair_loader(ell,r,actual);init,L,R=ll.ca.initialize_pair(ell,r)
            expected=[(x*actual.B+24+48*s,24,0) for x,s in sorted(init.items())]
            require(seeds==expected,('loader mismatch',ell,r))
            require(len(seeds)==len(set(seeds))<=len(ell)+len(r)+7,'non-distinct/too-large loader')
            require(all(ll.background_height(p,actual)==5 for p in seeds),'seed not on height5')
            encoded='1'*len(ell)+'0'+ell+r
            require(ll.load_binary_input(encoded,actual)==seeds,'binary parser mismatch')
            pair_cases+=1
    # Numeric prism ledger on an exhaustive bounded grid of valid inequalities.
    prism_cases=0
    for l in range(8):
        for r in range(8):
            L=min(-3,-l-1);R=max(3,r+1);n=l+r
            for T in range(12):
                for p in range(-T,T+1):
                    H=2*T+max(p-L,R-p);lo=2*L-2*T-p+1;hi=2*R+2*T-p-1
                    require(H<=n+3+3*T and hi-lo<=2*n+4*T+10,'prism algebra')
                    V=(actual.B*(hi-lo+5)+1)*(actual.B*(H+1)+1)*(336*actual.M+53)
                    C=80*actual.B**2*(336*actual.M+53)
                    require(V<=C*(n+T+1)**2,'quadratic bound')
                    prism_cases+=1
    rejected=[]
    def reject(name,fn):
        try:fn()
        except (AssertionError,ValueError):rejected.append(name)
        else:raise AssertionError(('tamper accepted',name))
    reject('duplicate port',lambda:pr.compile_support(['WIRE'],[pr.Edge(0,'L',0,'R'),pr.Edge(0,'L',0,'R')]))
    reject('unsupported offset',lambda:pr.compile_support(['WIRE'],[pr.Edge(0,'L',0,'R',3,1)]))
    reject('same endpoint twice',lambda:pr.compile_support(['WIRE'],[pr.Edge(0,'L',0,'L')]))
    reject('invalid port',lambda:pr.compile_support(['WIRE'],[pr.Edge(0,'L',0,'B')]))
    reject('non-axis segment',lambda:list(pr.segment((0,0,0),(1,1,0))))
    reject('malformed input',lambda:ll.load_binary_input('1100',actual))
    old=gg.gate
    def badgate(kind):
        b,ports=old(kind)
        if kind=='AND':b[(0,0,0)]=5
        return b,ports
    gg.gate=badgate
    try:reject('AND threshold tamper',gg.verify)
    finally:gg.gate=old
    old=gg.diode
    def baddiode():
        b,ports=old();b[(0,0,0)]=5;return b,ports
    gg.diode=baddiode
    try:reject('diode threshold tamper',gg.verify)
    finally:gg.diode=old
    out=dict(status='PASS',torus_periods=periods,all_support_and_halo_queries=checked,
             period_shift_queries=500,fixed_primitive_plane_cases=9*29*18,
             pair_loader_cases=pair_cases,prism_integer_cases=prism_cases,
             rejected_tamper_cases=rejected,normal_optimized_checks_use_explicit_exceptions=True)
    (ROOT/'compiler'/'coefficient_checks.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
if __name__=='__main__':main()
