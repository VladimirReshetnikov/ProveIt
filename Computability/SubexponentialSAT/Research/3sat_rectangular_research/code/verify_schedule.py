#!/usr/bin/env python3
"""Independent exact interval and packing-gate audit of the final schedules."""
from fractions import Fraction as F
from math import isqrt
from pathlib import Path
import json


def require(x,msg):
    if not x:raise ValueError(msg)


def add(x,y):return x[0]+y[0],x[1]+y[1]
def mul(x,y):return x[0]*y[0],x[1]*y[1]
def div(x,y):
    require(y[0]>0,'Division across zero')
    return x[0]/y[1],x[1]/y[0]
def val(x):return F(x),F(x)
def sqrt(x):
    x=F(x);d=10**45;lo=isqrt(x.numerator*d*d//x.denominator)
    return F(lo,d),F(lo+1,d)


def pi_ln2():
    def atan(q,n):
        a=sum((F((-1)**j,(2*j+1)*q**(2*j+1)) for j in range(n)),F(0))
        b=a+F((-1)**n,(2*n+1)*q**(2*n+1))
        return min(a,b),max(a,b)
    a,b=atan(5,80),atan(239,20)
    pi=(16*a[0]-4*b[1],16*a[1]-4*b[0])
    n=100;lo=2*sum((F(1,(2*j+1)*3**(2*j+1)) for j in range(n)),F(0))
    tail=2*F(1,3)**(2*n+1)/F(2*n+1)/F(8,9)
    return pi,(lo,lo+tail)


def describe(x):
    # The exact interval is the mathematical certificate; decimal is display.
    return {'lower':str(x[0]),'upper':str(x[1]),'display':float(x[0])}


def audit():
    root=Path(__file__).resolve().parent.parent / 'data'
    rows=json.loads((root/'new_backend_plans.json').read_text())
    bsq={row['r']:F(row['beta_squared']) for row in rows}
    bsq[10]=F(json.loads((root/'new_backend_weighted10.json').read_text())['beta_squared'])
    pi,ln2=pi_ln2();K=mul(div(pi,ln2),sqrt(2));q=F(63,100)
    logs={4:F(2),6:F(258497,100000),7:F(280736,100000),
          10:F(332193,100000),13:F(370044,100000),15:F(39069,10000)}
    for r,bound in logs.items():
        require(r**bound.denominator<=2**bound.numerator,'Incorrect log bound')
    specs=[('generic',[10,13,10,7],
            [F(301,20000),F(287,25000),F(357,100000),F(193,50000)],
            F(1,20),F(28633,1000)),
           ('lowdegree',[15,10,7,6],
            [F(2149,20000),F(2337,100000),F(407,20000),F(109,10000)],
            F(1,5),F(10337,1000))]
    answers=[]
    for name,rs,etas,cap,safe in specs:
        A=F(0);M=F(1);prefix=val(0);branches=[];spaces=[];gates=[]
        for depth,(r,eta) in enumerate(zip(rs,etas)):
            previous=A;A+=eta
            rounding=A*(1+2*logs[r]);fresh=previous+2*A*logs[r]
            if name=='generic':
                inherited=F(9,10)+(2 if depth==0 else 1)*A*logs[r]
            else:
                inherited=F(1,12)+2*A*logs[r]
            require(max(rounding,fresh,inherited)<1,'A finite-stage gate failed')
            gates.append({'depth':depth,'r':r,'eta':str(eta),
                          'cumulative':str(A),'rounding_gap':str(1-rounding),
                          'fresh_gap':str(1-fresh),'inherited_gap':str(1-inherited)})
            scale=div(mul(K,val(M)),sqrt(eta))
            local=mul(sqrt(bsq[r]),scale)
            branches.append(add(prefix,local));spaces.append(local)
            prefix=add(prefix,mul(sqrt(F(2*(r-1),r*r)),scale))
            M*=F(2,r)
        require(A<cap,'Tail has no budget')
        eta_tail=(cap-A)*(1-q)
        scale=div(mul(K,val(M)),sqrt(eta_tail))
        local=mul(sqrt(bsq[4]),scale)
        branches.append(add(prefix,local));spaces.append(local)
        gamma=div(val(F(1,2)),sqrt(q))
        one_minus_gamma=(1-gamma[1],1-gamma[0])
        multiplier=div(sqrt(F(3,8)),one_minus_gamma)
        require(multiplier[0]>sqrt(bsq[4])[1],'Tail maximum cannot be simplified')
        terminal=add(prefix,mul(multiplier,scale));branches.append(terminal)
        target=branches[0] if name=='generic' else terminal
        for other in branches:
            if other!=target:require(other[1]<target[0],'Dominant branch incorrect')
        require(target[1]<safe,'Safe coefficient exceeded')
        require(all(x[1]<spaces[0][0] for x in spaces[1:]),'Space root not largest')
        require(q>F(11,20),'Tail taper fails bootstrap condition')
        # At the tail cap, the equality gate is controlled by lambda-sqrt(lambda).
        tail_gate=F(9,10)+2*cap if name=='generic' else 5*cap
        require(tail_gate==1,'Unexpected tail boundary')
        answers.append({'name':name,'r_prefix':rs,'etas':list(map(str,etas)),
                        'tail_eta0':str(eta_tail),'tail_ratio':str(q),
                        'tail_cap':str(cap),'gates':gates,
                        'branch_intervals':list(map(describe,branches)),
                        'space_intervals':list(map(describe,spaces)),
                        'dominant_time':'root' if name=='generic' else'terminal',
                        'safe_coefficient':str(safe),
                        'boundary_margin_required':'lambda-ceil(sqrt(lambda))'})
    return {'status':'PASS','schedules':answers}


if __name__=='__main__':print(json.dumps(audit(),indent=2))
