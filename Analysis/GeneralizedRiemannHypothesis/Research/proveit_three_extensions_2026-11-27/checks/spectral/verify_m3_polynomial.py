#!/usr/bin/env python3
"""Independent algebraic verification for frequencies {1,4,7,10}.

Works in x=cos(theta) with integer Chebyshev polynomials. It does not use
any trigonometric evaluation, the continuum witness, or its positivity
calculations. Python standard library only.
"""
import json
from pathlib import Path
from four_frequency_certificate import I,SCALE,determinant

T=[[0,1],[1,0,-8,0,8],[0,-7,0,56,0,-112,0,64],[-1,0,50,0,-400,0,1120,0,-1280,0,512]]
U=[[1],[0,-4,0,8],[-1,0,24,0,-80,0,64],[0,10,0,-160,0,672,0,-1024,0,512]]
def deriv(p):return [i*p[i] for i in range(1,len(p))]
DT=list(map(deriv,T));DDT=list(map(deriv,DT))
def poly(p,x):
    z=I(0)
    for a in reversed(p):z=z*x+a
    return z
def values(z,x):
    co=[I(1)]+z[:3]
    return tuple(sum(c*poly(p,x) for c,p in zip(co,ps)) for ps in (T,DT,DDT))
def jac(z):
    rows=[]
    for k,x in enumerate(z[3:6]):
        row=[poly(p,x) for p in T[1:]]+[I(0)]*4;row[3+k]=values(z,x)[1];rows.append(row)
    for k,x in enumerate(z[3:6]):
        row=[poly(p,x) for p in DT[1:]]+[I(0)]*4;row[3+k]=values(z,x)[2];rows.append(row)
    rows.append([poly(p,z[6]) for p in T[1:]]+[I(0)]*3+[values(z,z[6])[1]])
    return rows
def eq(z):
    a=[values(z,x) for x in z[3:6]]
    return [x[0] for x in a]+[x[1] for x in a]+[values(z,z[6])[0]]
def main():
    data=json.loads(Path(__file__).with_name('m3_polynomial_witness.json').read_text())
    z0=[I(t) for t in data['z']];r=I(data['r']).hi
    z=[t+I(-r,r,True) for t in z0];R=[[I(t) for t in row] for row in data['R']]
    J=jac(z);g=eq(z0)
    for i in range(7):
        q=sum((I(int(i==k))-sum(R[i][j]*J[j][k] for j in range(7))).mag() for k in range(7))
        d=sum(R[i][j]*g[j] for j in range(7)).mag()
        assert q<SCALE and d+(-((-r*q)//SCALE))<r
    nodes=[z[6]]+z[3:6]
    assert -SCALE<nodes[0].lo<0
    assert all(nodes[i].hi<nodes[i+1].lo for i in range(3)) and nodes[-1].hi<SCALE
    V=[[poly(p,x) for x in nodes] for p in T[1:]]
    minors=[((-1)**j)*determinant([[V[i][k] for k in range(4) if k!=j] for i in range(3)]) for j in range(4)]
    assert all(t.lo>0 for t in minors) or all(t.hi<0 for t in minors)
    odd=determinant([[poly(p,x) for x in nodes] for p in U])
    assert odd.lo>0 or odd.hi<0
    # Near the contacts, use exact double-zero equations and positive curvature.
    shoulder=I('0.01').lo
    near=[I(x.lo-shoulder,x.hi+shoulder,True) for x in nodes]
    def positive_on(left,right,index):
        stack=[(left,right,0)];n=0
        while stack:
            l,r,d=stack.pop();n+=1
            if values(z,I(l,r,True))[index].lo>0:continue
            assert d<30
            m=(l+r)//2;stack.extend([(l,m,d+1),(m,r,d+1)])
        return n
    count=0
    for i,x in enumerate(near):count+=positive_on(x.lo,x.hi,1 if i==0 else 2)
    for i in range(3):count+=positive_on(near[i].hi,near[i+1].lo,0)
    count+=positive_on(near[-1].hi,SCALE,0)
    print(json.dumps({'status':'PASS','method':'Chebyshev polynomial certificate; no trigonometric evaluation','frequency_set':[1,4,7,10],'positivity_boxes':count},indent=2))
if __name__=='__main__':main()
