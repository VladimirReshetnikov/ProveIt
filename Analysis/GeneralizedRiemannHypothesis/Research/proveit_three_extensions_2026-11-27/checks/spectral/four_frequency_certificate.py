#!/usr/bin/env python3
"""Exact outward-rounded certificate for four wide arithmetic frequencies.

Replay uses only the Python standard library. Generation additionally uses
NumPy and SciPy to propose roots and inverse Jacobians; those proposals are
then checked by the same integer-only verifier used for replay.
"""
from __future__ import annotations
import argparse, itertools, json, math, time
from fractions import Fraction
from pathlib import Path

if not __debug__:
    raise RuntimeError('Proof checks require assertions: run Python without -O.')

SCALE = 10**24

def floorq(a, b):
    return a // b

def ceilq(a, b):
    return -((-a) // b)

class I:
    __slots__ = ('lo', 'hi')
    def __init__(self, lo, hi=None, raw=False):
        if raw:
            self.lo, self.hi = lo, hi
        else:
            lo = Fraction(str(lo)) if not isinstance(lo, Fraction) else lo
            hi = lo if hi is None else Fraction(str(hi))
            self.lo = floorq(lo.numerator*SCALE, lo.denominator)
            self.hi = ceilq(hi.numerator*SCALE, hi.denominator)
        assert self.lo <= self.hi
    @staticmethod
    def cv(x):
        return x if isinstance(x, I) else I(x)
    def __add__(self, other):
        o=I.cv(other); return I(self.lo+o.lo,self.hi+o.hi,True)
    __radd__=__add__
    def __neg__(self): return I(-self.hi,-self.lo,True)
    def __sub__(self, other): return self+-I.cv(other)
    def __rsub__(self, other): return I.cv(other)+-self
    def __mul__(self, other):
        o=I.cv(other); a=[self.lo*o.lo,self.lo*o.hi,self.hi*o.lo,self.hi*o.hi]
        return I(floorq(min(a),SCALE),ceilq(max(a),SCALE),True)
    __rmul__=__mul__
    def __truediv__(self, other):
        o=I.cv(other)
        assert not o.lo<=0<=o.hi
        if o.hi<0:return (-self)/(-o)
        return self*I(floorq(SCALE*SCALE,o.hi),ceilq(SCALE*SCALE,o.lo),True)
    def __rtruediv__(self, other):return I.cv(other)/self
    def __pow__(self,n):
        assert n>=0
        out=I(1);v=self
        while n:
            if n&1:out=out*v
            n//=2
            if n:v=v*v
        return out
    def mag(self):return max(abs(self.lo),abs(self.hi))
    def mid(self):return (self.lo+self.hi)//2
    def __repr__(self):return f'[{self.lo/SCALE:.9g},{self.hi/SCALE:.9g}]'

ZERO=I(0);ONE=I(1)

def sincos(v):
    v=I.cv(v); mid=v.mid(); rad=max(v.hi-mid,mid-v.lo)
    y=I(mid,mid,True)/16
    assert y.mag()<=3*SCALE, 'Taylor argument outside certified range'
    yy=y*y
    ss=y; cc=ONE; st=y; ct=ONE
    for k in range(1,25):
        st=-st*yy/((2*k)*(2*k+1)); ss=ss+st
        ct=-ct*yy/((2*k-1)*(2*k)); cc=cc+ct
    # sin through 49 and cos through 48; both remainders < 10^-35
    assert Fraction(3**50,math.factorial(50))<Fraction(1,10**35)
    err=I(-1,1,True)
    ss=ss+err;cc=cc+err
    for _ in range(4):ss,cc=2*ss*cc,cc*cc-ss*ss
    lip=I(-rad,rad,True)
    return ss+lip,cc+lip

def sinc(v):
    v=I.cv(v); mid=v.mid();rad=max(v.hi-mid,mid-v.lo)
    y=I(mid,mid,True)
    assert y.mag()<=4*SCALE,'sinc Taylor argument outside certified range'
    yy=y*y; out=ONE; term=ONE
    for k in range(1,31):
        term=-term*yy/((2*k)*(2*k+1));out=out+term
    assert Fraction(4**62,math.factorial(63))<Fraction(1,10**40)
    # sinc(v)=int_0^1 cos(tv)dt has derivative bounded by 1/2.
    rad=ceilq(rad,2)+1
    return out+I(-rad,rad,True)

def values(e,z,s):
    a,b,c=z[:3]
    se,ce=sincos(e*s)
    s1,c1=sincos((1+e)*s);s2,c2=sincos((2+e)*s);s3,c3=sincos((3+e)*s)
    f=s*sinc(e*s)+a*c1+b*s2+c*c3
    fp=ce-a*(1+e)*s1+b*(2+e)*c2-c*(3+e)*s3
    fpp=-e*se-a*(1+e)**2*c1-b*(2+e)**2*s2-c*(3+e)**2*c3
    return f,fp,fpp,(c1,s2,c3),(-(1+e)*s1,(2+e)*c2,-(3+e)*s3),(ce,s1,c2,s3)

def equations(e,z):
    p=[values(e,z,t) for t in z[3:6]]
    x=values(e,z,z[6])
    return [q[0] for q in p]+[q[1] for q in p]+[x[0]]

def jacobian(e,z):
    mat=[]
    p=[values(e,z,t) for t in z[3:6]]
    for j,q in enumerate(p):
        row=list(q[3])+[ZERO]*4;row[3+j]=q[1];mat.append(row)
    for j,q in enumerate(p):
        row=list(q[4])+[ZERO]*4;row[3+j]=q[2];mat.append(row)
    q=values(e,z,z[6]);mat.append(list(q[3])+[ZERO]*3+[q[1]])
    return mat

def determinant(m):
    n=len(m);out=ZERO
    for p in itertools.permutations(range(n)):
        inv=sum(p[i]>p[j] for i in range(n) for j in range(i+1,n))
        t=I(-1 if inv%2 else 1)
        for i,j in enumerate(p):t=t*m[i][j]
        out=out+t
    return out

def verify_cell(cell, full=True):
    e=I(cell['e0'],cell['e1']);z0=[I(v) for v in cell['z']]
    rr=I(cell['r']);assert rr.lo>0
    rad=rr.hi;z=[q+I(-rad,rad,True) for q in z0]
    R=[[I(v) for v in row] for row in cell['R']]
    g=equations(e,z0);J=jacobian(e,z)
    qmax=0
    for i in range(7):
        shift=sum(R[i][j]*g[j] for j in range(7)).mag()
        qsum=0
        for k in range(7):
            qsum+=(I(int(i==k))-sum(R[i][j]*J[j][k] for j in range(7))).mag()
        assert qsum<SCALE,('contraction',i,qsum/SCALE)
        assert shift+ceilq(rad*qsum,SCALE)<rad,('inclusion',i,shift/SCALE,rad/SCALE,qsum/SCALE)
        qmax=max(qmax,qsum)
    if not full:return {'q':qmax/SCALE}
    a,b,c,u,v,w,x=z
    assert x.lo>-2*SCALE and x.hi<0 and u.lo>0
    assert u.hi<v.lo and v.hi<w.lo and w.hi<5*SCALE
    assert (e*w).hi<I('1.57').lo # < pi/2; pi>3.14
    # A common tail bound: |A|+|B|+|C|<63/11=2*9/(22/7).
    assert a.mag()+b.mag()+c.mag()<I(Fraction(63,11)).lo
    nodes=[x,u,v,w]
    pv=[values(e,z,t) for t in nodes]
    M=[[q[3][i] for q in pv] for i in range(3)]
    cof=[determinant([[M[i][k] for k in range(4) if k!=j] for i in range(3)])*((-1)**j) for j in range(4)]
    assert all(c.hi<0 for c in cof),('dual weights',cof)
    odd=[[q[5][i] for q in pv] for i in range(4)]
    assert determinant(odd).lo>0,'odd determinant'
    shoulder=I(Fraction(1,8)).lo
    near=[I(t.lo-shoulder,t.hi+shoulder,True) for t in nodes]
    for j,t in enumerate(near):
        val=values(e,z,t)[1 if j==0 else 2]
        assert val.lo>0,('local positivity',j,val)
    e_low=Fraction(cell['e0'])
    top=Fraction(9) if e_low==0 else min(Fraction(9),Fraction(11,7)/e_low)
    top=I(top).hi
    intervals=[(near[j].hi,near[j+1].lo) for j in range(3)]+[(near[-1].hi,top)]
    visits=0
    for left,right in intervals:
        stack=[(left,right,0)]
        while stack:
            l,r,depth=stack.pop();visits+=1
            assert l<r
            val=values(e,z,I(l,r,True))[0]
            if val.lo>0:continue
            assert depth<24,('global positivity',float(e_low),I(l,r,True),val)
            m=(l+r)//2;stack.extend([(l,m,depth+1),(m,r,depth+1)])
    return {'q':qmax/SCALE,'positivity_boxes':visits}

def proposal(left,right):
    import numpy as np
    from scipy.optimize import root
    e=float((left+right)/2)
    def val(z,s):
        a,b,c=z[:3]
        f=s*np.sinc(e*s/np.pi)+a*np.cos((1+e)*s)+b*np.sin((2+e)*s)+c*np.cos((3+e)*s)
        fp=np.cos(e*s)-a*(1+e)*np.sin((1+e)*s)+b*(2+e)*np.cos((2+e)*s)-c*(3+e)*np.sin((3+e)*s)
        fpp=-e*np.sin(e*s)-a*(1+e)**2*np.cos((1+e)*s)-b*(2+e)**2*np.sin((2+e)*s)-c*(3+e)**2*np.cos((3+e)*s)
        return f,fp,fpp
    def eq(z):
        p=[val(z,t) for t in z[3:6]]
        return np.array([q[0] for q in p]+[q[1] for q in p]+[val(z,z[6])[0]])
    guess=np.array([2.01044,-1.02658,-1.97555,.06613,2.07567,4.01747,-1.42490])*(1-3*e)+np.array([1.98839,-1.66831,-1.73364,.17527,1.85090,3.51382,-1.23915])*(3*e)
    sol=root(eq,guess,tol=1e-11);z=sol.x
    assert np.linalg.norm(eq(z))<1e-9
    J=[]
    for j,s in enumerate(z[3:6]):
        row=[np.cos((1+e)*s),np.sin((2+e)*s),np.cos((3+e)*s)]+[0]*4
        row[3+j]=val(z,s)[1];J.append(row)
    for j,s in enumerate(z[3:6]):
        row=[-(1+e)*np.sin((1+e)*s),(2+e)*np.cos((2+e)*s),-(3+e)*np.sin((3+e)*s)]+[0]*4
        row[3+j]=val(z,s)[2];J.append(row)
    s=z[6];J.append([np.cos((1+e)*s),np.sin((2+e)*s),np.cos((3+e)*s),0,0,0,val(z,s)[1]])
    R=np.linalg.inv(J)
    return {'e0':str(left),'e1':str(right),'z':[format(x,'.18g') for x in z], 'r':str((right-left)*32+Fraction(1,10**12)), 'R':[[format(v,'.18g') for v in row] for row in R]}

def generate(path):
    todo=[(Fraction(0),Fraction(1,3))];cells=[];start=time.time();failures=0
    while todo:
        left,right=todo.pop();cell=proposal(left,right)
        try:
            stats=verify_cell(cell)
        except AssertionError as ex:
            failures+=1
            assert right-left>Fraction(1,10**7),(left,right,ex)
            mid=(left+right)/2;todo.extend([(mid,right),(left,mid)])
            if failures%50==0:print('refinements',failures,'accepted',len(cells),'time',round(time.time()-start,1),flush=True)
            continue
        cells.append(cell)
        if len(cells)%25==0:
            Path(path).write_text(json.dumps(cells,indent=1))
            print('accepted',len(cells),'epsilon',float(right),'time',round(time.time()-start,1),stats,flush=True)
    Path(path).write_text(json.dumps(cells,indent=1))
    print('CERTIFIED',len(cells),'cells; seconds',round(time.time()-start,1),flush=True)

def replay(path):
    cells=json.loads(Path(path).read_text());last=Fraction(0);count=0;q=0;start=time.time()
    for i,c in enumerate(cells):
        assert Fraction(c['e0'])==last,'gap or overlap in coverage'
        last=Fraction(c['e1']);assert last>Fraction(c['e0'])
        stat=verify_cell(c);count+=stat['positivity_boxes'];q=max(q,stat['q'])
        if (i+1)%50==0:print('checked',i+1,'of',len(cells),flush=True)
    assert last==Fraction(1,3)
    print(json.dumps({'status':'PASS','cells':len(cells),'parameter_interval':['0','1/3'],'positivity_boxes':count,'largest_contraction_bound':q,'seconds':round(time.time()-start,2)},indent=2))

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('action',choices=['generate','replay']);p.add_argument('--cells',default=str(Path(__file__).with_name('four_frequency_cells.json')));a=p.parse_args()
    (generate if a.action=='generate' else replay)(a.cells)
