#!/usr/bin/env python3
"""Exact rational Banach certificate for a five-point stencil with two blind modes.

Uses Python's standard library only. No floating-point value participates in any
assertion.  Decimal output is diagnostic, not part of the proof.

For intervals I and a centre m, sin(I), cos(I) are enclosed by the rational
Taylor polynomial at m, a Lagrange remainder bound, and the radius of I,
using |sin'|, |cos'| <= 1. log(k) uses the positive arctanh series at
r=(k-1)/(k+1), with its geometric tail bound.
"""
from fractions import Fraction as Q
from math import factorial, isqrt
from decimal import Decimal, localcontext
import json
import sys

class I:
    def __init__(self, lo, hi=None):
        self.lo=Q(lo); self.hi=Q(lo if hi is None else hi)
        assert self.lo<=self.hi
    def __add__(self,other):
        other=lift(other);return I(self.lo+other.lo,self.hi+other.hi)
    __radd__=__add__
    def __neg__(self):return I(-self.hi,-self.lo)
    def __sub__(self,other):return self+-lift(other)
    def __rsub__(self,other):return lift(other)+-self
    def __mul__(self,other):
        other=lift(other);v=[a*b for a in (self.lo,self.hi) for b in (other.lo,other.hi)]
        return I(min(v),max(v))
    __rmul__=__mul__
    def __truediv__(self,other):
        other=lift(other);assert not(other.lo<=0<=other.hi)
        return self*I(1/other.hi,1/other.lo)
    def norm(self):return max(abs(self.lo),abs(self.hi))

def lift(x):return x if isinstance(x,I) else I(x)

def sqrt_interval(x, digits=35):
    """Outward rational square-root enclosure via integer square roots."""
    x=lift(x);assert x.lo>=0
    scale=10**digits
    lo=isqrt((x.lo.numerator*scale*scale)//x.lo.denominator)
    hi=isqrt((x.hi.numerator*scale*scale)//x.hi.denominator)+1
    return I(Q(lo,scale),Q(hi,scale))

def broad_interval(x,digits=7):
    """Outward decimal-grid endpoints, retained as exact rational strings."""
    scale=10**digits
    lo=(x.lo.numerator*scale)//x.lo.denominator
    hi=-((-x.hi.numerator*scale)//x.hi.denominator)
    return [str(Q(lo,scale)),str(Q(hi,scale))]
def log_integer(k,n=110):
    r=Q(k-1,k+1)
    val=sum((2*r**(2*j+1)/Q(2*j+1) for j in range(n)),Q(0))
    rem=2*r**(2*n+1)/(Q(2*n+1)*(1-r*r))
    return I(val,val+rem)

def sincos(x,n=70):
    x=lift(x);m=(x.lo+x.hi)/2;rad=(x.hi-x.lo)/2
    ss,cc=Q(0),Q(0);ts,tc=m,Q(1)
    for j in range(n):
        ss+=ts;cc+=tc
        ts*= -m*m/Q((2*j+2)*(2*j+3))
        tc*= -m*m/Q((2*j+1)*(2*j+2))
    # Taylor orders 2n and 2n-1 respectively; |all real derivatives| <= 1.
    es=abs(m)**(2*n+1)/factorial(2*n+1)
    ec=abs(m)**(2*n)/factorial(2*n)
    return I(ss-es-rad,ss+es+rad),I(cc-ec-rad,cc+ec+rad)

L2,L3=log_integer(2),log_integer(3)

def functions_and_jacobian(box):
    s,t,x,y=map(lift,box)
    A,B,C,D=-4+7*s-4*t,8-32*s+48*t,27*s-108*t,64*t
    values=[];J=[]
    for index,xi in enumerate((x,y)):
        s2,c2=sincos(xi*L2);s3,c3=sincos(xi*L3);s4,c4=sincos(2*xi*L2)
        values.extend([A+B*c2+C*c3+D*c4,B*s2+C*s3+D*s4])
        ds=[7-32*c2+27*c3,-32*s2+27*s3]
        dt=[-4+48*c2-108*c3+64*c4,48*s2-108*s3+64*s4]
        dx=[-B*L2*s2-C*L3*s3-2*D*L2*s4,B*L2*c2+C*L3*c3+2*D*L2*c4]
        for j in range(2):
            row=[ds[j],dt[j],I(0),I(0)];row[2+index]=dx[j];J.append(row)
    return values,J

CENTRE=list(map(Q,[
 '0.226581725372920248553022108864',
 '0.021509738593496195392746518501',
 '5.698378161005081978098269879203',
 '10.737241689185610111079863383138']))
PRECONDITIONER=[list(map(Q,row)) for row in [
 ['0.025037570749280074050563217188751','0.0071215534504792628723296683314581','-0.025966270813046925957730725806518','0.0044120601768797700071939788954142'],
 ['0.0040633077122905881298492621317585','0.0011557456331762572891094306460881','-0.011673287173868423562978173715599','0.0019834671618393550069168677632872'],
 ['-0.2146082035317926952599781102852','0.24879528879704599501885316900011','0.29582515222179256334077171615725','-0.05026514522760662868492987894397'],
 ['0.24223449289030709474103331939638','0.068899890725926906475116616799069','0.31506870860891928485286244558347','0.40346077690191140123969591917642']]]

def fmt(q):
    with localcontext() as ctx:
        ctx.prec=16
        return str(Decimal(q.numerator)/Decimal(q.denominator))

def main():
    radius=Q(1,10**10)
    box=[I(z-radius,z+radius) for z in CENTRE]
    fc,_=functions_and_jacobian(CENTRE)
    _,jx=functions_and_jacobian(box)
    residual=max(sum((PRECONDITIONER[i][k]*fc[k] for k in range(4)),I(0)).norm() for i in range(4))
    error_matrix=[[I(int(i==j))-sum((PRECONDITIONER[i][k]*jx[k][j] for k in range(4)),I(0)) for j in range(4)] for i in range(4)]
    contraction=max(sum((error_matrix[i][j].norm() for j in range(4)),Q(0)) for i in range(4))
    assert residual<Q(1,10**25)
    assert contraction<Q(1,10**5)
    assert residual+contraction*radius<radius
    # Entire parameter box is strictly in the feasible shape domain, with C nonzero.
    ss,tt=box[:2]
    assert 0<tt.lo and tt.hi<Q(1,6)
    assert (Q(1,2)+tt.lo)**2-ss.norm()**2>Q(1,5)
    assert (ss-4*tt).lo>Q(1,10)
    assert 5<box[2].lo<box[2].hi<6
    assert 10<box[3].lo<box[3].hi<11
    assert box[2].hi<box[3].lo
    # Reconstruct a real spectral factor and certify that all five weights are nonzero.
    disc=(1+2*tt)*(1+2*tt)-4*ss*ss
    yy=(1+2*tt-sqrt_interval(disc))/2
    uu=sqrt_interval(1-yy+2*tt)
    bb=ss/uu
    vv=sqrt_interval(1-yy-2*tt)
    aa,cc=(uu+vv)/2,(uu-vv)/2
    weights=[aa,bb-2*aa,cc-2*bb+aa,bb-2*cc,cc]
    assert all(w.lo>0 or w.hi<0 for w in weights)
    report={
      'status':'PASS',
      'arithmetic':'exact fractions; rational Taylor and arctanh remainder bounds',
      'centre':[str(x) for x in CENTRE],
      'box_radius':str(radius),
      'preconditioned_residual_bound':fmt(residual),
      'contraction_norm_bound':fmt(contraction),
      'image_radius_bound':fmt(residual+contraction*radius),
      'factor_coefficient_intervals':[broad_interval(w) for w in (aa,bb,cc)],
      'five_stencil_weight_intervals':[broad_interval(w) for w in weights],
      'certified_conclusion':'A unique zero of the four real equations lies in this box; its feasible five-point stencil has exactly two positive blind frequencies.',
      'proof':'Banach fixed point applied to x -> x-M F(x); ||I-M J||<1 implies M is nonsingular.'}
    print(json.dumps(report,indent=2))
    if len(sys.argv)>1:
        with open(sys.argv[1],'w') as f:json.dump(report,f,indent=2);f.write('\n')
if __name__=='__main__':main()
