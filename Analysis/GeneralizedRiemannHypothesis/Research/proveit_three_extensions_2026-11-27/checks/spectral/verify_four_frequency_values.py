#!/usr/bin/env python3
"""Verify point roots and numerical constants using exact interval arithmetic.

No NumPy, SciPy, or mpmath is imported by this replay program.
"""
import json
from fractions import Fraction
from pathlib import Path
from four_frequency_certificate import I, SCALE, equations, jacobian, sincos, verify_cell

def atan_bounds(q, n=70):
    s=Fraction(0)
    for k in range(n):s+=(-1)**k*Fraction(1,(2*k+1)*q**(2*k+1))
    t=(-1)**n*Fraction(1,(2*n+1)*q**(2*n+1))
    return min(s,s+t),max(s,s+t)

def pi_bounds():
    a,b=atan_bounds(5);c,d=atan_bounds(239)
    return I(16*a-4*d,16*b-4*c)

def outward(v,digits=17):
    k=10**digits
    lo=(v.lo*k)//SCALE
    hi=-((-v.hi*k)//SCALE)
    def fmt(n):
        sign='-' if n<0 else '';n=abs(n)
        return f'{sign}{n//k}.{n%k:0{digits}d}'
    return [fmt(lo),fmt(hi)]

def derivative_e_at_zero(z):
    a,b,c=z[:3]
    def at(s):
        s1,c1=sincos(s);s2,c2=sincos(2*s);s3,c3=sincos(3*s)
        f=-a*s*s1+b*s*c2-c*s*s3
        fp=-a*(s1+s*c1)+b*(c2-2*s*s2)-c*(s3+3*s*c3)
        return f,fp
    vals=[at(s) for s in z[3:6]]
    return [v[0] for v in vals]+[v[1] for v in vals]+[at(z[6])[0]]

def replay(path=None):
    path=Path(path) if path else Path(__file__).with_name('four_frequency_point_witnesses.json')
    data=json.loads(path.read_text());pi=pi_bounds();results={}
    for label,cell in data['points'].items():
        verify_cell(cell)
        r=I(cell['r']).hi
        z=[I(v)+I(-r,r,True) for v in cell['z']]
        if label=='zero':
            results['x_zero']=outward(z[6]);results['c1']=outward(-z[6]/pi)
            J=jacobian(I(0),z);R=[[I(v) for v in row] for row in cell['R']]
            v0=[I(v) for v in data['derivative_zero']]
            ge=derivative_e_at_zero(z)
            residual=[sum(J[i][j]*v0[j] for j in range(7))+ge[i] for i in range(7)]
            err=max(sum(R[i][j]*residual[j] for j in range(7)).mag() for i in range(7))
            q=max(sum((I(int(i==k))-sum(R[i][j]*J[j][k] for j in range(7))).mag() for k in range(7)) for i in range(7))
            assert q<SCALE
            err=-((-err*SCALE)//(SCALE-q))
            dx=v0[6]+I(-err,err,True)
            results['xprime_zero']=outward(dx);results['c2']=outward(-dx/pi)
        else:
            m=int(label)
            assert Fraction(cell['e0'])==Fraction(1,m)==Fraction(cell['e1'])
            results['gap_m_'+label]=outward(I(Fraction(1,2))-z[6]/(pi*m))
    print(json.dumps({'status':'PASS','enclosures':results},indent=2))
    return results

if __name__=='__main__':replay()
