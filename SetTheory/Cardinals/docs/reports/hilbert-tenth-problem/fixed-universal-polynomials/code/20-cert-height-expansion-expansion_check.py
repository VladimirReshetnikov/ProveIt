#!/usr/bin/env python3
"""Independent bounded Decimal checks of the author's analytic identities.
No upstream imports/code/schedules, no complete witness tuples. Decimal checks
corroborate the analytic proof and are not interval-arithmetic certification.
"""
from decimal import Decimal, localcontext
from fractions import Fraction
from math import comb
import json

D=Decimal
COUNT=0

def need(ok,message):
    global COUNT
    COUNT+=1
    if not ok:raise ValueError(message)

def log1p(z):
    total=D(0); power=z; j=1
    threshold=abs(z)*D(10)**(-440)
    while True:
        term=power/D(j)
        total+=term if j%2 else -term
        if abs(term)<threshold:return total
        power*=z;j+=1
        need(j<1000,'log1p iteration cap')

def log1m(z):return log1p(-z)

def g(z):
    total=D(0); power=z;j=1
    threshold=abs(z)*D(10)**(-440)
    while True:
        cj=D(comb(2*j,j))/D(2*j*4**j)
        term=cj*power;total-=term
        if abs(term)<threshold:return total
        power*=z;j+=1
        need(j<1000,'g iteration cap')

def params(branch,R):
    if branch=='A+':return D(2)*(R+1)/3,(R+1)/3-1
    if branch=='A-':return D(2)*(R-1)/3,(R-1)/3-1
    return D(5)*(R+1)/7,D(15)*(R+1)/28-1

def poly(branch,R):
    if branch=='A+':return (4*R**3+4*R**2-7*R-1)/3
    if branch=='A-':return (4*R**3-12*R**2+9*R-1)/3
    return (25*R**3+25*R**2-39*R-11)/14

def derivative(branch,R):
    if branch=='A+':return (12*R**2+8*R-7)/3
    if branch=='A-':return (12*R**2-24*R+9)/3
    return (75*R**2+50*R-39)/14

def second(branch,R):
    if branch=='A+':return 8*R+D(8)/3
    if branch=='A-':return 8*R-8
    return (150*R+50)/14

def calc(branch,R):
    ln2=D(2).ln();p,y=params(branch,R);L=p+y+1;B=2*p*(R-1)
    X=(p*ln2).exp();Y=(y*ln2).exp();d=1/X+2/(X*Y)
    A=X*Y+Y+2;a=1/(A*A)
    # Reference uses direct roots at 450-digit working precision.
    lamA=A+(A*A-1).sqrt()
    Z=(p*lamA.ln()).exp()
    S=(Z-1/Z)**2/4;b=1/(S*S)
    lamS=S+(S*S-1).sqrt()
    u=(-2*p*lamA.ln()).exp();v=(-2*R*lamS.ln()).exp()
    logH=(R*lamS.ln()+log1m(v)-(2*(S*S-1).sqrt()).ln())/ln2
    E=(B*(log1p(d)+g(a))+2*(R-1)*log1m(u)+R*g(b)-log1m(b)/2+log1m(v))/ln2
    N=poly(branch,R)
    tol=D('1e-420')
    need(abs(logH-N-E)<tol,'exact analytic identity')
    need(abs(E-B*d/ln2)<B*d*d/ln2,'uniform first-order remainder')
    for z in [a,u,b,v]:need(0<z<=d*d/16,'sector size bound')
    need(derivative(branch,R)>3*R*R,'N prime lower')
    need(0<second(branch,R)<12*R,'N second bound')
    need(B<2*R*R,'B bound')
    series=[]
    for k in [1,2,4]:
        total=D(0)
        for j in range(1,k+1):
            cj=D(comb(2*j,j))/D(2*j*4**j)
            total+=(B*(1 if j%2 else -1)*d**j/D(j)-B*cj*a**j-2*(R-1)*u**j/D(j)+(D(1)/(2*j)-R*cj)*b**j-v**j/D(j))
        tail=(B*d**(k+1)/D(k+1)+B*a**(k+1)/(2*(k+1)*(1-a))+2*(R-1)*u**(k+1)/((k+1)*(1-u))+(R+1)*b**(k+1)/(2*(k+1)*(1-b))+v**(k+1)/((k+1)*(1-v)))
        need(abs(total-E*ln2)<=tail,'order '+str(k)+' tail bound')
        series.append({'order':k,'error_to_bound':format(abs(total-E*ln2)/tail,'.12E')})
    gamma=D(4)/3 if branch.startswith('A') else D(25)/14
    r0=((logH/gamma).ln()/3).exp()
    for _ in range(25):r0-=(poly(branch,r0)-logH)/derivative(branch,r0)
    need(abs(poly(branch,r0)-logH)<tol,'cubic inverse residual')
    p0,y0=params(branch,r0)
    q0=(-p0*ln2).exp();Y0=(y0*ln2).exp()
    T0=2*p0*(r0-1)*q0/(ln2*derivative(branch,r0))
    inverse_bound=64*(q0/Y0+q0*q0)
    inverse_error=abs(R-r0+T0)
    need(inverse_error<=inverse_bound,'inverse first-sector bound')
    need(r0>R and r0-R<2*d,'inverse localization')
    return {'branch':branch,'R':str(R),'log_correction':format(E,'.12E'),'leading_relative_error':format(abs(E-B*d/ln2)/(B*d/ln2),'.12E'),'series':series,'inverse_error_to_bound':format(inverse_error/inverse_bound,'.12E')}

def polynomial_coefficients():
    def plus(a,b):
        c=dict(a)
        for k,v in b.items():c[k]=c.get(k,Fraction(0))+v
        return c
    def times(a,b):
        c={}
        for i,x in a.items():
            for j,y in b.items():c[i+j]=c.get(i+j,Fraction(0))+x*y
        return c
    def scale(a,b):return {k:v*b for k,v in a.items()}
    fixtures=[
      ('A+',Fraction(4,3),Fraction(4,3),Fraction(-7,3),Fraction(-1,3),Fraction(-1,3),Fraction(25,36),Fraction(-11,81)),
      ('A-',Fraction(4,3),Fraction(-4),Fraction(3),Fraction(-1,3),Fraction(1),Fraction(1,4),Fraction(0)),
      ('B',Fraction(25,14),Fraction(25,14),Fraction(-39,14),Fraction(-11,14),Fraction(-1,3),Fraction(142,225),Fraction(-104,2025)),
    ]
    for name,a,b,c,d,shift,u,v in fixtures:
        r={1:Fraction(1),0:shift,-1:u,-2:v}
        r2=times(r,r);r3=times(r2,r)
        result=plus(plus(scale(r3,a),scale(r2,b)),plus(scale(r,c),{0:d,3:-a}))
        for j in [3,2,1,0]:need(result.get(j,0)==0,'exact Puiseux coefficient '+name)
    return len(fixtures)

def run():
    with localcontext() as ctx:
        ctx.prec=450;ctx.Emax=999999999;ctx.Emin=-999999999
        records=[calc(branch,D(R)) for branch in ['A+','A-','B'] for R in [100,200,300]]
    coefficients=polynomial_coefficients()
    return {'status':'PASS','scope':'450-digit bounded numerical corroboration, not interval certification; analytic proof supplies rigorous bounds. No giant integers or complete tuples.','active_checks':COUNT,'decimal_precision':450,'records':records,'exact_rational_Puiseux_branches':coefficients}

if __name__=='__main__':print(json.dumps(run(),indent=2,sort_keys=True))
