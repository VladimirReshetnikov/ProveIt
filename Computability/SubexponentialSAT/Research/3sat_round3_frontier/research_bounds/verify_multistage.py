#!/usr/bin/env python3
"""Original exact rational checks; no imported proposal code is executed.
Finite checks certify constants and parameter inequalities, not upstream identities.
"""
from fractions import Fraction as F
from math import isqrt, log, sqrt, pi
import json
from pathlib import Path

def require(condition, message="Exact verification failed"):
    if not condition:
        raise RuntimeError(message)

def sqrt_interval(x, places=40):
    scale=10**places
    k=isqrt((x.numerator*scale*scale)//x.denominator)
    lo,hi=F(k,scale),F(k+1,scale)
    require(lo*lo<=x<hi*hi)
    return lo,hi

def atan_interval(x,n=30):
    # Even number of terms: lower alternating truncation; odd: upper.
    lo=sum((-1)**j*x**(2*j+1)/F(2*j+1) for j in range(2*n))
    hi=lo+x**(4*n+1)/F(4*n+1)
    return lo,hi
al,ah=atan_interval(F(1,5));bl,bh=atan_interval(F(1,239))
pi_lo,pi_hi=16*al-4*bh,16*ah-4*bl
# ln(2)=2 atanh(1/3), positive series and geometric tail envelope.
N=60
ln_lo=2*sum(F(1,(2*j+1)*3**(2*j+1)) for j in range(N))
ln_hi=ln_lo+F(2,2*N+1)*F(1,3**(2*N+1))/F(8,9)
require(F(314159,100000)<pi_lo<pi_hi<F(314160,100000))
require(F(693147,1000000)<ln_lo<ln_hi<F(693148,1000000))
q=F(763,1000)
qlo,qhi=sqrt_interval(q)
root_time_factor=pi_hi/ln_lo

def certificate(name,rs,As,Astar,target,lowdegree):
    vs=[A-(As[j-1] if j else 0) for j,A in enumerate(As)]
    vtail=(Astar-As[-1])*(1-q)
    require(all(v>0 for v in vs) and vtail>0)
    mass=F(1); upper=F(0); display=0.;rows=[]
    for j,(r,A,v) in enumerate(zip(rs,As,vs)):
        n,d=A.numerator,A.denominator
        if lowdegree:
            valid=pow(r,2*n)<pow(2,d-n)
            condition='r^(2 numerator(A)) < 2^(denominator(A)-numerator(A))'
        else:
            mult=20 if j==0 else 10
            valid=pow(r,mult*n)<pow(2,d)
            condition=f'r^({mult} numerator(A)) < 2^denominator(A)'
        require(valid)
        sqlo,sqhi=sqrt_interval(F(2)*(1-F(1,r))/v)
        upper+=mass*root_time_factor*sqhi
        term=float(mass)*pi/log(2)*sqrt(float(F(2)*(1-F(1,r))/v));display+=term
        rows.append({'depth':j,'r':r,'A':str(A),'u_fraction':str(v),'path_mass':str(mass),'coefficient_display':term,'exact_capacity_check':valid,'condition':condition})
        mass*=F(2,r)
    n,d=Astar.numerator,Astar.denominator
    tailvalid=pow(3,2*n)<pow(2,d-n) if lowdegree else pow(3,10*n)<pow(2,d)
    require(tailvalid)
    sqlo,sqhi=sqrt_interval(F(4,3)/vtail)
    denlo=1-F(2,3)/qlo
    require(denlo>0 and q>F(7,10))
    upper+=mass*root_time_factor*sqhi/denlo
    taildisplay=float(mass)*pi/log(2)*sqrt(float(F(4,3)/vtail))/(1-F(2,3)/sqrt(float(q)))
    display+=taildisplay
    require(upper<target)
    if lowdegree:require(As[0]>F(1,12) and Astar<F(9,10))
    else:require(Astar+F(1,5)<1 and Astar<F(9,10))
    return {'name':name,'C_display':display,'exact_rational_upper':str(upper),'upper_decimal_display':float(upper),'safe_certificate':target,'rows':rows,'tail':{'r':3,'A_infinity':str(Astar),'q':str(q),'u_first_fraction':str(vtail),'path_mass':str(mass),'coefficient_display':taildisplay,'exact_capacity_check':tailvalid},'exact_certificate_passed':True}

generic=certificate('generic maxdegree s^(9/10)',[13,14,8,6,5,4],list(map(F,['.01351','.02626','.03333','.03868','.04306','.04999'])),F('.06308'),64,False)
low=certificate('root maxdegree s^(1/12)',[35,11,7,6,5,4],list(map(F,['.08881','.12627','.15116','.16206','.17717','.19999'])),F('.2398'),24,True)
# Independent leading-term check via 500 exact geometric entries.
for c in [generic,low]:
    tail=c['tail'];m=F(tail['path_mass']);v=F(tail['u_first_fraction']); partial=0
    for j in range(500):
        partial+=float(m)*pi/log(2)*sqrt(float(F(4,3)/v));m*=F(2,3);v*=q
    require(abs(partial-tail['coefficient_display'])<1e-12)
# Negative controls use exact bad capacity/target cases, not floating displays.
negative=0
for name,rs,As,cap,target,is_low in [
    ('bad generic root',[13,14,8,6,5,4],['.014','.02626','.03333','.03868','.04306','.04999'],'.06308',64,False),
    ('false generic target',[13,14,8,6,5,4],['.01351','.02626','.03333','.03868','.04306','.04999'],'.06308',63,False),
    ('bad lowdegree root',[35,11,7,6,5,4],['.1','.12627','.15116','.16206','.17717','.19999'],'.2398',24,True),
    ('false lowdegree target',[35,11,7,6,5,4],['.08881','.12627','.15116','.16206','.17717','.19999'],'.2398',23,True),
]:
    try:
        certificate(name,rs,list(map(F,As)),F(cap),target,is_low)
    except RuntimeError:
        negative+=1
require(negative==4)
out={'negative_controls_rejected':negative,'status':'pass','scope':'Exact schedules and rounded coefficient certificates only; no imported package executed.','certificates':[generic,low],'leading_capacity_rows':14,'exact_math':'Fractions, integer powers and isqrt; Machin pi intervals and atanh log(2) intervals.'}
path=Path(__file__).with_name('multistage_checks.json');path.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'status':'pass','generic':generic['C_display'],'lowdegree':low['C_display'],'safe':[64,24],'file':str(path)},indent=2))
