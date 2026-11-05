#!/usr/bin/env python3
"""Bounded exact dyadic and modular checks for a symbolic graph witness."""
import hashlib,json,math,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('Use python3 -I -S -B without optimization')
def require(x,s):
    if not x:raise RuntimeError(s)
# A dyadic is (positive integer mantissa, integer binary exponent).
# Products round outward at B mantissa bits; no floating arithmetic is used.
B=256
def times(x,y,up):
    v=x[0]*y[0];e=x[1]+y[1]; shift=max(0,v.bit_length()-B)
    if shift:
        v=(v+((1<<shift)-1) if up else v)>>shift;e+=shift
    return v,e
def power(x,n,up):
    r=(1,0)
    while n:
        if n&1:r=times(r,x,up)
        n//=2
        if n:x=times(x,x,up)
    return r
def lt(x,y):
    # Compare without converting to floats or constructing huge powers.
    lx=x[0].bit_length()+x[1];ly=y[0].bit_length()+y[1]
    if lx!=ly:return lx<ly
    if x[1]>=y[1]:return (x[0]<<(x[1]-y[1]))<y[0]
    return x[0]<(y[0]<<(y[1]-x[1]))
def root_bounds(d):
    v=math.isqrt(d<<(2*B))
    return (v,-B),(v+1,-B)
def add_n_root(n,lo,hi):return ((n<<B)+lo[0],-B),((n<<B)+hi[0],-B)
def pair_mul(x,y,d,mod):
    a,b=x;c,e=y
    return (a*c+d*b*e)%mod,(a*e+b*c)%mod
def pair_power(x,n,d,mod):
    r=(1,0)
    while n:
        if n&1:r=pair_mul(r,x,d,mod)
        n//=2
        if n:x=pair_mul(x,x,d,mod)
    return r
q,Y,X,U,a,n,H,D,P=3,27,6,729,189,191,759,36480,4374
j,m=2446738,4020619
require(Y==q**3 and X==2*q,'old q-cube coordinates')
require(X==2*q and U==Y*Y and a==Y*(X+1) and H==4*a+3 and D==n*n-1 and P==X*U,'parameters')
require(m%4==3 and j>=100 and m>=100 and 2*j>m,'index constraints')
# alpha=n+sqrt(D); beta=2P+1+2sqrt(P(P+1)).
# alpha,beta>2. Their inverse-power corrections are below eps=2^-200.
Dlo,Dhi=root_bounds(D);E=P*(P+1);Elo,Ehi=root_bounds(E)
al,ah=add_n_root(n,Dlo,Dhi)
bl=((2*P+1)*(1<<B)+2*Elo[0],-B)
bh=((2*P+1)*(1<<B)+2*Ehi[0],-B)
epsfactor=((1<<200)-1,-200)
# (1-eps)*alpha^m*sqrt(E) > 27*beta^j*sqrt(D).
left=times(times(power(al,m,False),Elo,False),epsfactor,False)
right=times(times(power(bh,j,True),Dhi,True),(27,0),True)
require(lt(right,left),'lower Pell ratio')
# alpha^m*sqrt(E) < 28*(1-eps)*beta^j*sqrt(D).
left2=times(power(ah,m,True),Ehi,True)
right2=times(times(times(power(bl,j,False),Dlo,False),epsfactor,False),(28,0),False)
require(lt(left2,right2),'upper Pell ratio')
# Exact rank moduli; no 1.3-million-bit coordinates are constructed.
gH,cH=pair_power((n,1),m,D,H)
d=(gH-X-a*cH)%H; dh=math.gcd(U,H)
require(d%(H//dh)==0,'main quotient integrality')
Amod=(U//dh)*(d//(H//dh))%U
kmod=2*j%U
require((kmod-1+Amod-m)%U==0,'gamma integrality')
cU=pair_power((n,1),m,D,U)[1]
require((gH,cH,d,dh,Amod,kmod,cU)==(488,538,506,3,486,428,115),'expected residues')
c31=pair_power((n,1),m,D,31)[1]
f2_31=(1+D*pow(c31,4,31))%31
require(c31==29 and f2_31==13 and pow(f2_31,15,31)==30,'nonsquare certificate')
result={'status':'PASS_BOUNDED_ARITHMETIC_CHECKS_ONLY',
 'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 'q':q,'Y':Y,'free_f2_is_nonsquare_mod_31':True,'first_index':j,'main_index':m,
 'dyadic_mantissa_bits':B,'proved_ratio_bounds':'27 < c/k < 28',
 'c_mod_31':c31,'F2_mod_31':f2_31,'main_pair_mod_H':[gH,cH],'main_difference_mod_H':d,'gcd_U_H':dh,
 'A_mod_U':Amod,'k_mod_U':kmod,'c_mod_U':cU,'m_mod_U':m%U,
 'ports':{'beta':2,'K0':1,'MC':m-40,'MF':0},
 'scope':'Exact bounded dyadic and modular inputs for the free-f² symbolic full-zero argument in README; that argument is not Lean-checked.'}
print(json.dumps(result,indent=2,sort_keys=True))
