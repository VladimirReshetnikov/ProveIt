#!/usr/bin/env python3
"""Independent corroborative complex-disk and Lagrange-tail checks.
No upstream imports or source-schedule execution. Floating calculations are
not interval-certified. The proof audit supplies uniform all-orders results.
"""
import json,math
from fractions import Fraction as F
import mpmath as mp
COUNTS={}
def need(ok,label):
 if not ok: raise RuntimeError(label)
 COUNTS[label]=COUNTS.get(label,0)+1

branches={
 'A+':(F(2,3),F(1),1,(F(4,3),F(4,3),F(-7,3),F(-1,3))),
 'A-':(F(2,3),F(1),-1,(F(4,3),F(-4),F(3),F(-1,3))),
 'B':(F(5,7),F(5,4),1,(F(25,14),F(25,14),F(-39,14),F(-11,14))),
}
def M(x): return mp.mpf(x.numerator)/x.denominator if isinstance(x,F) else mp.mpf(x)

def analytic(branch,r,r0):
 alpha,lam,eps,coeffs=branches[branch]
 alpha,lam=M(alpha),M(lam)
 p=alpha*(r+eps); L=lam*(r+eps); y=L-p-1
 ln2=mp.log(2)
 d=mp.exp(-p*ln2)+2*mp.exp(-(p+y)*ln2)
 a=mp.exp(-2*(p+y)*ln2)/(1+d)**2
 def g(z): return mp.log1p(-z/(2*(1+mp.sqrt(1-z))))
 phi=mp.log1p(d)+g(a)
 ellA=L*ln2+phi
 u=mp.exp(-2*p*ellA)
 b=16*u*u/(1-u)**4
 ellS=2*p*ellA-ln2+2*mp.log1p(-u)+g(b)
 v=mp.exp(-2*r*ellS)
 E=(2*p*(r-1)*phi+2*(r-1)*mp.log1p(-u)+r*g(b)-mp.log1p(-b)/2+mp.log1p(-v))/ln2
 gamma,b2,b1,b0=map(M,coeffs)
 h=r-r0
 Nprime=3*gamma*r0*r0+2*b2*r0+b1
 Nsecond=6*gamma*r0+2*b2
 D=Nprime+Nsecond*h/2+gamma*h*h
 return {'p':p,'L':L,'phi':phi,'d':d,'a':a,'u':u,'b':b,'v':v,'ellA':ellA,'ellS':ellS,'E':E,'D':D,'f':E/D}

# Exact polynomial margins at rational centers, independent of analytic samples.
for branch,(alpha,lam,eps,coeffs) in branches.items():
 gamma,b2,b1,b0=coeffs
 for r0 in [F(100)+F(k,8) for k in range(801)]+[F(1000),F(10**6)]:
  p0=alpha*(r0+eps); y0=(lam-alpha)*(r0+eps)-1
  need(p0>=66 and y0>=32 and alpha*(r0+eps+F(1,4))<r0,'exact affine disk envelopes')
  need(F(2,3)*(r0*r0-F(5,2)*r0+F(7,16))>=F(3,5)*r0*r0,'exact quadratic real-part margin')
  diff=F(1,4)*(3*r0*r0+4*r0+1)+F(1,16)*(3*r0+2)+F(1,64)
  need(diff<r0*r0,'exact cubic displacement margin')
  need(F(2,3)*r0*(r0-1)**2-r0*r0>=F(3,5)*r0**3,'exact cubic real-part margin')
  Nprime=3*gamma*r0*r0+2*b2*r0+b1; Nsecond=6*gamma*r0+2*b2
  need(Nprime>3*r0*r0 and 0<Nsecond<12*r0,'exact cubic derivatives')
  need(3*r0*r0-F(3,2)*r0-F(1,8)>2*r0*r0,'exact nonzero denominator margin')
  need((6*r0+3)<r0*r0,'exact subordinate E budget')
  need(2*r0*r0>=(4*p0) and r0*r0>=4*p0,'exact conjugate exponent comparisons')

# Sample the entire complex circumference and interior radii using specified logs.
disk_rows=[]
with mp.workdps(110):
 for branch,(alpha,lam,eps,_) in branches.items():
  for rfrac in [F(100),F(201,2),F(143),F(250)]:
   r0=M(rfrac);p0=M(alpha)*(r0+eps);q0=mp.power(2,-p0)
   maxf=mp.mpf(0); maxE=mp.mpf(0); minD=mp.inf
   for radius in [mp.mpf(0),mp.mpf('0.125'),mp.mpf('0.25')]:
    for j in range(24):
     r=r0+radius*mp.exp(2j*mp.pi*j/24)
     z=analytic(branch,r,r0)
     need(abs(z['d'])<2*q0 and abs(z['a'])<q0*q0,'sample primary complex scales')
     need(abs(z['phi'])<5*q0,'sample Phi bound')
     need(mp.re(z['p']*z['ellA'])>r0*r0*mp.log(2)/2,'sample main log real part')
     need(abs(z['u'])<q0**4 and abs(z['b'])<q0**4 and abs(z['v'])<q0**4,'sample conjugate scales')
     need(mp.re(r*z['ellS'])>r0**3*mp.log(2),'sample auxiliary log real part')
     need(abs(z['E'])<18*r0*r0*q0,'sample E bound')
     need(abs(z['D'])>2*r0*r0,'sample denominator separation')
     need(abs(z['f'])<16*q0,'sample f bound')
     maxf=max(maxf,abs(z['f'])/(16*q0));maxE=max(maxE,abs(z['E'])/(18*r0*r0*q0));minD=min(minD,abs(z['D'])/(2*r0*r0))
   disk_rows.append({'branch':branch,'r0':str(rfrac),'max_f_bound_ratio':mp.nstr(maxf,16),'max_E_bound_ratio':mp.nstr(maxE,16),'min_D_bound_ratio':mp.nstr(minD,16)})

# Lagrange coefficients from explicit derivatives, checked against direct roots.
inverse_rows=[]
for branch,(alpha,lam,eps,_) in branches.items():
 for rfrac in [F(100),F(201,2),F(143)]:
  pest=alpha*(rfrac+eps)
  dps=math.ceil(8*float(pest)*math.log10(2))+100
  with mp.workdps(dps):
   r0=M(rfrac);p0=M(alpha)*(r0+eps);q0=mp.power(2,-p0)
   epsilon0=16*q0;rho=1/(8*epsilon0)
   f=lambda r:analytic(branch,r,r0)['f']
   need(rho>1,'parameter disk includes one')
   terms=[]
   for n in range(1,6):
    term=(-1)**n*mp.diff(lambda r:f(r)**n,r0,n-1)/math.factorial(n)
    terms.append(term)
   # Fixed-point root is evaluated independently of the derivative expansion.
   h=mp.mpf(0)
   for _ in range(12): h=-f(r0+h)
   need(abs(h+f(r0+h))<mp.power(10,-dps+25),'direct small root residual')
   need(mp.im(h)==0 and h<0 and abs(h)<mp.mpf('0.25'),'real root and continuation endpoint')
   maxratio=mp.mpf(0)
   partial=mp.mpf(0)
   for K in range(6):
    if K:partial+=terms[K-1]
    bound=mp.mpf('0.25')*rho**(-K-1)/(1-1/rho)
    ratio=abs(h-partial)/bound
    need(ratio<1,'L9 explicit tail through order five')
    maxratio=max(maxratio,ratio)
   # On the large artificial-parameter circle, follow the same unique small root.
   for angle in [0,mp.pi/3,mp.pi,3*mp.pi/2]:
    t=rho*mp.exp(1j*angle)
    ht=mp.mpc(0)
    for _ in range(100):ht=-t*f(r0+ht)
    need(abs(ht)<mp.mpf('0.25'),'large parameter root stays in disk')
    need(abs(ht+t*f(r0+ht))<mp.mpf('1e-100'),'large parameter root residual')
    need(abs(1+t*mp.diff(f,r0+ht))>mp.mpf('0.9'),'sample root simplicity')
   inverse_rows.append({'branch':branch,'r0':str(rfrac),'decimal_precision':dps,'max_L9_error_to_bound':mp.nstr(maxratio,16),'first_coefficient':mp.nstr(terms[0],16),'fifth_coefficient':mp.nstr(terms[4],16)})

print(json.dumps({'status':'PASS','counts':dict(sorted(COUNTS.items())),'complex_disk_cases':disk_rows,'inverse_cases':inverse_rows,'mpmath_version':mp.__version__,'numerical_checks_are_interval_certified':False,'upstream_code_executed':False,'saved_schedule_executed':False,'integer_witness_tuple_materialized':False},indent=2,sort_keys=True))
