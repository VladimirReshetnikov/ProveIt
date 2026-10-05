"""Exact scalar facts for the entire connected two-pulse contour estimate."""
from fractions import Fraction as F
from pathlib import Path
import contextlib,io,json
with contextlib.redirect_stdout(io.StringIO()):import half_scalar as v
from model_intervals import trig_rad
v.K=64
rmin,rmax=F(59,100),F(82,100)
tmin,tmax=F(68214,10**5),F(68621,10**5)
# |tan z|>=tanh|z| follows from |arctan a|<=atanh|a| when |a|<1.
z=rmin
s=sum((z**(2*j+1)/F(2*j+1)for j in range(32)),F(0))
s+=z**65/(65*(1-z*z))
v.need(s<tmin,'lower annulus bound')
a_min=trig_rad(tmin,True)/trig_rad(tmin,False)
a_max=trig_rad(tmax,True)/trig_rad(tmax,False)
v.strict_more(a_min,F(81,100),'real saddle field exceeds .81')
v.strict_less(a_max,rmax,'circle field below .82')
# The largest signed-factor threshold at L>=4 is tan(pi/32).
t4=v.sinp(F(1,32))/v.cosp(F(1,32))
v.strict_less(t4,F(1,10),'signed-factor threshold')
bmax=v.sinp(F(17,64))/v.cosp(F(17,64))
v.strict_less(bmax,F(6,5),'second positive tangent factor')
v.need(rmax*F(6,5)<1,'positive angular terms below one')
neg=rmin*F(1,10)/(rmin-F(1,10))**2
pos=2*rmin/(1+rmin)**2
v.need(neg<F(1,4),'negative angular term')
v.need(pos-F(1,4)>F(1,5),'angular derivative margin')
# Shallow signed products are dominated coefficientwise after replacing
# the sole negative cosine, at spatial index j=1, by its absolute value.
def Habs(r,x):
 p=v.iv(1)
 for j in range(1,v.K+1):
  c=v.cosp(x/F(2**j));s=v.sinp(x/F(2**j))
  p=p*((-c if j==1 else c)+r*s)
 tail=r*v.PI*v.iv(x/F(2**v.K))
 v.need(tail.hi<v.S,'absolute product tail')
 v.need((v.PI*v.iv(x/F(2**(v.K+1)))).hi<v.iv(r/2).lo,'positive omitted absolute factors')
 return v.I(p.lo,(p/(1-tail)).hi)
v.r=F(81,100)
glower=v.H(F(1))
rows=[]
for L in [1,2,3]:
 p=v.iv(rmax)
 for j in range(2,L+1):p=p*(v.cosp(F(1,2**j))+rmax*v.sinp(F(1,2**j)))
 upper=p*Habs(rmax,1+F(1,2**L))
 ratio=upper/glower.square()
 v.strict_less(ratio,F(199,200),'shallow depth '+str(L))
 rows.append({'depth':L,'squared_modulus_not_used':True,'absolute_product_ratio_interval':v.out(ratio)})
out={'all_checks_exact':True,'all_checks_passed':True,'field_annulus':['.59','.82'],'real_field_lower':'.81','angular_derivative_margin':'1/5','shallow_cap':'199/200','shallow_rows':rows,'negative_angular_upper':str(neg),'positive_angular_lower':str(pos),'scope':'This checker certifies the entire two-pulse template; the pressure comparison is proved separately in the article'}
Path(__file__).with_name('two_pulse_certificate.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
