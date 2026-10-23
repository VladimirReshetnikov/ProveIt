#!/usr/bin/env python3
"""Independently authored exact checks of the new polynomial quotient majorant."""
import sympy as s,json
from pathlib import Path
A,C,i,D,k=s.symbols('A C i D k')
L=C*D+1-A
F=1+k*k*D*D*(D-1)
G=A+F*L
N=2*G+L
N1=2*k*k*D*(D-1)*L+3*C
N2=2*k*k*(D-1)*L
N3=2*k*k*(L-C)
N4=2*k*k*C
T6=k*((1024*D**2-512*D-128)*N-64*N1-40*N2-28*N3-21*N4)
t6=1024*D**6-512*D**5-128*D**4-64*D**3-40*D**2-28*D-21
d5=33792*D**5+10560*D**4+4928*D**3+2464*D**2+1176*D+441
assert s.expand(t6*t6-1024**2*D**11*(D-1)-d5)==0
E=14*k**3*(A-1)/D-42*k**3*C/D+42*k**3*(A-1)/D**2+k*((120*C+192-64*A)/D+(84*C+120-40*A)/D**2+(63*C+84-28*A)/D**3+(63-21*A)/D**4)
assert s.expand(T6-k*t6*N/D**4-E)==0
t7=2048*D**7-1024*D**6-256*D**5-128*D**4-80*D**3-56*D**2-42*D-33
assert s.expand(t7*t7-2048**2*D**13*(D-1))==109824*D**6+36608*D**5+18304*D**4+9984*D**3+5460*D**2+2772*D+1089
E7=14*k**3*(A-1)/D-9*k**3*C/D+9*k**3*(A-1)/D**2-33*k**3*C/D**2+33*k**3*(A-1)/D**3+k*((120*C+192-64*A)/D+(84*C+120-40*A)/D**2+(63*C+84-28*A)/D**3+(63-21*A)/D**4)+s.Rational(99,2)*k*C/D**4+s.Rational(33,2)*k*(3-A)/D**5
assert s.expand(T6-k*t7*N/(2*D**5)-E7)==0
B8=8*D*D-4*D-1
assert s.expand(T6-k*(128*B8*N-8*k*k*(2*B8+2*D-1)*L+C*(14*k*k-192)))==0
J=4*A-5
assert s.expand(J**3-(A+1)*(64*A*A-304*A+604)+729)==0
assert s.expand(J**3-(A*A-1)*(64*A-240)-(364*A-365))==0
correction=i**3*(9*C*C*(64*A-239)-14*C*(64*A*A-304*A+603)+1024)+288*i+2048
T=s.expand((T6+correction).subs(k,i*J*C).subs(D,(A*A-1)*C*C+1))
F0=s.expand(F.subs(k,i*J*C).subs(D,(A*A-1)*C*C+1))
G0=s.expand(G.subs(k,i*J*C).subs(D,(A*A-1)*C*C+1))
delta=s.Poly(s.expand(T*T-2048**2*((A*A-1)*C*C+1)*F0*G0*G0),A,C,i)
rank=lambda abc:(7*abc[0]+3*abc[1],2*abc[0]+abc[2])
m=max(rank(es) for es,co in delta.terms())
leaders=[(es,int(co)) for es,co in delta.terms() if rank(es)==m]
print('degree pair',m,'leaders',leaders,'terms',len(delta.terms()))
assert m==(159,36)
assert leaders==[((15,18,6),9*2**18)]
assert all(all(e<=cap for e,cap in zip(es,(15,18,6))) for es,co in delta.terms())
# Use arithmetic fixtures, not floating point approximations.
fixtures=0
for aa in [729,730,1000,33280,10**5]:
 for cc in [1,2,5,100,10**5]:
  for ii in [1,2,7,100]:
   dd=(aa*aa-1)*cc*cc+1;kk=ii*(4*aa-5)*cc;ll=cc*dd+1-aa
   ff=1+kk*kk*dd*dd*(dd-1);gg=aa+ff*ll;nn=2*gg+ll
   nn1=2*kk*kk*dd*(dd-1)*ll+3*cc;nn2=2*kk*kk*(dd-1)*ll;nn3=2*kk*kk*(ll-cc);nn4=2*kk*kk*cc
   tt=kk*((1024*dd*dd-512*dd-128)*nn-64*nn1-40*nn2-28*nn3-21*nn4)+ii**3*(9*cc*cc*(64*aa-239)-14*cc*(64*aa*aa-304*aa+603)+1024)+288*ii+2048
   assert tt>0 and tt*tt>2048**2*dd*ff*gg*gg
   fixtures+=1
out={'status':'PASS','radical_scale':2048,'majorant':'T6+i^3[9 C^2(64 A-239)-14 C(64 A^2-304 A+603)+1024]+288 i+2048','degree_T_square_defect':{'t':159,'constant':36},'leading_A_C_i_powers':[15,18,6],'leading_coefficient':9*2**18,'expanded_defect_terms':len(delta.terms()),'componentwise_degree_bound':[15,18,6],'integer_fixtures':fixtures,'identity_checks':7}
Path(__file__).with_name('REFINED_MAJORANT_CHECKS.json').write_text(json.dumps(out,indent=2)+'\n')
# Independently inspectable finite polynomial certificate.
Path(__file__).with_name('REFINED_DEFECT_POLYNOMIAL.json').write_text(json.dumps({'variables':['A','C','i'],'terms':[{'powers':list(es),'coefficient':int(co)} for es,co in delta.terms()]},separators=(',',':'))+'\n')
print(out)
