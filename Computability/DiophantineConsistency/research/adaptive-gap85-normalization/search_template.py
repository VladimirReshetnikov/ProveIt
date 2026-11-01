#!/usr/bin/env python3
"""Finite artificial-port scan of one very restricted gap-85 Pell template.

This does not search arbitrary 85 zeros, the actual fixed ports, or models.
"""
from math import isqrt

# A single illustrative hit when the necessary q^3 | Y condition is omitted.
x,y,eta,zeta,q,T=8,5,815,789,13,6
k=eta+zeta;a=y*(x+1);delta=a*a+4*a+3;c=eta+y*k
assert c==4*delta+3
ell=x*y*y*k
assert isqrt(1+ell*(ell+k))**2==1+ell*(ell+k)
assert isqrt(1+delta*c*c)**2==1+delta*c*c
R=c*T-4*delta
U=y*q*q; H=3+4*a; b0=x+a*c; E=x*y
root=isqrt(1+delta*c*c)
numerator=U*(root-b0)-H*(E*q-k+R+1)
assert R>0 and numerator>0 and numerator%(H*U)==0
assert y%q**3!=0
print('illustrative near-hit:',{'X':x,'Y':y,'eta':eta,'zeta':zeta,'q':q,'T':T,'R':R,'gamma':numerator//(H*U),'q_cubed_divides_Y':False})

# Search only c=4*delta+3; first-factor Pell indices generated from the
# fundamental solution and positive eta,zeta. The auxiliary template imposes
# R=c*T-4*delta. Test the positive main root and positive integral gamma.
examined=0; hits=[]
for q in range(2,7):
    for y in range(q**3,401,q**3):
        for x in range(1,401):
            if (x+y)%q: continue
            a=y*(x+1);delta=a*a+4*a+3;c=4*delta+3
            s=x*y*y;D=s*(s+1);k=2;first_root=2*s+1
            while y*k<c:
                eta=c-y*k;zeta=k-eta
                if eta>0 and zeta>0:
                    U=y*q*q;H=3+4*a;E=x*y;b0=x+a*c
                    main_root=4*(a+2)**3-3*(a+2)
                    for T in range(1,100):
                        R=c*T-4*delta
                        if R<=0: continue
                        examined+=1
                        numerator=U*(main_root-b0)-H*(E*q-k+R+1)
                        if numerator<=0: break
                        if numerator%(H*U)==0:
                            hits.append((q,x,y,eta,zeta,T,R,numerator//(H*U)))
                first_root,k=(2*s+1)*first_root+2*D*k,2*first_root+(2*s+1)*k
print('bounded scan:',{'q_range':'2..6','X_range':'1..400','Y_max':400,'T_range':'1..99','examined':examined,'hits':hits})
