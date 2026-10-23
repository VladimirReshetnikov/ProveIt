#!/usr/bin/env python3
"""Exact finite checks of polynomial majorant identities, not a semantic proof."""
from collections import defaultdict
from pathlib import Path
import json
HERE=Path(__file__).resolve().parent

def req(p,msg):
    if not p:raise RuntimeError(msg)

def values(A,C,i):
    J=4*A-5;D=(A*A-1)*C*C+1;e=i*J*C;L=C*D+1-A
    E=C*D*e;F=(A*A-1)*E*E+1;G=A+F*L
    N=2*G+L
    N1=2*e*e*D*(D-1)*L+3*C
    N2=2*e*e*(D-1)*L
    N3=2*e*e*(L-C)
    N4=2*e*e*C
    cor=256*i*(e*e+2)+2048
    T=e*((1024*D*D-512*D-128)*N-64*N1-40*N2-28*N3-21*N4)+cor
    r1=3-A;r2=3*C*D+3-A;r3=2*e*e*(A-1)*D*D+r2
    r4=2*e*e*(1-A-C)*D**3+2*e*e*(A-1)*D*D+r2
    tn=1024*D**6-512*D**5-128*D**4-64*D**3-40*D*D-28*D-21
    dn=33792*D**5+10560*D**4+4928*D**3+2464*D*D+1176*D+441
    Rnum=e*(64*r1*D**3+40*r2*D*D+28*r3*D+21*r4)+cor*D**4
    X=e*e*D**3*(D-1)
    req(D*F==X+D,'DF identity')
    for k,Nk,rk in [(1,N1,r1),(2,N2,r2),(3,N3,r3),(4,N4,r4)]:
        req(N==D**k*Nk+rk,'quotient remainder')
    req(tn*tn-1024**2*D**11*(D-1)==dn,'square approximation')
    req(T>0 and T*T>2048**2*D*F*G*G,'strict majorant')
    req(D**4*T==e*tn*N+Rnum,'remainder numerator')
    lhs=D**8*(T*T-2048**2*D*F*G*G)
    rhs=e*e*dn*N*N+1024**2*D**8*(X*L*L-4*D*G*(C*D+1))+2*e*tn*N*Rnum+Rnum*Rnum
    req(lhs==rhs,'division-free cancellation certificate')
    for H,P,R in [(1,1,1),(3,17,7),(100,100000,99999)]:
        I=(G*G-1)*H*H+1;B=2*P*(P+R)+1;V=T*H+B
        req((V-B)>0 and (V-B)**2>2048**2*D*F*I,'explicit gap')
        lhs2=D**8*(V*V-2048**2*D*F*I)
        rhs2=H*H*lhs+2048**2*D*F*D**8*(H*H-1)+D**8*(2*T*H*B+B*B)
        req(lhs2==rhs2,'V certificate')

count=0
for A in list(range(3,51))+[33280,10**6]:
    for C in range(1,7):
        for i in range(1,5):
            values(A,C,i);count+=1
# Independently reconstruct the universal tnum square identity by sparse products.
p={6:1024,5:-512,4:-128,3:-64,2:-40,1:-28,0:-21}
r=defaultdict(int)
for a,x in p.items():
    for b,y in p.items():r[a+b]+=x*y
r[12]-=1024**2;r[11]+=1024**2
r={k:v for k,v in r.items() if v}
req(r=={5:33792,4:10560,3:4928,2:2464,1:1176,0:441},'universal sparse identity')
result={'strict_majorant_and_certificate_fixtures':count,'gap_fixtures':3*count,
        'universal_sparse_identity':r,'status':'PASS',
        'padding':'2*P*(P+R)+1',
        'primary_degree':'820*t+12*W+208',
        'primary_diagonal_leading_coefficient':'3*2^1494',
        'certificate_relation':'certificate=D^16*primary',
        'certificate_degree':'1140*t+12*W+272',
        'certificate_diagonal_leading_coefficient':'3*2^2038',
        'scope':'Exact finite majorant checks and the universal tn-square identity. Full symbolic identities and degree certificates are independently checked by verify_refined.py; the proof is in HIGHER_MAJORANT.md.'}
(HERE/'HIGHER_MAJORANT_AUDIT.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
