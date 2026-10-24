#!/usr/bin/env python3
"""Independent exact checks for the positive saturated ProductPell theorem."""
from math import gcd, isqrt
from pathlib import Path
import hashlib
import json


def need(value, label):
    if not value:
        raise RuntimeError(label)


def pell(a, n):
    """Return chi_a(n), psi_a(n) by binary multiplication of Pell units."""
    x, y = 1, 0
    u, v = a, 1
    delta = a*a-1
    while n:
        if n & 1:
            x, y = x*u + delta*y*v, x*v + y*u
        u, v = u*u + delta*v*v, 2*u*v
        n //= 2
    return x, y


def run():
    count = 0
    for a in range(2, 10):
        for c in range(1, 20):
            for J in range(1, 5):
                for i in range(1, 4):
                    for j in range(1, 4):
                        B = 3
                        delta = a*a-1
                        D = delta*c*c+1
                        S = i*J*c*c
                        F = delta*D*S*S+1
                        G = a+F*(c*D+1-a)
                        H = c+F*(B+(j-1)*c)
                        I = (G*G-1)*H*H+1
                        T = a*D*S
                        need(F % D == 1, 'F modulo D')
                        need((F-1) % c == 0, 'F modulo C')
                        need((F-1) % J == 0, 'F modulo J')
                        need((G-1) % D == 0, 'G modulo D')
                        need((G-1) % c == 0, 'G modulo C')
                        need((H-B) % c == 0, 'H modulo C')
                        need((H-c) % F == 0, 'H modulo F')
                        need((I-D) % F == 0, 'I modulo F')
                        need((I-1) % D == 0, 'I modulo D')
                        need(gcd(D,F)==gcd(D,I)==gcd(F,I)==1, 'coprime')
                        need(T*T-D*F == D*(D*S*S-1)>0, 'first majorant')
                        V=T*G*H
                        need(V*V-D*F*I == (T*T-D*F)*G*G*H*H+D*F*(H*H-1)>0,
                             'whole majorant')
                        count += 1
    fixtures = []
    for a, B, J, n in [(2,3,1,1170), (2,3,3,3510), (3,3,1,20790)]:
        d,c=pell(a,B)
        D=d*d
        f,Eold=pell(a,n)
        modulus=J*D*c*c
        need(Eold % modulus==0, 'old Pell divisibility')
        iold=Eold//modulus
        i=d*iold
        F=(a*a-1)*D*(i*J*c*c)**2+1
        Fold=(a*a-1)*(iold*J*D*c*c)**2+1
        need(F==Fold==f*f, 'saturation preservation')
        G=a+F*(c*D+1-a)
        h,H=pell(G,B)
        need((H-c) % F==0, 'absorbed H first quotient')
        q=(H-c)//F
        need((q-B)%c==0 and q>=B, 'absorbed H positive quotient')
        j=1+(q-B)//c
        need(H==c+F*(B+(j-1)*c), 'absorbed H identity')
        I=(G*G-1)*H*H+1
        need(I==h*h, 'I square')
        root=d*f*h
        need(D*F*I==root*root, 'complete product square')
        Fbad=(a*a-1)*(i*J*c*c)**2+1
        need(Fbad!=Fold, 'remove-all-D negative control')
        fixtures.append(dict(A=a,B=B,J=J,index=n,C=c,
            old_i_bits=iold.bit_length(),new_i_bits=i.bit_length(),
            j_bits=j.bit_length(),root_bits=root.bit_length(),
            product_bits=(D*F*I).bit_length()))
    result=dict(status='PASS',unconditional_cases=count,complete_fixtures=fixtures,
        negative_controls=3,
        statement='Finite exact checks supplement the ordinary theorem; no ZFC refutation was constructed.',
        script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    (Path(__file__).parent/'SATURATION_CHECKS.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    run()
