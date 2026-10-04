#!/usr/bin/env python3
"""Independent bounded arithmetic and static data audit. Executes no saved rows."""
import hashlib
import json
from math import gcd, isqrt
from pathlib import Path

ROOT = Path(__file__).resolve().parent

def require(value, message):
    if not value:
        raise ValueError(message)

def pell(A, n, modulus=None):
    D = A*A-1
    x, y, u, v = 1, 0, A, 1
    while n:
        if n & 1:
            x, y = x*u+D*y*v, x*v+y*u
            if modulus:
                x %= modulus
                y %= modulus
        n //= 2
        if n:
            u, v = u*u+D*v*v, 2*u*v
            if modulus:
                u %= modulus
                v %= modulus
    return x, y

def prime(n):
    return n > 1 and all(n%d for d in range(2,isqrt(n)+1))

def main():
    pins=json.loads((ROOT/'SOURCE_PINS.json').read_text())
    for row in pins['files']:
        raw=(ROOT/row['local']).read_bytes()
        require(hashlib.sha256(raw).hexdigest()==row['sha256'], 'SHA256')
        require(hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==row['blob_sha'], 'blob')
    packet=json.loads((ROOT/'source/complete83_free_coefficient_scout.json').read_text())['packet']
    rows=packet['source']
    names=[row[0] for row in rows]
    require(len(names)==len(set(names))==83,'row names')
    known=set(packet['free'])
    for out, op, a, b in rows:
        require(op in ('+','-','*'),'opcode')
        require(all(type(t) is int or t in known for t in (a,b)),'topology')
        require(out not in known,'SSA')
        known.add(out)
    live={packet['output']}
    for out, op, a, b in reversed(rows):
        if out in live:
            live.update(t for t in (a,b) if type(t) is str)
    require(set(names+packet['free'])<=live,'liveness')
    require(sum(r[1]=='*' for r in rows)==46,'multiplication count')
    require(len(packet['witnesses'])==18,'positive supplied count')
    require(packet['witness_domain']=='strictly positive integers','domain')
    gamma_cases=0
    for A in range(2,31):
        H=4*A-5
        old, current=0,0
        for n in range(0,16):
            x,y=pell(A,n)
            gamma=(x-(A-2)*y-2**n)//H
            require(x-(A-2)*y==2**n+H*gamma,'gamma exact')
            if n>=2:
                require(gamma>current,'gamma strict growth')
                require(gamma==2*A*current-old+2**(n-2),'gamma recurrence')
            old,current=current,gamma
            if n>=3 and n%2:
                D=A*A-1
                require((y-n)%D==0 and (y-n)//D>0,'input delta')
            gamma_cases+=1
    crt_cases=[]
    for A in (2,4,6,8,10):
        D=A*A-1
        ps=[p for p in range(D+1,D+121) if p%4==1 and prime(p)][:3]
        require(len(ps)==3,'test primes')
        for p in ps:
            mainx,c=pell(A,p)
            require(c%p==pow(D,(p-1)//2,p),'Frobenius')
            require(gcd(c,8*p)==1,'CRT coprimality')
            f,b=pell(A,2*p)
            S=D*b
            require(D*f*f-S*S==D,'strong norm')
            require(f*f%c==1 and gcd(c,f)==1,'c,f')
            for R in (1,3,p-2):
                ell=3*p+8*p*((R-3*p)*pow(8*p,-1,c)%c)
                require(ell>0 and ell%c==R%c and ell%(8*p)==3*p,'CRT')
                require(ell%4==3,'sign')
                cf=c*f
                chi,y=pell(S,ell,S*cf)
                require(chi%S==0,'quotient representative')
                V=chi//S
                require((V+R)%c==0 and (V+c)%f==0,'both quotient residues')
                require((V+c+R*f*f)%cf==0,'T divisibility')
                require((S*S*V*V-(S*S-1)*y*y-1)%cf==0,'aux norm modulo cf')
                crt_cases.append({'A':A,'p':p,'R':R,'c_bits':c.bit_length(),'ell_bits':ell.bit_length()})
    result={'status':'PASS','pins':len(pins['files']),'static_source_rows':83,'live_free_ports':len(packet['free']),'M':46,'A':37,'positive_witnesses':18,'gamma_cases':gamma_cases,'crt_cases':crt_cases,'scope':'Finite corroboration only. No saved source rows, upstream Python, or schedules executed. No valid compiler full zero materialized. No prime-density theorem inferred from tests.'}
    print(json.dumps(result,indent=2))

if __name__=='__main__':
    main()
