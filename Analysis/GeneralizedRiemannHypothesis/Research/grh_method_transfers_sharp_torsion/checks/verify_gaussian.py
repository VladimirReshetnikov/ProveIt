"""Independently enumerate primes in the Gaussian conductor layers."""
from math import isqrt

def primes_to(limit):
    sieve=bytearray([1])*(limit+1)
    sieve[:2]=bytes(2)
    for i in range(2,isqrt(limit)+1):
        if sieve[i]:
            sieve[i*i::i]=bytes((limit-i*i)//i+1)
    return {i for i,v in enumerate(sieve) if v}

def represented(limit,primes,level):
    scale=2**(level-1)
    sums=set()
    for y in range(-isqrt(limit)//scale-1,isqrt(limit)//scale+2):
        for x in range(-isqrt(limit),isqrt(limit)+1):
            value=(2*x+y)**2+(scale*y)**2
            if value in primes and value!=2:
                sums.add(value)
    return sums

def principal(limit,primes,level):
    scale=2**level
    return {a*a+(scale*b)**2 for b in range(1,isqrt(limit)//scale+1)
            for a in range(1,isqrt(limit-(scale*b)**2)+1,2)
            if a*a+(scale*b)**2 in primes}

if __name__=='__main__':
    limit=100000
    primes=primes_to(limit)
    for level in range(2,8):
        actual=represented(limit,primes,level)
        assert actual==principal(limit,primes,level-1)-principal(limit,primes,level)
        print(f'n={level}: {len(actual)} primes up to {limit}, first five {sorted(actual)[:5]}')
