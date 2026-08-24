def sieve(n):
    s=bytearray([1])*n; s[0]=s[1]=0
    for i in range(2,int(n**0.5)+1):
        if s[i]: s[i*i::i]=bytearray(len(s[i*i::i]))
    return [i for i in range(n) if s[i]]
P=[p for p in sieve(10**5) if p>=5]
w2=[p for p in P if pow(2,p-1,p*p)==1]
w3=[p for p in P if pow(3,p-1,p*p)==1]
both=[p for p in P if pow(2,p-1,p*p)==1 and pow(3,p-1,p*p)==1]
print("base2:",w2); print("base3:",w3); print("both:",both)
print("num primes 5<=p<1e5:",len(P))
