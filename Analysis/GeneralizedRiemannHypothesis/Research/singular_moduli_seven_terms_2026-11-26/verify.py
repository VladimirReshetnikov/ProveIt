"""Replay the disk certificate by binomial expansion and modular Horner."""
import json
from math import comb
from pathlib import Path

def valuation(x, p):
    if not x: return float("inf")
    v = 0
    while x % p == 0:
        x //= p
        v += 1
    return v

def horner(c, A, B, modulus):
    # Compose c(X) with A+B*Y over Z/modulus.
    acc = [0]
    for t in reversed(c):
        nxt = [(A*acc[0]+t)%modulus]
        nxt += [(A*acc[j]+B*acc[j-1])%modulus for j in range(1,len(acc))]
        nxt.append(B*acc[-1]%modulus)
        acc = nxt
    return acc[:7]

rows = json.loads(Path(__file__).with_name("certificates.json").read_text())
assert len(rows) == 10
assert len({r["discriminant"] for r in rows}) == 10
for r in rows:
    d,p,a,u,k = (r[key] for key in ("discriminant","p","a","u","k"))
    c = r["coefficients"]
    assert len(c) == 7 and c[-1] == 1 and c[0] and u%p
    assert (p,k) in {(2,2),(3,2),(17,1)}
    A, B = p**a*u, p**a
    vals = [sum(c[j]*comb(j,i)*A**(j-i)*B**i for j in range(i,7))
            for i in range(7)]
    divs = [p**(6*a+k*(6-i)) for i in range(7)]
    assert vals[-1] == p**(6*a)
    assert all(x%m == 0 for x,m in zip(vals,divs))
    res = horner(c,A,B,divs[0])
    assert all((x-y)%divs[0] == 0 for x,y in zip(vals,res))
    print(d,p,a,u,k,",".join(str(valuation(x,p)) for x in vals))
print("PASS: all 10 shifted polynomials give integral roots on the stated disk.")
