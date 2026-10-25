#!/usr/bin/env python3
"""Reconstruct the whole incoming complemented-label radix47 tuple from its full recipe.

The literal 436-character code and finite tile formulas are the unchanged
ProveIt indexed-tile specification. No simulation or search is performed.
"""
from __future__ import annotations
import argparse
import gzip
import hashlib
import json
import math
from pathlib import Path

ROOT = Path(__file__).resolve().parent
ALPHABET = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"
CODE = (
    "BxEnhvy6NipzkWmROo0GsA3uK3twWLxscLq20UTumy5Cdu461LwD6g7RDNzF8Y"
    "iYDFTpB8ehAypd7d6OsOL4APamnJeNXQypUezCmW9n4oXP6XfgmiWuAWZ8ZJ7U"
    "OP7gu4kVdlGZqZHULQMar1dXNeJW4i7oNVI8usp8BlovjjZbwPCovZI328fRUq"
    "4q92R81s5GjWQaQfGhkq9UYMK3rRMaBmsOIBkJqc2cj2VRIZ6mjzkBIOkW9SjZ"
    "FzeA6J5u4j3sBL3SdgwXzM9mHvQivu8EJ1TBTpRhHDqZIbmYgwQ8VqTAFotl6F"
    "We1YC554GKrVHsA8oUGKSA6F6k5KREBSD0Tgd7bFALY84LLbpw574BQyvdoHrl"
    "0Oe35uwDf15DpT6VJWZBjSbHPpPAINYTte0eUxnTFTKBlGj8Am6sb1gLldh8WZ"
    "8P"
)


def reconstruct():
    if len(CODE) != 436:
        raise ValueError("Wrong code length")
    number = 0
    for symbol in CODE:
        number = number * 62 + ALPHABET.index(symbol)
    N = number % (1 << 636)
    T0 = (number >> 636) % (1 << 1675)
    E0 = number >> 2311
    actions = []
    sig = tau = 0
    for q in range(215):
        m = (N >> (430 + q)) & 1
        Fq = 14 * (1 - m) + m * ((E0 >> (4 * tau)) & 15)
        tau += m
        for b in (0, 1):
            j = 2*q + b
            nu = (N >> j) & 1
            target = nu * (1 + sig) + (1 - nu) * ((T0 // pow(216, j-sig)) % 216)
            actions.append((target, (Fq >> (2*b)) & 1, (Fq >> (2*b+1)) & 1))
            sig += nu
    right = sorted({u for u, v, d in actions if d == 1})
    left = sorted({u for u, v, d in actions if d == 0})
    rt = {q: 6+j for j, q in enumerate(right)}
    lt = {q: 205+j for j, q in enumerate(left)}
    tiles = {}
    def put(index, tile):
        if index in tiles:
            raise ValueError("Duplicate tile index")
        tiles[index] = tile
    def h(q, b):
        return 2*(q+1)+b
    put(0, (2,435,3,1)); put(1, (5,0,0,0))
    for j, (u,v,d) in enumerate(actions):
        q,b = divmod(j,2)
        put(j+2, (lt[u] if d == 0 else 0, h(q,b), rt[u] if d == 1 else 0, v))
    for b in (0,1):
        put(432+b,(0,h(215,b),0,h(215,b)))
        put(434+b,(0,b,0,b))
    for q in right:
        for b in (0,1): put(424+2*rt[q]+b,(rt[q],b,0,h(q,b)))
    for q in left:
        for b in (0,1): put(424+2*lt[q]+b,(0,b,lt[q],h(q,b)))
    for j in range(4): put(924+j,(0,j+430*(j//2),0,438))
    put(928,(2,434,2,0)); put(929,(3,436,4,4)); put(930,(4,436,4,0))
    for t in (434,435,436): put(497+t,(1,438,1,t))
    for a in (0,1,4):
        for b in (0,1,2): put(934+3*a+b-6*(a//4),(a,437,b,437))
    if set(tiles) != set(range(943)):
        raise ValueError("Incomplete indexed tile enumeration")
    def rho(e):
        if e < 0: raise ValueError("Negative rho exponent")
        return 1 << (47*e)
    coefficients=[0]*3297
    for index in range(943):
        w,n,e,s = tiles[index]
        u=w+(n<<8)+(e<<17)+(s<<25)
        coefficients[index]=1+1024*(u+1)
    for b,e,m in [(10,1023,8),(18,1013,9),(27,1003,8),(35,983,9)]:
        for j in range(m):coefficients[e+j]=1<<(b+j)
    for e in [992,1011,1022,1031,1095,2195,3296]:coefficients[e]=1<<44
    expected=json.loads((ROOT/"provenance/radix47/radix47/phi_coefficients.json").read_text())
    if coefficients!=expected:raise ValueError("Not the whole 3297-coefficient complemented tuple")
    beta=rho(8807)-1;B=beta+1;base=1<<47
    es=set(range(943)) | set(range(983,993)) | set(range(1003,1012)) | set(range(1013,1032)) | {1063,1064,1095,2195,3296}
    MC=beta-sum(rho(e) for e in es if e!=1)-2*rho(1063)
    core=sum(rho(e) for e in range(1013,1023))+sum(rho(e) for e in range(1065,1074))+rho(2195)+rho(3296)
    padding=(base-1)*sum(rho(e) for e in range(8792,8807))
    padding+=(base-1)*sum(rho(e) for e in range(7691,7694))+((1<<28)-4)*rho(7694)
    native=4+(base-2)*(rho(4393)+rho(5495))+core+padding
    MF=beta+native
    K=sum(rho(e) for e in (30,62,1100,2201,8849))
    K+=sum(c*(rho(4393-e)+rho(5495-e)) for e,c in enumerate(coefficients))
    if not (beta>=31 and beta%2==1 and K>0 and 0<MC<beta<MF<2*beta):
        raise ValueError("Actual fixed tuple fails its arithmetic scalar interface")
    if not (MC%4==2 and native%8==4 and MC.bit_count()==47*8807-986 and native.bit_count()==986):
        raise ValueError("Wrong full native mask population/phase")
    if not (len(es)==986 and sum(coefficients)==3953059820717999 and max(coefficients)==1<<44 and max(coefficients[:943])==15049678914561):
        raise ValueError("Wrong complete coefficient support/carry premises")
    Csum=sum(coefficients);M=max(coefficients)
    if not (Csum+5+2*M+3*base//4+29<30*base and 943+29<1024 and 88*M+(base-1024)+2*M+5+3*base//4+29<13*base and 7*M-1024+12<base):
        raise ValueError("Incoming native carry/bootstrap bounds fail")
    # Independently collect all retained native linear target identities.
    kernel={30:1,62:1,1100:1,2201:1}
    for e,c in enumerate(coefficients):
        if c:
            for v in (4393-e,5495-e):
                if v in kernel:raise ValueError("Non-distinct reflected kernel residue")
                kernel[v]=c
    geometry=json.loads((ROOT/"provenance/radix47/radix47/native_geometry.json").read_text())
    if len(geometry['claims'])!=51:raise ValueError("Missing native target identity")
    for claim in geometry['claims']:
        got=[[e,kernel[claim['target']-e]] for e in sorted(es) if claim['target']-e in kernel]
        if got!=claim['terms']:raise ValueError("Full native target differs: "+str(claim['target']))
    if any(e-f==1102 for e in es for f in es):raise ValueError("Clause supports intersect")
    if [(e,f) for e in sorted(es) for f in sorted(es) if e-f==1101]!=[(3296,2195)]:
        raise ValueError("Wrong unique phase-anchor gap")
    # Complete actual-integer controller associations, not values from another radix.
    def prime(n):return n>=2 and all(n%j for j in range(2,math.isqrt(n)+1))
    def factors(n):
        out=[];d=2
        while d*d<=n:
            if n%d==0:
                out.append(d)
                while n%d==0:n//=d
            d+=1
        if n>1:out.append(n)
        return out
    for modulus,order,expected_b,expected_k,expected_h in [(47,23,12,5,17),(8807,4403,2677,4079,5042),(1012691,1012690,959313,1005855,834350)]:
        if not prime(modulus):raise ValueError("Controller modulus not prime")
        if (B%modulus,K%modulus,(1+B*K+B*B)%modulus)!=(expected_b,expected_k,expected_h):
            raise ValueError("Wrong actual whole-tuple controller association")
        if math.gcd((B*B-1)*(1+B*K+B*B),modulus)!=1:raise ValueError("Controller unit premise fails")
        if pow(B,order,modulus)!=1 or any(pow(B,order//p,modulus)==1 for p in factors(order)):
            raise ValueError("Wrong exact controller order")
    if pow(B,1012690,1012691**2)!=285921151559:raise ValueError("Wrong valuation-one controller lift")
    return {"beta":beta,"K0":K,"MC":MC,"MF":MF}


def check_or_write(write=False):
    binding = json.loads((ROOT/"q1_bv.json").read_text())["coefficient_binding"]["ports"]
    native_binding=json.loads((ROOT/"provenance/radix47/radix47/polynomial.json").read_text())["coefficient_binding"]["ports"]
    for port,meta in binding.items():
        for key in ("raw_sha256","gzip_sha256","bits"):
            if meta[key]!=native_binding[port][key]:raise ValueError("Not incoming P66 whole-tuple binding")
    receipt = []
    for name,value in reconstruct().items():
        meta = binding[name]
        raw = value.to_bytes((value.bit_length()+7)//8,"little")
        digest = hashlib.sha256(raw).hexdigest()
        if digest != meta["raw_sha256"] or value.bit_length() != meta["bits"]:
            raise ValueError(f"Reconstructed value differs from parent binding: {name}")
        path = ROOT/"coefficients"/meta["file"]
        if write:
            path.parent.mkdir(parents=True,exist_ok=True)
            path.write_bytes(gzip.compress(raw,compresslevel=9,mtime=0))
        if gzip.decompress(path.read_bytes()) != raw:
            raise ValueError(f"Payload differs: {name}")
        receipt.append({"port":name,"bits":value.bit_length(),"raw_sha256":digest,"gzip_sha256":hashlib.sha256(path.read_bytes()).hexdigest()})
    if sum((v["bits"]+7)//8 for v in receipt)!=207214 or max(v["bits"] for v in receipt)!=415904:
        raise ValueError("Wrong whole-tuple storage profile")
    return receipt


if __name__ == "__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write",action="store_true")
    args=parser.parse_args()
    print(json.dumps(check_or_write(args.write),indent=2))
