#!/usr/bin/env python3
"""Reconstruct all four indexed BFS943 fixed numerals from the printed recipe.

The literal 436-character code and finite tile formulas are the unchanged
ProveIt indexed-tile specification. No simulation or search is performed.
"""
from __future__ import annotations
import argparse
import gzip
import hashlib
import json
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
        return 1 << (67*e)
    beta = rho(8807)-1
    es = set(range(943)) | set(range(983,993)) | set(range(1003,1012)) | set(range(1013,1032)) | {1063,1064,1095,2195,3296}
    MC = beta - sum(rho(e) for e in es if e != 1) - 2*rho(1063)
    MF = beta + 4 + ((1 << 51)-2)*(rho(4393)+rho(5495))
    MF += sum(rho(e) for e in range(1013,1023)) + sum(rho(e) for e in range(1065,1074)) + rho(2195)+rho(3296)
    MF += ((1 << 65)-1)*sum(rho(e) for e in range(8792,8805)) + ((1 << 19)-1)*rho(8805)
    K = sum(rho(e) for e in (30,62,1100,2201,8849))
    for index in range(943):
        w,n,e,s = tiles[index]
        val = w + (n << 8) + (e << 17) + (s << 25) + (127 << 34)
        coefficient = 1 + (1 << 51) - (val << 10)
        K += coefficient*(rho(4393-index)+rho(5495-index))
    for b,e,m in [(10,1023,8),(18,1013,9),(27,1003,8),(35,983,9),(44,1031,1),(45,1022,1),(46,1011,1),(47,992,1),(48,1095,1),(49,2195,1),(50,3296,1)]:
        for j in range(m):
            K += (1 << (b+j))*(rho(4393-e-j)+rho(5495-e-j))
    if not (beta>=31 and beta%2==1 and K>0 and 0<MC<beta<MF<2*beta):
        raise ValueError("Actual fixed tuple fails its arithmetic scalar interface")
    return {"beta":beta,"K0":K,"MC":MC,"MF":MF}


def check_or_write(write=False):
    binding = json.loads((ROOT/"q1_bv.json").read_text())["coefficient_binding"]["ports"]
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
    return receipt


if __name__ == "__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write",action="store_true")
    args=parser.parse_args()
    print(json.dumps(check_or_write(args.write),indent=2))
