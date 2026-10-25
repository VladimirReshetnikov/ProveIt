"""Reconstruct the complete indexed BFS943 tuple printed by package 133.

No parameters remain after this finite integer computation.  The formulas
are transcribed from the pinned parent_printed_equation.tex, not inferred
from the numerical hashes.
"""
from pathlib import Path
import hashlib
import json

ALPHABET = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"
ENCODED = (
    "BxEnhvy6NipzkWmROo0GsA3uK3twWLxscLq20UTumy5Cdu461LwD6g7RDNzF8Y"
    "iYDFTpB8ehAypd7d6OsOL4APamnJeNXQypUezCmW9n4oXP6XfgmiWuAWZ8ZJ7U"
    "OP7gu4kVdlGZqZHULQMar1dXNeJW4i7oNVI8usp8BlovjjZbwPCovZI328fRUq"
    "4q92R81s5GjWQaQfGhkq9UYMK3rRMaBmsOIBkJqc2cj2VRIZ6mjzkBIOkW9SjZ"
    "FzeA6J5u4j3sBL3SdgwXzM9mHvQivu8EJ1TBTpRhHDqZIbmYgwQ8VqTAFotl6F"
    "We1YC554GKrVHsA8oUGKSA6F6k5KREBSD0Tgd7bFALY84LLbpw574BQyvdoHrl"
    "0Oe35uwDf15DpT6VJWZBjSbHPpPAINYTte0eUxnTFTKBlGj8Am6sb1gLldh8WZ"
    "8P"
)

def construct():
    if len(ENCODED) != 436:
        raise ValueError("incorrect action numeral length")
    number = 0
    for c in ENCODED:
        number = 62 * number + ALPHABET.index(c)
    N = number % (1 << 636)
    T0 = (number >> 636) % (1 << 1675)
    E0 = number >> 2311
    nu = [(N >> j) & 1 for j in range(430)]
    m = [(N >> (430+q)) & 1 for q in range(215)]
    actions = []
    for q in range(215):
        fq = 14 * (1-m[q]) + m[q] * ((E0 >> (4 * sum(m[:q]))) & 15)
        for b in range(2):
            j = 2*q+b
            sigma = sum(nu[:j])
            u = nu[j] * (1+sigma) + (1-nu[j]) * ((T0 // (216 ** (j-sigma))) % 216)
            v = (fq >> (2*b)) & 1
            d = (fq >> (2*b+1)) & 1
            actions.append((u,v,d))
    right = {u for u,v,d in actions if d == 1}
    left = {u for u,v,d in actions if d == 0}
    rp = {q:6+sum(x<q for x in right) for q in right}
    lp = {q:205+sum(x<q for x in left) for q in left}
    tiles = {}
    def put(j,t):
        if j in tiles:
            raise ValueError("duplicate tile index")
        tiles[j]=t
    h=lambda q,b:2*(q+1)+b
    put(0,(2,435,3,1)); put(1,(5,0,0,0))
    for j,(u,v,d) in enumerate(actions):
        put(j+2,((1-d)*lp.get(u,0),h(j//2,j%2),d*rp.get(u,0),v))
    for b in range(2):
        put(432+b,(0,h(215,b),0,h(215,b)))
        put(434+b,(0,b,0,b))
    for q in right:
        for b in range(2): put(424+2*rp[q]+b,(rp[q],b,0,h(q,b)))
    for q in left:
        for b in range(2): put(424+2*lp[q]+b,(0,b,lp[q],h(q,b)))
    for j in range(4): put(924+j,(0,j+430*(j//2),0,438))
    put(928,(2,434,2,0)); put(929,(3,436,4,4)); put(930,(4,436,4,0))
    for t in (434,435,436): put(497+t,(1,438,1,t))
    for a in (0,1,4):
        for b in range(3): put(934+3*a+b-6*(a//4),(a,437,b,437))
    if set(tiles) != set(range(943)):
        raise ValueError("incomplete indexed tiles")
    rho=lambda e:1 << (67*e)
    B=rho(8807)
    positions=(set(range(943))|set(range(983,993))|set(range(1003,1012))|
               set(range(1013,1032))|{1063,1064,1095,2195,3296})
    MC=B-1-sum(rho(e) for e in positions-{1})-2*rho(1063)
    MF=(B-1+4+((1<<51)-2)*(rho(4393)+rho(5495))+
        sum(rho(1013+j) for j in range(10))+sum(rho(1065+j) for j in range(9))+
        rho(2195)+rho(3296)+((1<<65)-1)*sum(rho(8792+j) for j in range(13))+
        ((1<<19)-1)*rho(8805))
    K=sum(rho(e) for e in (30,62,1100,2201,8849))
    for base in (4393,5495):
        for j in range(943):
            w,n,e,s=tiles[j]
            value=w+(n<<8)+(e<<17)+(s<<25)+(127<<34)
            K+=((1+(1<<51))-(1<<10)*value)*rho(base-j)
        for b,e,m_ in ((10,1023,8),(18,1013,9),(27,1003,8),(35,983,9),
                       (44,1031,1),(45,1022,1),(46,1011,1),(47,992,1),
                       (48,1095,1),(49,2195,1),(50,3296,1)):
            K+=sum((1<<(b+j))*rho(base-e-j) for j in range(m_))
    return dict(beta=B-1,K0=K,MC=MC,MF=MF)

def raw_bytes(value):
    return value.to_bytes((value.bit_length()+7)//8,"little")

if __name__ == "__main__":
    values=construct()
    binding=json.loads((Path(__file__).parent/"upstream133/compact/equation_85.json").read_text())["coefficient_binding"]["ports"]
    receipt={}
    for key,value in values.items():
        data=raw_bytes(value)
        row={"bits":value.bit_length(),"raw_sha256":hashlib.sha256(data).hexdigest()}
        for k,v in row.items():
            if binding[key][k] != v:
                raise ValueError((key,k,binding[key][k],v))
        receipt[key]=row
    print(json.dumps(receipt,indent=2))
