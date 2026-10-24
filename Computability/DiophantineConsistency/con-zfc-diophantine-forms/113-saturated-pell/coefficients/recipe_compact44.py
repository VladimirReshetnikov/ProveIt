#!/usr/bin/env python3
"""Reconstruct the complete coherent BFS44 tuple from the printed finite recipe.

No network, external table, variable exponent, or proof search is used.
All loops have fixed finite bounds. Output integers are constants of the
Diophantine equation, never existentially quantified inputs.
"""
from pathlib import Path
import gzip
import hashlib
import json

ALPHABET='0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz'
SEED=''.join('''
BxEnhvy6NipzkWmROo0GsA3uK3twWLxscLq20UTumy5Cdu461LwD6g7RDNzF8Y
iYDFTpB8ehAypd7d6OsOL4APamnJeNXQypUezCmW9n4oXP6XfgmiWuAWZ8ZJ7U
OP7gu4kVdlGZqZHULQMar1dXNeJW4i7oNVI8usp8BlovjjZbwPCovZI328fRUq
4q92R81s5GjWQaQfGhkq9UYMK3rRMaBmsOIBkJqc2cj2VRIZ6mjzkBIOkW9SjZ
FzeA6J5u4j3sBL3SdgwXzM9mHvQivu8EJ1TBTpRhHDqZIbmYgwQ8VqTAFotl6F
We1YC554GKrVHsA8oUGKSA6F6k5KREBSD0Tgd7bFALY84LLbpw574BQyvdoHrl
0Oe35uwDf15DpT6VJWZBjSbHPpPAINYTte0eUxnTFTKBlGj8Am6sb1gLldh8WZ
8P
'''.split())

def need(ok,message):
    if not ok: raise ValueError(message)

def recipe():
    need(len(SEED)==436,'complete 436-character seed')
    number=0
    for char in SEED: number=62*number+ALPHABET.index(char)
    N=number % (1<<636)
    targets=(number>>636) % (1<<1675)
    flags=number>>2311
    actions=[];sigma=0;tau=0
    for q in range(215):
        m=(N>>(430+q))&1
        f=((flags>>(4*tau))&15) if m else 14
        tau+=m
        for b in range(2):
            j=2*q+b;nu=(N>>j)&1
            u=1+sigma if nu else (targets//(216**(j-sigma)))%216
            actions.append((u,(f>>(2*b))&1,(f>>(2*b+1))&1))
            sigma+=nu
    need(actions[0]==(1,1,1),'correct renamed constructor target')
    right={u for u,v,d in actions if d==1}
    left={u for u,v,d in actions if d==0}
    rr={q:6+i for i,q in enumerate(sorted(right))}
    ll={q:205+i for i,q in enumerate(sorted(left))}
    h=lambda q,b:2*(q+1)+b
    tiles=set()
    for j,(u,v,d) in enumerate(actions):
        tiles.add((0 if d else ll[u],h(j//2,j%2),rr[u] if d else 0,v))
    for b in [0,1]:
        tiles.update([(0,h(215,b),0,h(215,b)),(0,b,0,b)])
    for q in right:
        for b in [0,1]: tiles.add((rr[q],b,0,h(q,b)))
    for q in left:
        for b in [0,1]: tiles.add((0,b,ll[q],h(q,b)))
    for t in [0,1,432,433]: tiles.add((0,t,0,438))
    tiles.update([(2,434,2,0),(2,435,3,1),(3,436,4,h(actions[0][0],0)),(4,436,4,0),(5,0,0,0)])
    for t in [434,435,436]: tiles.add((1,438,1,t))
    for a in [0,1,4]:
        for b in [0,1,2]: tiles.add((a,437,b,437))
    need(len(tiles)==943,'exact 943-tile inventory')
    start=(2,435,3,1);finish=(5,0,0,0)
    ordered=[start,finish]+sorted(tiles-{start,finish})
    # Lexicographic order equals the printed base-1024 key order.
    need(all(0<=v<1024 for t in tiles for v in t),'rank-key bounds')
    value=lambda t:t[0]+(t[1]<<8)+(t[2]<<17)+(t[3]<<25)+(127<<34)
    rp=lambda e:1<<(67*e)
    beta=rp(8807)-1
    E=set(range(943))|set(range(983,993))|set(range(1003,1012))|set(range(1013,1032))|{1063,1064,1095,2195,3296}
    MC=beta-sum(rp(e) for e in E-{1})-2*rp(1063)
    MF=(beta+4+((1<<51)-2)*(rp(4393)+rp(5495))
        +sum(rp(e) for e in range(1013,1023))
        +sum(rp(e) for e in range(1065,1074))+rp(2195)+rp(3296)
        +((1<<65)-1)*sum(rp(e) for e in range(8792,8805))
        +((1<<19)-1)*rp(8805))
    K=sum(rp(e) for e in [30,62,1100,2201,8849])
    for rank,t in enumerate(ordered):
        coefficient=1+(1<<51)-(1<<10)*value(t)
        K+=coefficient*(rp(4393-rank)+rp(5495-rank))
    control=[(10,1023,8),(18,1013,9),(27,1003,8),(35,983,9),(44,1031,1),(45,1022,1),(46,1011,1),(47,992,1),(48,1095,1),(49,2195,1),(50,3296,1)]
    for bit,e,m in control:
        for j in range(m): K+=(1<<(bit+j))*(rp(4393-e-j)+rp(5495-e-j))
    need(beta%2==1 and beta>=31 and K>0 and 0<MC<beta<MF<2*beta,'complete port box')
    return {'beta':beta,'K0':K,'MC':MC,'MF':MF}

def verify():
    directory=Path(__file__).resolve().parent/'compact44_bfs'
    names={'beta':'beta.bin.gz','K0':'K.bin.gz','MC':'MC.bin.gz','MF':'MF_source.bin.gz'}
    out={}
    for name,n in recipe().items():
        raw=gzip.decompress((directory/names[name]).read_bytes())
        need(n==int.from_bytes(raw,'little'),'whole coefficient equality: '+name)
        out[name]={'bits':n.bit_length(),'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest()}
    return out

if __name__=='__main__':
    print(json.dumps({'seed_characters':436,'tiles':943,'whole_tuple':verify()},indent=2))
