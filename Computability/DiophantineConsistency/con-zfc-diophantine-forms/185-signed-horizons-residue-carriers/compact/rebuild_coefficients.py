#!/usr/bin/env python3
"""Reconstruct all four inherited Start-only4127 integers from the printed seed.

The recipe and decoder are credited to ProveIt package 174; this independent
small entry point checks complete bytes, not a selection of modular residues.
"""
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parent
ALPHABET='0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz'
SEED=(
    'BxEnhvy6NipzkWmROo0GsA3uK3twWLxscLq20UTumy5Cdu461LwD6g7RDNzF8Y'
    'iYDFTpB8ehAypd7d6OsOL4APamnJeNXQypUezCmW9n4oXP6XfgmiWuAWZ8ZJ7U'
    'OP7gu4kVdlGZqZHULQMar1dXNeJW4i7oNVI8usp8BlovjjZbwPCovZI328fRUq'
    '4q92R81s5GjWQaQfGhkq9UYMK3rRMaBmsOIBkJqc2cj2VRIZ6mjzkBIOkW9SjZ'
    'FzeA6J5u4j3sBL3SdgwXzM9mHvQivu8EJ1TBTpRhHDqZIbmYgwQ8VqTAFotl6F'
    'We1YC554GKrVHsA8oUGKSA6F6k5KREBSD0Tgd7bFALY84LLbpw574BQyvdoHrl'
    '0Oe35uwDf15DpT6VJWZBjSbHPpPAINYTte0eUxnTFTKBlGj8Am6sb1gLldh8WZ8P'
)

def need(ok,msg):
    if not ok: raise ValueError(msg)

need(len(SEED)==436,'Seed length')
A=0
for s in SEED: A=62*A+ALPHABET.index(s)
N=A%(1<<636); T=(A>>636)%(1<<1675); E=A>>2311
bit=lambda n,j:(n>>j)&1
digit=lambda n,b,j:(n//b**j)%b
actions=[]
for j in range(430):
    q,b=divmod(j,2)
    nu=bit(N,j); sigma=sum(bit(N,k) for k in range(j))
    m=bit(N,430+q); tau=sum(bit(N,430+k) for k in range(q))
    F=14+m*(digit(E,16,tau)-14)
    u=nu*(1+sigma)+(1-nu)*digit(T,216,j-sigma)
    actions.append((u,bit(F,2*b),bit(F,2*b+1)))
sets=[sorted({u for u,v,d in actions if d==x}) for x in (0,1)]
rank=lambda d,q:205-199*d+sum(x<q for x in sets[d])
h=lambda q,b:2*q+b+2
tiles={0:(2,435,3,1),1:(5,0,0,0)}
def tile(j,t):
    need(j not in tiles,'Duplicate tile index')
    tiles[j]=t
for j,(u,v,d) in enumerate(actions):
    q,b=divmod(j,2)
    tile(j+2,((1-d)*rank(0,u),h(q,b),d*rank(1,u),v))
for a in (0,1):
    for b in (0,1):
        tile(434-2*a+b,(0,432*a+b,0,432*a+b))
        tile(924+2*a+b,(0,432*a+b,0,438))
for d in (0,1):
    for q in sets[d]:
        r=rank(d,q)
        for b in (0,1):tile(424+2*r+b,(d*r,b,(1-d)*r,h(q,b)))
for j,t in enumerate(((2,434,2,0),(3,436,4,4),(4,436,4,0)),928):tile(j,t)
for t in (434,435,436):tile(497+t,(1,438,1,t))
for a in (0,1,2):
    for b in (0,1,2):tile(934+3*a+b,(a*a,437,b,437))
need(set(tiles)==set(range(943)),'Tile index coverage')
weights={j:1+2**10*(1+w+2**8*n+2**17*p+2**25*s)
         for j,(w,n,p,s) in tiles.items()}
for first,shift,count in ((943,35,9),(973,18,9),(992,27,8),(1002,10,8)):
    for j in range(count):weights[first+j]=1<<(shift+j)
physical=set(range(943))|set(range(943,952))|set(range(973,982))
physical|=set(range(992,1000))|set(range(1002,1010))|{990,991,1031}
p=lambda j:1<<(47*j)
B=p(4127); beta=B-1
DC=p(20)+p(30)+p(1031)+sum(v*(p(2042-j)+p(3074-j)) for j,v in weights.items())
K0=DC+p(4137)
MC=beta-sum(p(j) for j in physical if j!=1)-2*p(990)
core=sum(p(973+j) for j in range(9))+sum(p(1012+j) for j in range(8))+p(1031)
MF=B+3+(2**44-2)*(p(2042)+p(3074))+core+2**29*p(4124)-p(4106)
ports={'beta':beta,'K0':K0,'MC':MC,'MF':MF}
binding=json.loads((ROOT/'inherited/P66.json').read_text())['coefficient_binding']['ports']
receipts={}
for name,value in ports.items():
    raw=value.to_bytes((value.bit_length()+7)//8,'big')
    info=binding[name]
    need(len(raw)==info['bytes'] and value.bit_length()==info['bits'],'Coefficient size')
    need(hashlib.sha256(raw).hexdigest()==info['sha256'],'Whole coefficient identity')
    need(raw==(ROOT/'coefficients'/info['file']).read_bytes(),'Whole materialized bytes')
    receipts[name]={'bits':value.bit_length(),'bytes':len(raw),'sha256':info['sha256']}
need(0<MC<beta<MF<2*beta and K0>0,'Coefficient box')
print(json.dumps({'status':'PASS','seed_characters':436,'decoded_actions':430,
                  'decoded_tiles':943,'raw_bytes':sum(x['bytes'] for x in receipts.values()),
                  'coefficients':receipts},indent=2))
