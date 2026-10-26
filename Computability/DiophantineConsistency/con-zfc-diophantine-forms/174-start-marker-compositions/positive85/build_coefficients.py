#!/usr/bin/env python3
"""Reconstruct all four fixed ports from the complete printed radix67 recipe.

Only fixed loops occur here. These computations define integer coefficients;
they introduce no Diophantine variables and require no network or external
repository. Raw output is canonical unsigned big-endian unless the historical
hash identifies little-endian; the resulting metadata states the byte order.
"""
import gzip
import hashlib
import json
from pathlib import Path
import argparse

ROOT=Path(__file__).resolve().parent
ALPHABET="0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"
SEED=(
"BxEnhvy6NipzkWmROo0GsA3uK3twWLxscLq20UTumy5Cdu461LwD6g7RDNzF8Y"
"iYDFTpB8ehAypd7d6OsOL4APamnJeNXQypUezCmW9n4oXP6XfgmiWuAWZ8ZJ7U"
"OP7gu4kVdlGZqZHULQMar1dXNeJW4i7oNVI8usp8BlovjjZbwPCovZI328fRUq"
"4q92R81s5GjWQaQfGhkq9UYMK3rRMaBmsOIBkJqc2cj2VRIZ6mjzkBIOkW9SjZ"
"FzeA6J5u4j3sBL3SdgwXzM9mHvQivu8EJ1TBTpRhHDqZIbmYgwQ8VqTAFotl6F"
"We1YC554GKrVHsA8oUGKSA6F6k5KREBSD0Tgd7bFALY84LLbpw574BQyvdoHrl"
"0Oe35uwDf15DpT6VJWZBjSbHPpPAINYTte0eUxnTFTKBlGj8Am6sb1gLldh8WZ"
"8P")

def need(x,msg):
    if not x:raise ValueError(msg)

def tiles():
    need(len(SEED)==436,"seed length")
    a=0
    for ch in SEED:a=62*a+ALPHABET.index(ch)
    N=a%(1<<636);T0=(a>>636)%(1<<1675);E0=a>>2311
    sigma=0;tau=0;actions=[]
    for q in range(215):
        m=(N>>(430+q))&1
        Fq=14*(1-m)+m*((E0>>(4*tau))&15)
        tau+=m
        for b in (0,1):
            j=2*q+b;nu=(N>>j)&1
            target=nu*(1+sigma)+(1-nu)*((T0//(216**(j-sigma)))%216)
            v=(Fq>>(2*b))&1;d=(Fq>>(2*b+1))&1
            actions.append((target,v,d));sigma+=nu
    need(len(actions)==430 and actions[0]==(1,1,1),"actions")
    R=sorted({u for u,v,d in actions if d==1})
    L=sorted({u for u,v,d in actions if d==0})
    rr={q:6+j for j,q in enumerate(R)}
    ll={q:205+j for j,q in enumerate(L)}
    out={}
    def put(i,t):
        need(i not in out,"duplicate tile "+str(i));out[i]=t
    def h(q,b):return 2*(q+1)+b
    put(0,(2,435,3,1));put(1,(5,0,0,0))
    for j,(u,v,d) in enumerate(actions):
        q,b=divmod(j,2)
        put(j+2,((1-d)*ll.get(u,0),h(q,b),d*rr.get(u,0),v))
    for b in (0,1):
        put(432+b,(0,h(215,b),0,h(215,b)))
        put(434+b,(0,b,0,b))
    for q in R:
        for b in (0,1):put(424+2*rr[q]+b,(rr[q],b,0,h(q,b)))
    for q in L:
        for b in (0,1):put(424+2*ll[q]+b,(0,b,ll[q],h(q,b)))
    for j in range(4):put(924+j,(0,j+430*(j//2),0,438))
    put(928,(2,434,2,0));put(929,(3,436,4,4));put(930,(4,436,4,0))
    for t in (434,435,436):put(497+t,(1,438,1,t))
    for a in (0,1,4):
        for b in (0,1,2):put(934+3*a+b-6*(a//4),(a,437,b,437))
    need(set(out)==set(range(943)),"incomplete tile table")
    return [out[i] for i in range(943)]

def reconstruct():
    r=1<<67;B=1<<590069;beta=B-1
    def rp(e):return 1<<(67*e)
    def geom(m):return ((1<<(67*m))-1)//(r-1)
    E=set(range(943))|set(range(983,993))|set(range(1003,1012))|set(range(1013,1032))|{1063,1064,1095,2195,3296}
    MC=B-1-sum(rp(e) for e in E-{1})-2*rp(1063)
    MF=B-1+4+((1<<51)-2)*(rp(4393)+rp(5495))
    MF+=rp(1013)*geom(10)+rp(1065)*geom(9)+rp(2195)+rp(3296)
    MF+=((1<<65)-1)*rp(8792)*geom(13)+((1<<19)-1)*rp(8805)
    phi={}
    for i,(w,n,e,s) in enumerate(tiles()):
        v=w+(1<<8)*n+(1<<17)*e+(1<<25)*s+127*(1<<34)
        phi[i]=1+(1<<51)-(1<<10)*v
    controls=[(10,1023,8),(18,1013,9),(27,1003,8),(35,983,9),
              (44,1031,1),(45,1022,1),(46,1011,1),(47,992,1),
              (48,1095,1),(49,2195,1),(50,3296,1)]
    for b,e,m in controls:
        for j in range(m):phi[e+j]=phi.get(e+j,0)+(1<<(b+j))
    K=sum(rp(e) for e in (30,62,1100,2201,8849))
    K+=sum(v*(rp(4393-e)+rp(5495-e)) for e,v in phi.items())
    need(0<MC<beta<MF<2*beta and K>0,"port bounds")
    return {'beta':beta,'K0':K,'MC':MC,'MF':MF}

def build(write=False):
    expected=json.loads((ROOT/'inherited/inverse85_degree304.json').read_text())['coefficient_binding']['ports']
    values=reconstruct();meta={}
    if write:(ROOT/'coefficients').mkdir(exist_ok=True)
    for name,n in values.items():
        need(n.bit_length()==expected[name]['bits'],"bit length "+name)
        rawbe=n.to_bytes((n.bit_length()+7)//8,'big')
        rawle=n.to_bytes((n.bit_length()+7)//8,'little')
        want=expected[name]['raw_sha256']
        if hashlib.sha256(rawbe).hexdigest()==want:raw=rawbe;order='big'
        elif hashlib.sha256(rawle).hexdigest()==want:raw=rawle;order='little'
        else:raise ValueError("both raw hash reconstructions fail: "+name)
        filename=name+'.bin.gz';compressed=gzip.compress(raw,mtime=0)
        meta[name]={'file':filename,'bits':n.bit_length(),'raw_bytes':len(raw),
                    'byte_order':order,'raw_sha256':want,
                    'gzip_sha256':hashlib.sha256(compressed).hexdigest(),
                    'historical_gzip_sha256':expected[name]['gzip_sha256']}
        if write:(ROOT/'coefficients'/filename).write_bytes(compressed)
        else:
            saved=ROOT/'coefficients'/filename
            need(saved.exists(),"run build_coefficients.py --write first")
            need(gzip.decompress(saved.read_bytes())==raw,"saved payload value "+name)
    report={'status':'PASS','source':'Complete fixed indexed BFS943 radix67 recipe',
            'definition':'inherited/coefficient_recipe.tex','ports':meta,
            'total_raw_bytes':sum(v['raw_bytes'] for v in meta.values()),
            'compressed_bytes':sum((ROOT/'coefficients'/v['file']).stat().st_size for v in meta.values())}
    if write:(ROOT/'coefficients/manifest.json').write_text(json.dumps(report,indent=2)+'\n')
    return report

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--write',action='store_true')
    print(json.dumps(build(p.parse_args().write),indent=2))

