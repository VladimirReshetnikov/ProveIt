#!/usr/bin/env python3
"""Reconstruct four fixed BFS943/radix67 integers from the printed finite recipe.

No machine execution or refutation search is performed. Attribution:
ProveIt/163-trace-radical/compact/coefficient_recipe.tex at the pinned snapshot.
"""
from pathlib import Path
import gzip, hashlib, json

ROOT=Path(__file__).resolve().parent
SEED=''.join([
'BxEnhvy6NipzkWmROo0GsA3uK3twWLxscLq20UTumy5Cdu461LwD6g7RDNzF8Y',
'iYDFTpB8ehAypd7d6OsOL4APamnJeNXQypUezCmW9n4oXP6XfgmiWuAWZ8ZJ7U',
'OP7gu4kVdlGZqZHULQMar1dXNeJW4i7oNVI8usp8BlovjjZbwPCovZI328fRUq',
'4q92R81s5GjWQaQfGhkq9UYMK3rRMaBmsOIBkJqc2cj2VRIZ6mjzkBIOkW9SjZ',
'FzeA6J5u4j3sBL3SdgwXzM9mHvQivu8EJ1TBTpRhHDqZIbmYgwQ8VqTAFotl6F',
'We1YC554GKrVHsA8oUGKSA6F6k5KREBSD0Tgd7bFALY84LLbpw574BQyvdoHrl',
'0Oe35uwDf15DpT6VJWZBjSbHPpPAINYTte0eUxnTFTKBlGj8Am6sb1gLldh8WZ',
'8P'])
ALPHABET='0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz'

def construct():
    if len(SEED)!=436:raise ValueError('seed length')
    aa=0
    for c in SEED:aa=62*aa+ALPHABET.index(c)
    nn=aa%2**636;tt=(aa>>636)%2**1675;ee=aa>>2311
    special=[(nn>>(430+q))&1 for q in range(215)]
    flags=[];cum=0
    for m in special:
        flags.append(14 if not m else (ee>>(4*cum))&15)
        cum+=m
    targets=[];writes=[];directions=[];sigma=0
    for j in range(430):
        fresh=(nn>>j)&1
        targets.append(1+sigma if fresh else (tt//216**(j-sigma))%216)
        writes.append((flags[j//2]>>(2*(j%2)))&1)
        directions.append((flags[j//2]>>(2*(j%2)+1))&1)
        sigma+=fresh
    rr={targets[j] for j in range(430) if directions[j]==1}
    ll={targets[j] for j in range(430) if directions[j]==0}
    rn={q:6+sum(r<q for r in rr) for q in rr}
    ln={q:205+sum(l<q for l in ll) for q in ll}
    tiles={}
    def add(i,t):
        if i in tiles:raise ValueError(('duplicate tile',i))
        tiles[i]=t
    def h(q,b):return 2*(q+1)+b
    add(0,(2,435,3,1));add(1,(5,0,0,0))
    for j in range(430):
        u,v,d=targets[j],writes[j],directions[j]
        add(j+2,(ln[u] if d==0 else 0,h(j//2,j%2),rn[u] if d==1 else 0,v))
    for b in range(2):
        add(432+b,(0,h(215,b),0,h(215,b)));add(434+b,(0,b,0,b))
    for q in rr:
        for b in range(2):add(424+2*rn[q]+b,(rn[q],b,0,h(q,b)))
    for q in ll:
        for b in range(2):add(424+2*ln[q]+b,(0,b,ln[q],h(q,b)))
    for j in range(4):add(924+j,(0,j+430*(j//2),0,438))
    add(928,(2,434,2,0));add(929,(3,436,4,4));add(930,(4,436,4,0))
    for t in (434,435,436):add(497+t,(1,438,1,t))
    for a in (0,1,4):
        for b in range(3):add(934+3*a+b-6*(a//4),(a,437,b,437))
    if set(tiles)!=set(range(943)):raise ValueError(('tile coverage',len(tiles)))
    def power(e):
        if e<0:raise ValueError('negative fixed radix power')
        return 1<<(67*e)
    bb=power(8807);beta=bb-1
    es=set(range(943))|set(range(983,993))|set(range(1003,1012))|set(range(1013,1032))|{1063,1064,1095,2195,3296}
    mc=bb-1-sum(power(e) for e in es-{1})-2*power(1063)
    mf=bb-1+4+(2**51-2)*(power(4393)+power(5495))
    mf+=sum(power(1013+j) for j in range(10))+sum(power(1065+j) for j in range(9))+power(2195)+power(3296)
    mf+=(2**65-1)*sum(power(8792+j) for j in range(13))+(2**19-1)*power(8805)
    kk=sum(power(j) for j in (30,62,1100,2201,8849))
    for j in range(943):
        w,n,e,s=tiles[j];value=w+(n<<8)+(e<<17)+(s<<25)+(127<<34)
        coef=1+2**51-2**10*value
        kk+=coef*(power(4393-j)+power(5495-j))
    controller=[(10,1023,8),(18,1013,9),(27,1003,8),(35,983,9),(44,1031,1),(45,1022,1),(46,1011,1),(47,992,1),(48,1095,1),(49,2195,1),(50,3296,1)]
    for b,e,m in controller:
        for j in range(m):kk+=2**(b+j)*(power(4393-e-j)+power(5495-e-j))
    return {'beta':beta,'K0':kk,'MC':mc,'MF':mf}

def main():
    parent=json.loads((ROOT/'164-unsquared-factors-linear-selectors/positive/equation_bV.json').read_text())
    out=ROOT/'coefficients';out.mkdir(exist_ok=True);records=[]
    for name,value in construct().items():
        binding=parent['coefficient_binding']['ports'][name]
        raw=value.to_bytes((value.bit_length()+7)//8,'little')
        digest=hashlib.sha256(raw).hexdigest()
        if digest!=binding['raw_sha256'] or value.bit_length()!=binding['bits']:
            raise ValueError((name,value.bit_length(),digest,binding))
        data=gzip.compress(raw,compresslevel=9,mtime=0)
        (out/binding['file']).write_bytes(data)
        records.append({'name':name,'bits':value.bit_length(),'bytes':len(raw),'sha256':digest,'gzip_sha256':hashlib.sha256(data).hexdigest()})
    (out/'RECONSTRUCTION.json').write_text(json.dumps(records,indent=2)+'\n')
    print(json.dumps(records,indent=2))

if __name__=='__main__':main()
