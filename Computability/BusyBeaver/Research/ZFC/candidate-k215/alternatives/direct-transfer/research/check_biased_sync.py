#!/usr/bin/env python3
"""Finite corroboration of the intended biased-parser synchronization proof."""
from math import isqrt
from pathlib import Path
import hashlib, json


def P(x, y): return (x+y)*(x+y+1)//2+y
def unP(n):
    s=(isqrt(8*n+1)-1)//2
    y=n-s*(s+1)//2
    return s-y,y
def decode(n):
    a,r=unP(n)
    if a==0: return ("S",),r,0
    if a==1:
        x,r=unP(r)
        return ("MP",x),r,1
    y,r=unP(r);x,r=unP(r)
    return ("AX",a-2,x,y),r,1
def step(L,b):
    assert L>0
    command,r,newb=decode(L-1+b)
    assert r<L
    return command,r,newb
def fields(k):
    if k[0]=="S":return [0]
    if k[0]=="MP":return [1,k[1]]
    return [k[1]+2,k[3],k[2]]
def beta(k):return int(k[0]!="S")
def encode(word,b,q):
    assert q>0
    if not word:return q
    r=encode(word[1:],beta(word[0]),q)
    for f in reversed(fields(word[0])):r=P(f,r)
    return 1-b+r
def main():
    for r in range(1,1001):
        a=P(2,P(1,P(0,r)));z=P(1,a);n=P(1,z)
        assert n+1==P(0,z+1)
        k,p,b=decode(n);assert k==("MP",1)
        k,p,b=step(p,b);assert(k,p,b)==(("AX",0,0,1),r,1)
        k,p,b=decode(n+1);assert k==("S",)
        k,p,b=step(p,b);assert k==("MP",2)
        k,p,b=step(p,b);assert(k,p,b)==(("MP",0),r,1)
        assert n>=r
    words=[[("S",)],[("MP",0),("S",)],[("AX",0,0,0),("S",),("MP",1),("S",)]]
    encodings=0
    for w in words:
        for b in (0,1):
            for q in (1,2,11):
                ptr=encode(w,b,q);assert ptr>=q
                bias=b
                for target in w:
                    k,ptr,bias=step(ptr,bias);assert k==target
                assert ptr==q
                encodings+=1
    result={"status":"PROPOSED_BIASED_PARSER_SYNCHRONIZATION_CHECK_PASS","consecutive_pairs":1000,
        "positive_tail_word_checks":encodings,
        "scope":"Abstract intended parser only; archived scratch-biased source does not implement it.",
        "checker_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    Path(__file__).with_name("biased_sync_result.json").write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result,indent=2))
if __name__=="__main__":main()
