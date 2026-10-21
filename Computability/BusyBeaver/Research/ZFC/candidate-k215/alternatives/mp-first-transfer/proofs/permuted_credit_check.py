#!/usr/bin/env python3
"""Independent standard-library checks of MP0/S1/AX>=2 scheduler credit.
Finite corroboration only; the universal proof is in permuted_credit.md.
"""
from math import isqrt
from functools import lru_cache
from pathlib import Path
import json,hashlib
N=500_000

def unpair(n):
    s=(isqrt(8*n+1)-1)//2
    y=n-s*(s+1)//2
    return s-y,y

def right(n): return unpair(n)[1]

def decode_shape(n):
    a,y=unpair(n)
    if a==0: return 'MP',0,right(y)
    if a==1: return 'S',-1,y
    return 'AX',10,right(right(y))

b=[];m=[];length=[];B=[0]
for n in range(N):
    tag,delta,res=decode_shape(n)
    j=res-1
    assert j<n
    bal=delta+(b[j] if res else 0)
    low=min(0,delta+(m[j] if res else 0))
    le=1+(length[j] if res else 0)
    assert le<=n+1
    b.append(bal);m.append(low);length.append(le);B.append(B[-1]+bal)

@lru_cache(None)
def explicit(n):
    tag,delta,res=decode_shape(n)
    return (tag,)+(explicit(res-1) if res else ())
explicit_count=1000
for n in range(explicit_count):
    bal=low=0
    for tag in explicit(n):
        bal += {'MP':0,'S':-1,'AX':10}[tag]
        low=min(low,bal)
    assert (bal,low,len(explicit(n)))==(b[n],m[n],length[n])
assert explicit(0)==('MP',) and explicit(1)==('S',) and explicit(2)==('MP',)
assert B[:4]==[0,0,-1,-1]
assert min(B[n]+m[n] for n in range(N))==-1
assert min(B[n]-B[1]+m[n] for n in range(1,N))==-1
assert all(B[k]+k>=0 for k in range(N+1))
diags=0
for s in range(2,isqrt(2*N)+2):
    lo=s*(s+1)//2; hi=(s+1)*(s+2)//2
    if hi>N: break
    assert all(B[n]-B[lo]+m[n]>=0 for n in range(lo,hi))
    assert B[hi]-B[lo]>=7*s-9
    assert B[lo]>=-1
    diags+=1

def exact_credit(cutoff):
    s=(isqrt(8*cutoff+1)-1)//2
    end=max(3,(s+1)*(s+2)//2)
    assert end<=N
    return max([0]+[-(B[n]-B[cutoff]+m[n]) for n in range(cutoff,end)])
assert exact_credit(0)==exact_credit(1)==1
assert exact_credit(2)==0
record={'status':'PERMUTED_TRANSFER_CREDIT_FINITE_CHECK_PASS','scope':'Finite corroboration of explicitly proved all-natural theorem; no binary simulation.','tags':{'MP':0,'S':1,'AX':'c+2'},'fields':{'MP':['0','x'],'S':['1'],'AX':['c+2','y','x']},'conservative_deltas':{'MP':0,'S':-1,'AX':10},'candidates':N,'explicit_words_compared':explicit_count,'complete_diagonals_checked':diags,'initial_words':[list(explicit(i)) for i in range(3)],'initial_B':B[:4],'minimum_from_zero':-1,'minimum_from_cutoff_one':-1,'credit_at_cutoff_one':1,'ten_head_bootstrap_margin':9,'credits_first_twenty':[exact_credit(i) for i in range(20)]}
file=Path(__file__).with_name('permuted_credit_result.json')
file.write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2))
