#!/usr/bin/env python3
"""Finite proof components and independent checks for the corrected biased scheduler.
This script does not validate any literal Turing-machine table.
"""
from math import isqrt
from pathlib import Path
import json,hashlib,argparse

def pair(a,b):
    return (a+b)*(a+b+1)//2+b

def unpair(n):
    s=(isqrt(8*n+1)-1)//2
    y=n-s*(s+1)//2
    return s-y,y

def right(n):return unpair(n)[1]

def parse(n):
    a,y=unpair(n)
    if a==0:return 'S', y-1 if y else None
    if a==1:
        r=right(y);return 'MP',r if r else None
    r=right(right(y));return 'AX',r if r else None

def end(n):
    while True:
        op,r=parse(n)
        if r is None:return int(op!='S')
        assert 0<=r<n
        n=r

def F(n):return pair(0,n+1)

def Fpow(n,k):
    for _ in range(k):n=F(n)
    return n

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path);a=ap.parse_args()
    limit=1024*1025//2
    counts=[];ends=[];balances=[];minima=[];lengths=[];total=0
    for n in range(limit):
        op,r=parse(n)
        assert r is None or 0<=r< n
        if r is not None:assert 2*(r+2)<=n+2
        cost=int(op=='S')
        w=cost+(counts[r] if r is not None else 0)
        ell=1+(lengths[r] if r is not None else 0)
        assert w<=ell<=(n+2).bit_length()-1
        total+=w
        assert total<=n+1,(n,total)
        counts.append(w);lengths.append(ell)
        ends.append(ends[r]if r is not None else int(op!='S'))
        b={'S':-1,'MP':0,'AX':10}[op]
        balances.append(b+(balances[r]if r is not None else 0))
        minima.append(min(0,b+(minima[r]if r is not None else 0)))
    # Actual initial phase and a finite check of the forced-hit theorem.
    n,previous_bias=1,1;balance=0;minimum=0;visits=[];small=[]
    while n<limit:
        visits.append(n)
        minimum=min(minimum,balance+minima[n])
        if n<128:small.append({'candidate':n,'incoming_balance':balance,'word_balance':balances[n],'word_minimum':minima[n]})
        balance+=balances[n]
        n,previous_bias=n+1+previous_bias,ends[n]
    assert minimum==0
    present=set(visits)
    forced=0
    for q in range(6,limit):
        if ends[q-5]==ends[q-4]==1 and ends[q-3]==0:
            assert q in present,q
            forced+=1
    # Integer, rather than symbolic-AST, checks of the synchronization algebra.
    checked=0
    for r in range(1,1001):
        z=Fpow(r,4)
        assert end(z)==end(r)
        assert end(z-1)==end(z-2)==1
        q=Fpow(r,7)
        assert [end(q-j)for j in (5,4,3)]==[1,1,end(r)]
        for c,u,v in ((0,0,0),(1,2,3),(17,43,r),(r,r,r)):
            p=pair(c+2,pair(v,pair(u,q)))
            assert [end(p-j)for j in (5,4,3)]==[1,1,end(r)]
            checked+=1
    # Universal inequalities used above the induction cutoff.
    for m in range(10,1000):assert (1<<(m//2))-1>=2*m
    result={'status':'ABSTRACT_SCHEDULER_FINITE_COMPONENTS_PASS',
      'scope':'Corrected root-return parser only; no physical machine is validated by this program.',
      'S_count_base_prefixes':limit,'S_count_sum_at_base':total,'maximum_S_count_in_base':max(counts),
      'length_bound_checked_inputs':limit,'first_candidate':1,'initial_bias':1,
      'actual_schedule_finite_minimum':minimum,'visited_candidates_checked':len(visits),
      'forced_hit_instances_checked':forced,'integer_AX_wrapper_identity_cases':checked,
      'first_128_candidate_receipt':small,
      'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    raw=json.dumps(result,indent=2)+'\n'
    if a.out:a.out.write_text(raw)
    print(raw)
if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must be enabled.')
    main()
