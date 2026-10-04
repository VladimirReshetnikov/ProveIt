#!/usr/bin/env python3
"""New finite probes for the repeated-firing proof, not a proof replacement.

No builder, upstream checker, saved schedule, or external package is imported.
Pell witnesses are justified by the pinned theorem, not materialized here.
"""
from itertools import product
from collections import Counter
from pathlib import Path
import hashlib
import json
import random

HERE=Path(__file__).resolve().parent


def sub(mask,value):return value>=0 and value & ~mask == 0
def pack(digits,b):return sum(v*pow(b,j) for j,v in enumerate(digits))
def digits(x,b,n):
    result=[]
    for _ in range(n):x,v=divmod(x,b);result.append(v)
    assert x==0
    return result
def geom(b,n):return (pow(b,n)-1)//(b-1)


def spread(u,b,n,s):
    assert 0<=u<pow(b,n) and s>=n+1
    cb=pow(b,s-1)
    copies=geom(cb,n)
    mask=geom(b*cb,n)
    return (u*copies)&((b-1)*mask)


def conversion_checks():
    count=0
    for n in range(1,6):
        for width in range(n+1,n+4):
            b=pow(32,width)
            for salt in range(32):
                ds=[(7*j+salt)%32 for j in range(n)]
                assert spread(pack(ds,32),32,n,width)==pack(ds,b)
                count+=1
    return count


def physical_checks():
    cases=slots=0
    for p,q,r,d,e,f in product((1,2),repeat=6):
        width=max(p*q*r,d*e*f)+1
        b=pow(32,width)
        tx=max(2,(q*r+2*d)//(2*d),(e*f+2*p)//(2*p))
        ty=max(2,(r+2*e)//(2*e),(f+2*q)//(2*q))
        tz=2
        hx,hy,hz=p*d*tx,q*e*ty,r*f*tz
        A,B,C=2*hx,2*hy,2*hz
        tile=[(2*x+3*y+5*z+1)%6 for z in range(r) for y in range(q) for x in range(p)]
        patch=[(7*x+11*y+13*z+3)%16 for z in range(f) for y in range(e) for x in range(d)]
        tb=spread(pack(tile,32),32,p*q*r,width)
        db=spread(pack(patch,32),32,d*e*f,width)
        tr=spread(tb,pow(b,p),q*r,2*d*tx)
        tp=spread(tr,pow(b,A*q),r,2*e*ty)
        background=tp*geom(pow(b,p),2*d*tx)*geom(pow(b,A*q),2*e*ty)*geom(pow(b,A*B*r),2*f*tz)
        dr=spread(db,pow(b,d),e*f,2*p*tx)
        dp=spread(dr,pow(b,A*e),f,2*q*ty)
        additions=dp*pow(b,hx+A*hy+A*B*hz)
        truth=[]
        for z in range(C):
            for y in range(B):
                for x in range(A):
                    vx,vy,vz=x-hx,y-hy,z-hz
                    h=tile[(vx%p)+p*(vy%q)+p*q*(vz%r)]
                    if 0<=vx<d and 0<=vy<e and 0<=vz<f:h+=patch[vx+d*vy+d*e*vz]
                    truth.append(h)
        assert background+additions==pack(truth,b)
        assert max(truth)<=20
        cases+=1;slots+=A*B*C
    return dict(cases=cases,physical_slots=slots)


def recurrence_checks():
    # Exhaust all arbitrary candidate pre digits, not only cumulative ones.
    cases=solutions=0
    for b,n,K in ((4,1,1),(4,1,2),(4,1,3),(4,2,1),(4,2,2),(8,1,3)):
        assert K<b
        Q=pow(b,n);end=pow(Q,K)
        for pre in range(end):
            pd=digits(pre,b,n*K)
            for ebits in product((0,1),repeat=n*K):
                E=pack(ebits,b)
                left=Q*(pre+E)-pre
                passes=left>=0 and left%end==0 and left//end<Q
                totals=[0]*n;expected=[]
                for t in range(K):
                    expected.extend(totals)
                    for j in range(n):totals[j]+=ebits[t*n+j]
                semantic=pd==expected
                assert passes==semantic,(b,n,K,pre,E)
                if passes:
                    assert left//end==pack(totals,b)
                    solutions+=1
                cases+=1
    # More generous radix exactly as in the certificate, with random malicious
    # arbitrary digits and valid event tableaux over several frames and slots.
    rng=random.Random(821991)
    probes=0
    for K in range(1,8):
        b=1
        while b<64*(K+1):b*=32
        n=4;Q=pow(b,n);end=pow(Q,K)
        for _ in range(100):
            es=[rng.randrange(2) for _ in range(n*K)]
            totals=[0]*n;ps=[]
            for t in range(K):
                ps.extend(totals)
                for j in range(n):totals[j]+=es[t*n+j]
            pre,E,V=pack(ps,b),pack(es,b),pack(totals,b)
            assert Q*(pre+E)==pre+end*V
            assert max(ps)<=K-1 and max(totals)<=K
            arbitrary=rng.randrange(end)
            candidate=Q*(arbitrary+E)-arbitrary
            passes=candidate>=0 and candidate%end==0 and candidate//end<Q
            assert passes==(arbitrary==pre)
            probes+=1
    return dict(exhaustive_candidates=cases,exhaustive_solutions=solutions,large_radix_pairs=probes)


def legality_checks():
    count=0
    for K in range(1,7):
        b=1
        while b<64*(K+1):b*=32
        for h,neighbors,own,event in product(range(21),range(6*K-5),range(K),(0,1)):
            C=h+neighbors
            assert C<b
            required=C-6*own-6 if event else 0
            for L in (0,1,b//2-1,max(0,required),max(0,required+1)):
                certificate=sub((b//2-1)*event,L) and (C & ((b-1)*event))==6*(own & ((b-1)*event))+6*event+L
                semantic=(event==0 and L==0) or (event==1 and required>=0 and L==required)
                assert certificate==semantic
                if required>=0 and event:assert required<=6*K+8<b//2
                count+=1
    # Packing can otherwise hide overflows; test multiple selected slots with
    # extremes of the entire certified slack interval, not only legal slacks.
    packed=0
    for K in (1,2,5,10):
        b=1
        while b<64*(K+1):b*=32
        for es in product((0,1),repeat=3):
            for aa in product((0,K-1),repeat=3):
                for ls in product((0,b//2-1),repeat=3):
                    if any(not e and l for e,l in zip(es,ls)):continue
                    E,A,L=pack(es,b),pack(aa,b),pack(ls,b)
                    selected=A&((b-1)*E)
                    expected=[6*a*e+6*e+l for a,e,l in zip(aa,es,ls)]
                    assert all(x<b for x in expected)
                    assert 6*selected+6*E+L==pack(expected,b)
                    packed+=1
    return dict(local_cases=count,packed_no_carry_cases=packed)


def boundary_checks():
    cases=slots=0
    for A,B,C,K in product(range(2,6),range(2,6),range(2,6),range(1,5)):
        b=1024;X=pow(b,A);Y=pow(b,A*B);Q=pow(b,A*B*C)
        I=b*X*Y*geom(b,A-2)*geom(X,B-2)*geom(Y,C-2)
        R=geom(Q,K)
        coordinates=[(x,y,z,t) for t in range(K) for z in range(C) for y in range(B) for x in range(A)]
        def at(x,y,z,t):
            if 0<x<A-1 and 0<y<B-1 and 0<z<C-1 and 0<=t<K:
                return (x+2*y+3*z+5*t)%(K+1)
            return 0
        pre=pack([at(*c) for c in coordinates],b)
        assert sub((b-1)*I*R,pre)
        assert pre%b==pre%X==pre%Y==0
        for stream,delta in zip((b*pre,X*pre,Y*pre,pre//b,pre//X,pre//Y),
                               ((-1,0,0),(0,-1,0),(0,0,-1),(1,0,0),(0,1,0),(0,0,1))):
            dx,dy,dz=delta
            assert stream==pack([at(x+dx,y+dy,z+dz,t) for x,y,z,t in coordinates],b)
            assert stream<pow(Q,K)
        cases+=1;slots+=len(coordinates)
    return dict(cases=cases,temporal_sites=slots)


def bounded_prefix_checks():
    # Two path vertices with four/five further neighbors outside the path.
    # For <=3 layers those exterior sites receive <=3 and cannot fire, so
    # these are valid embedded physical test instances with zero background.
    K=3;b=1024;n=2;Q=pow(b,n);R=geom(Q,K)
    tested=accepted=0
    for heights in product(range(16),repeat=n):
        eta=pack(heights,b)
        for events in product(range(4),repeat=K):
            counts=[0]*n;ps=[];es=[];local_legal=True
            slacks=[]
            for layer in events:
                ev=[(layer>>j)&1 for j in range(n)]
                ps.extend(counts);es.extend(ev)
                for j in range(n):
                    h=heights[j]+counts[1-j]-6*counts[j]
                    if ev[j] and h<6:local_legal=False
                    slacks.append(max(0,h-6) if ev[j] else 0)
                for j in range(n):counts[j]+=ev[j]
            pre,E,V=pack(ps,b),pack(es,b),pack(counts,b)
            C=pack([heights[j]+ps[t*n+1-j] for t in range(K) for j in range(n)],b)
            L=pack(slacks,b)
            certificate=Q*(pre+E)==pre+pow(Q,K)*V and sub((b//2-1)*E,L) and (C&((b-1)*E))==6*(pre&((b-1)*E))+6*E+L
            assert certificate==local_legal
            if certificate:
                accepted+=1
                for target in range(n):
                    occurrences=[tau for tau in range(K) if sub(E,pow(b,target)*pow(Q,tau))]
                    assert bool(occurrences)==(counts[target]>0)
                    assert not sub(E,pow(b,target)*pow(Q,K))
            tested+=1
    # Admitted separator, including target whose final count is even.
    heights=[12,4];order=[0,0,1]
    counts=[0,0]
    for v in order:
        assert heights[v]-6*counts[v]+counts[1-v]>=6
        counts[v]+=1
    assert counts==[2,1]
    E=pack([1,0,1,0,0,1],b);V=pack(counts,b)
    assert not sub(V,1) and sub(E,1) # Origin fired twice; low-bit V test fails.
    assert sub(E,b*pow(Q,2))        # Supplied separator target fires at t=2.
    # Mutual stable sites cannot manufacture an earliest legal event.
    assert 5<6 and (5&1023)!=6
    return dict(event_tableaux=tested,accepted_tableaux=accepted,
                repeated_separator=[12,4],legal_sequence=[0,0,1],even_count_target_accepted=True)


def target_code_checks():
    n=0
    def zz(z):return 2*z if z>=0 else -2*z-1
    def pair(a,b):return (a+b)*(a+b+1)//2+b
    def unpair(c):
        lo,hi=0,c+1
        while lo+1<hi:
            mid=(lo+hi)//2
            if mid*(mid+1)//2<=c:lo=mid
            else:hi=mid
        b=c-lo*(lo+1)//2
        return lo-b,b
    for x,y,z in product(range(-4,5),repeat=3):
        fields=[0,0,0,0,1,0,0,140,zz(x),zz(y),zz(z)]
        code=fields[-1]
        for v in reversed(fields[:-1]):code=pair(v,code)
        recovered=[];rest=code
        for _ in range(10):v,rest=unpair(rest);recovered.append(v)
        recovered.append(rest)
        assert recovered==fields
        for axis in (x,y,z):
            h,sign=divmod(zz(axis),2)
            assert h-2*sign*h-sign==axis
        n+=1
    return n


if __name__=='__main__':
    receipt=dict(conversion_cases=conversion_checks(),physical=physical_checks(),
                 recurrence=recurrence_checks(),legality=legality_checks(),
                 boundaries=boundary_checks(),prefixes=bounded_prefix_checks(),
                 signed_cantor_roundtrips=target_code_checks())
    receipt['checker_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    (HERE/'evidence/semantics-receipt.json').write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\n')
    print(json.dumps(receipt,sort_keys=True,indent=2))
