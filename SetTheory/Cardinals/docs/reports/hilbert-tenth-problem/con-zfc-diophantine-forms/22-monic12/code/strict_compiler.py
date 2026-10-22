#!/usr/bin/env python3
"""Finite coefficient compiler for blank K215, strict four-cell windows.

This script does not run K215 to completion and never expands the four enormous
integer coefficients.  The recipe, finite alphabet, and geometry are exact.
"""
from pathlib import Path
from collections import Counter
from itertools import product
import hashlib
import json

HERE = Path(__file__).resolve().parent
TRANSITIONS = HERE.parent / 'data/k215_transitions.json'
L, Q, R, V, H = 434, 435, 436, 437, 438
PHASES = {L, Q, R}
EDGES = {(L,L), (L,Q), (Q,R), (R,R)}
START = (L,Q,R,1)
FORBIDDEN = (H,0,0,H)

def payload(x):
    if x < 434:
        a,b = divmod(x,2)
        return b, None if a == 0 else a-1
    return 0, 0 if x == Q else None

def compatible(a,b):
    if a == V:
        return b != V and (b not in PHASES or b == L)
    if b == V:
        return a not in PHASES or a == R
    return ((a == H) == (b == H) and
            (a in PHASES) == (b in PHASES) and
            (a not in PHASES or (a,b) in EDGES))

def successors(l,c,r,delta):
    if sum(payload(x)[1] is not None for x in (l,c,r)) > 1:
        return []
    if not (compatible(l,c) and compatible(c,r)):
        return []
    # A finite run can be padded by two unvisited blank cells at each wall.
    if V in (l,c,r) and any(x not in {0,L,R,V,H} for x in (l,c,r)):
        return []
    if c == V:
        return [V]
    if c == H:
        return [n for n in (L,Q,R)
                if not (l == V and n != L) and not (r == V and n != R)]
    bit,state = payload(c)
    if state is not None:
        write,move,_ = delta[state,bit]
        if (move == -1 and l == V) or (move == 1 and r == V):
            return []
    else:
        write = bit
    out = []
    if not any(x in PHASES for x in (l,c,r)) and all(payload(x)[1] in (None,215) for x in (l,c,r)):
        out.append(H)
    arrivals = []
    for x,direction in ((l,1),(c,0),(r,-1)):
        b,q = payload(x)
        if q is not None and delta[q,b][1] == direction:
            arrivals.append(delta[q,b][2])
    if l != H and r != H and len(arrivals) <= 1:
        out.append(write if not arrivals else 2*(arrivals[0]+1)+write)
    return out

def alphabet(delta):
    headless = [x for x in range(439) if payload(x)[1] is None]
    heads = [x for x in range(439) if payload(x)[1] is not None]
    triples = list(product(headless,repeat=3))
    for pos in range(3):
        for q in heads:
            for pair in product(headless,repeat=2):
                row = list(pair); row.insert(pos,q); triples.append(tuple(row))
    windows = {t+(n,) for t in triples for n in successors(*t,delta)}
    assert START in windows and FORBIDDEN not in windows
    return [START,FORBIDDEN]+sorted(windows-{START})

def layout(windows):
    k=len(windows); a=439; ell=(k+1).bit_length()
    base=2*ell+11*a+8
    p=max(0,(k+4*a+4-base+1)//2)
    m=base+2*p; nd=m+1-k-4*a-4
    es=k+12*a; M=k+15*a+nd
    anchor_factors=(1,3,5,11)
    Emax=11*M; Hc=19*M+3*a+1
    T1=Hc+2*Emax+a+1
    gap=2*Emax+2
    while gap%4 != 2: gap+=1
    T2=T1+gap
    coords=((1,0),(1,1),(1,2),(2,1))
    def e(rc,s):
        r,c=rc
        return k+3*a+(2-r)*3*a+(2-c)*a+s
    offsets=[e(rc,0) for rc in coords]
    copies={e(rc,s) for rc in coords for s in range(a)}
    anchors={j*M for j in anchor_factors}
    support=set(range(k))|copies|set(range(es,es+nd))|anchors
    assert len(support)==m+1 and max(support)==Emax
    cell=1
    while cell < T2+2*Emax+2: cell*=5
    bmin=max(ell*(4*a+5+p)+3,
             ell*(4*a+4)+(4*(m+3)*(18*(k+4*a+4)+6)+8).bit_length()+1,4)
    b=1
    while b < bmin: b*=5
    bare=(3*a,Hc+a,4*M,8*M)
    targets=[]
    for s in range(a):
        targets.append((e((1,1),s),{e((2,1),s)},set(),{e((1,1),s)}))
        for dst,src in (((1,0),(1,1)),((1,1),(1,2))):
            targets.append((Hc+e(dst,s),{e(src,s)},{e(dst,s)},set()))
    targets += [(5*M,{M},set(),{5*M}),(11*M,{3*M},set(),{11*M})]
    assert len({t for t,*_ in targets}) == 3*a+2
    for t,want0,want1,want2 in targets:
        assert {t-v for v in bare if t-v in support} == want0
        assert ({t-Hc} if t-Hc in support else set()) == want1
        assert ({t} if t in support else set()) == want2
        assert t < T1-Emax
    expand=support|{es+1}
    assert not ({(T1-e)%cell for e in expand}&{(T2-e)%cell for e in expand})
    assert {(5*M-e)%cell for e in support}&{(11*M-e)%cell for e in support} == {0}
    for t,other in ((T1,T2),(T2,T1)):
        assert not ({t-v for v in bare}&support)
        assert all(other+x-t not in support for x in support)
    A=1<<ell
    mu=A-2+(pow(A,4*a+5+p)-A)//(A-1)
    census=Counter((j,x) for row in windows for j,x in enumerate(row))
    total_v=k+sum((census[j,x]+1)*pow(A,1+j*a+x)
                  for j in range(4) for x in range(a))
    total_v+=sum((k+1)*pow(A,4*a+t) for t in range(1,5))
    mass=(m+3)*(2*total_v+6)
    assert 2*mu.bit_count()+3*a+2 == m
    assert 4*mass+8 < 1<<b and 2*mu+4 < 1<<b
    assert gap%4==2 and gap>2*Emax
    dcmod5=sum(pow(2,x,5) for x in bare)%5
    assert (2*dcmod5-pow(2,Hc,5))%5==3
    return dict(k=k,a=a,ell=ell,p=p,m=m,dummy_count=nd,dummy_start=es,
                M=M,anchor_factors=list(anchor_factors),Emax=Emax,Hc=Hc,
                T1=T1,T2=T2,bmin=bmin,b=b,L=cell,d=b*cell,
                copy_offsets=offsets,bare_shifts=list(bare),
                mu_bit_length=mu.bit_length(),mu_population=mu.bit_count(),
                clause_mass_bit_length=total_v.bit_length(),
                carry_bound_bit_length=(4*mass+8).bit_length(),
                native_support=len(support),field_targets=len(targets),mod5_unit=3)

def seam_checks(delta):
    checked=0
    for control in (0,1):
        tr=dict(delta)
        tr[93,0]=(0,0,215) if control==0 else (1,-1,2)
        tr[2,1]=(0,-1,3); tr[3,0]=(1,1,215)
        tape={}; head=state=0; history=[]
        for _ in range(10):
            history.append((dict(tape),head,state))
            if state==215: break
            write,move,state=tr[state,tape.get(head,0)]
            tape[head]=write; head+=move
        assert history[-1][2]==215
        lm=max(3,3-min(h for _,h,_ in history))
        rm=max(3,3+max(h for _,h,_ in history))
        for dw,dh in product(range(4),repeat=2):
            width=lm+rm+2+dw; height=len(history)+1+dh; xs=lm+1
            word=[None]*(width*height)
            for y in range(height):
                for x in range(width):
                    if x==0: code=V
                    elif y==0: code=H
                    elif y==1: code=L if x<xs else Q if x==xs else R
                    else:
                        tape,head,state=history[min(y-1,len(history)-1)]
                        pos=x-xs
                        code=tape.get(pos,0)+(2*(state+1) if pos==head else 0)
                    word[(-(x-xs)-width*(y-1))%len(word)]=code
            win=[(word[(i+1)%len(word)],word[i],word[(i-1)%len(word)],word[(i-width)%len(word)]) for i in range(len(word))]
            assert all(n in successors(l,c,r,tr) for l,c,r,n in win)
            assert win[0]==START and win.count(START)==1 and FORBIDDEN not in win
            checked+=len(win)
    return checked

def main():
    rows=json.loads(TRANSITIONS.read_text())['transitions']
    delta={(q,b):(w,d,nq) for q,b,w,d,nq in rows}
    delta.update({(215,b):(b,0,215) for b in (0,1)})
    assert len(rows)==430 and delta[0,0]==(1,1,93)
    windows=alphabet(delta)
    assert len(windows)==5252
    scalars=layout(windows)
    dest=HERE.parent/'data/strict_windows.json'
    dest.write_text(json.dumps(windows,separators=(',',':'))+'\n')
    result={'status':'PASS','schema':'k215-strict-four-cell-coefficients-v1',
            'scalars':scalars,
            'window_sha256':hashlib.sha256(dest.read_bytes()).hexdigest(),
            'toy_helical_windows':seam_checks(delta),
            'scope':'Finite alphabet, field targets, carry bounds, rotations and toy seams. Not a formal compiler proof.'}
    (HERE.parent/'data/strict_compiler_checks.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
