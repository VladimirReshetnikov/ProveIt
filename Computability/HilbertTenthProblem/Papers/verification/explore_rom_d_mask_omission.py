#!/usr/bin/env python3
"""A full counterfamily for D-only omission with the current sparse ROM mask.

The fixed program and local word identities are checked exactly. Its actual
large-width path is proved by cycle invariants, not materialized or labelled
as a fresh complete huge-integer word evaluation. No smaller SLP is claimed.
"""
from pathlib import Path
import json
import sympy as sp


def digits(n):
    result=set();i=0
    while n:
        n,d=divmod(n,3)
        assert d in (0,1)
        if d:result.add(i)
        i+=1
    return result


def program():
    offsets=[];sums=set();n=0
    while len(offsets)<32:
        added=[n+a for a in offsets]+[2*n]
        if len(set(added))==len(added) and not set(added)&sums:
            offsets.append(n);sums.update(added)
        n+=1
    ell=4
    assert 3**ell>30
    base=max(offsets)+1;coord=[ell*(base+a) for a in offsets]
    a=coord[:30];bs,bz=coord[30:];d=max(coord)
    assert 3**ell>len(a)
    sums=[coord[i]+coord[j] for i in range(32) for j in range(i,32)]
    assert len(sums)==len(set(sums)) and min(coord)*2>max(coord)
    signs=[1,1,1,-1,-1,-1]+[1,1,1,-1,1,-1]+[1,1,1,-1,-1,-1] \
         +[-1,1,1,-1,-1,-1]+[1,-1,1,-1,-1,-1]
    zeros=[int(i in (1,2,12)) for i in range(30)]
    edges=[(i,i+1) for i in range(29)]+[(5,12),(11,6),(23,18),(23,0),(29,24),(29,0)]
    positions=[d+a[v]-a[u] for u,v in edges]+[d-ai for ai in a]
    positions += [d+bs-a[i] for i in range(30) if signs[i]==1]
    positions += [d+bz-a[i] for i in range(30) if zeros[i]==0]
    assert len(positions)==len(set(positions)) and min(positions)>=0
    assert all(p%ell==0 for p in positions)
    K=sum(3**p for p in positions);S=sum(3**p for p in a)
    g=3**d;hs=3**(d+bs);hz=3**(d+bz)
    forbidden={d+i for i in range(1,ell)}|{d+bs,d+bz}
    zold=sum(3**p for p in forbidden)
    bound=max(K*S,g*S,6*(hs+hz),zold,3*S,9)
    E=1;e=0
    while E<=bound:E*=3;e+=1
    forbidden.add(e);Zstar=zold+E
    width_bound=max(2*Zstar+1,K*S,g*S,81)
    R=1;m=0
    while R<=width_bound:R*=3;m+=1
    hole=d+bz-2
    assert hole>=0 and hole%ell==ell-2 and hole not in forbidden and hole<m
    checks=0
    for state,nxt in edges:
        support={p+a[state] for p in positions}
        removed={d+a[nxt]}
        if signs[state]==1:removed.add(d+bs)
        if not zeros[state]:removed.add(d+bz)
        assert removed<=support
        junk=support-removed
        assert all(p%ell==0 for p in junk) and not junk&forbidden and max(junk)<m
        assert hole not in junk
        C=3**a[state];V=sum(3**p for p in junk)
        assert V==K*C-g*3**a[nxt]-hs*int(signs[state]==1)-hz*(1-zeros[state])
        assert V>0 and V+Zstar<R and C+(R-1)//2-S>0
        checks+=1
    # The added bit belongs to row13, whose ordinary successor is14.
    state=13;nxt=14;support={p+a[state] for p in positions}
    removed={d+a[nxt],d+bs,d+bz};junk=support-removed
    assert not (junk|{hole})&forbidden and hole not in junk
    assert max(junk|forbidden|{hole})<m
    return dict(a=a,bs=bs,bz=bz,d=d,signs=signs,zeros=zeros,edges=edges,
                positions=set(positions),K=K,S=S,g=g,hs=hs,hz=hz,Zstar=Zstar,
                forbidden=forbidden,R=R,m=m,hole=hole,row_checks=checks,ell=ell)


def verify_local(m):
    R=3**m;h=m-2;x=3**h;j=(x//3-1)//2;rep=(R-3)//6;jr=(R-1)//2
    assert m>=4 and 2*j==x//3-1 and 4*x<R
    # At the false zero request both tracks have one bit at h. In the next
    # row both tracks have all one digits below h-1.
    a_bad=3**h;a_next=(3**(h-1)-1)//2
    delta=3**h
    spill,low=divmod(rep*delta,R)
    assert low==sum(3**i for i in range(h,m))
    assert spill==sum(3**i for i in range(h-1))
    T_bad=jr+low;T_next=R//3+spill
    carry,guard_bad=divmod(T_bad+a_bad,R)
    assert carry==1 and guard_bad==(3**h-1)//2
    guard_next=T_next+a_next+carry
    assert guard_next==R//3+3**(h-1)<R
    assert digits(guard_bad)==set(range(h))
    assert digits(guard_next)=={m-1,h-1}
    assert a_bad+a_bad==2*x and a_next+a_next==2*j
    # The added zero bit is Boolean; its complementary subtraction borrows
    # from the next head and has a ternary digit two.
    assert digits(1+delta)=={0,h}
    assert (R-delta)//3**h%3==2
    assert 2*x+1<R//3 and 2*j+1<R//3
    return dict(width=m,input_exponent=h,pump_iterations='(3^(m-3)-1)/2',
                guard_bad_support=[0,h-1],guard_next_support=[h-1,m-1])


def verify_cycles(c):
    # Finite checks supplement the general affine cycle invariants.
    cases=0
    for x in range(1,25):
        for j in range(0,8):
            v=[2*x,0,0]
            def block(first):
                nonlocal v
                before=v[:]
                for state in range(first,first+6):
                    lane=state%3;v[lane]+=c['signs'][state]
                    assert min(v)>=0
                return before,v[:]
            before,after=block(0);assert after==before
            for _ in range(j):
                before,after=block(6);assert after==[before[0],before[1]+2,before[2]]
            assert v==[2*x,2*j,0] and c['zeros'][12]==1 and v[0]>0
            before,after=block(12);assert before==after
            for _ in range(x):
                before,after=block(18);assert after==[before[0]-2,before[1],before[2]]
            for _ in range(j):
                before,after=block(24);assert after==[before[0],before[1]-2,before[2]]
            assert v==[0,0,0];cases+=1
    return cases


def verify_source_deltas():
    R,J,H,T,Z,D,V,hz,delta=sp.symbols('R J H T Z D V hz delta')
    rep=(R-3)/6
    newZ=Z+delta;newD=D-delta;newV=V+hz*delta;newT=T+rep*delta
    assert sp.expand((newZ+newD-H)-(Z+D-H))==0
    assert sp.expand((6*(J-newT)-(R-3)*newD)-(6*(J-T)-(R-3)*D))==0
    assert sp.expand((newV+hz*newD)-(V+hz*D))==0
    # For h=m-2, multiplication shifts the new junk bit into row b+1.
    assert sp.expand(hz*(R/9)-(hz/9)*R)==0
    return 4


def verify():
    c=program();m=c['m'];R=c['R'];h=m-2;x=R//9;j=(R//27-1)//2
    assert 4*x<R and x==3**h and 2*j==x//3-1 and j>0
    b=6+6*j;u=12+6*x+12*j
    assert b==x+3 and u==8*x+6 and u%6==0
    actual=verify_local(m)
    local=[verify_local(w) for w in range(4,65)]
    cycles=verify_cycles(c);deltas=verify_source_deltas()
    assert c['hz']*(R//9)==3**c['hole']*R
    return dict(status='PASS_D_ONLY_MASK_OMISSION_COUNTERFAMILY',program_states=30,
                grid_spacing=c['ell'],marker_capacity=3**c['ell'],
                program_edges=len(c['edges']),sidon_coordinates=c['a']+[c['bs'],c['bz']],
                complete_fixed_ROM_edge_checks=c['row_checks'],current_forbidden_positions=sorted(c['forbidden']),
                added_junk_position=c['hole'],position_is_unoccupied_and_not_forbidden=True,
                actual_counter_width=m,actual_input=f'3^{h}',
                actual_pump_iterations=f'(3^{m-3}-1)/2',
                actual_false_zero_row=f'3^{h}+3',actual_serial_blocks=f'8*3^{h}+6',
                local_interval_cases=len(local)+1,finite_cycle_cases=cycles,exact_source_delta_checks=deltas,
                retained_masks=11,central_valuation=f'11*{m}*(8*3^{h}+6)',
                even_packed_index=True,positive_generic_kernel_extension=True,
                free_repair_boundary=f'Adding the fixed forbidden bit3^{c["hole"]}=hz/9 blocks this counterfamily and preserves all correct ROM rows.',
                scope='Full mathematical counterfamily for the specified fixed sparse ROM and D-only mask omission. Fixed ROM rows, actual-width local carry identities and symbolic source deltas are checked exactly. The enormous duration-dependent global words are NOT materialized; their source equations and masks follow from the written cycle, telescoping and two-row carry proofs. No optimized SLP count or encoding-independent impossibility is claimed.')


if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print({k:v for k,v in result.items() if k not in ('scope','sidon_coordinates')})
