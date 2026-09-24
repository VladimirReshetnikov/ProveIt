#!/usr/bin/env python3
"""D-only mask counterfamily using a necessary, on-grid alternative-edge hole.

The enormous complete path is proved in the companion note rather than
materialized. This regression checks every fixed ROM row, actual-width local
carry identities, finite cycle controls, and exact perturbation identities.
"""
from pathlib import Path
import json

import explore_rom_d_mask_omission as base


def program():
    offsets=[];sums=set();n=0
    while len(offsets)<32:
        added=[n+a for a in offsets]+[2*n]
        if len(set(added))==len(added) and not set(added)&sums:
            offsets.append(n);sums.update(added)
        n+=1
    ell=4
    assert 3**ell>30
    shift=max(offsets)+1;coords=[ell*(shift+a) for a in offsets]
    order=[1,2,12]+[i for i in range(30) if i not in (1,2,12)]
    a=[None]*30
    for coord,state in zip(coords,order):a[state]=coord
    assert 3**ell>len(a)
    bs,bz=coords[30:];d=max(coords)
    assert max(a[i] for i in (1,2,12))<min(a[i] for i in range(30) if i not in (1,2,12))
    pairs=[coords[i]+coords[j] for i in range(32) for j in range(i,32)]
    assert len(pairs)==len(set(pairs)) and 2*min(coords)>max(coords)
    signs=[1,1,1,-1,-1,-1]+[1,1,1,-1,1,-1]+[1,1,1,-1,-1,-1] \
         +[-1,1,1,-1,-1,-1]+[1,-1,1,-1,-1,-1]
    zeros=[int(i in (1,2,12)) for i in range(30)]
    edges=[(i,i+1) for i in range(29)]+[(5,12),(11,6),(23,18),(23,0),(29,24),(29,0),(13,17)]
    assert all(v%3==(u+1)%3 for u,v in edges)
    positions=[d+a[v]-a[u] for u,v in edges]+[d-ai for ai in a]
    positions += [d+bs-a[i] for i in range(30) if signs[i]>0]
    positions += [d+bz-a[i] for i in range(30) if not zeros[i]]
    assert len(positions)==len(set(positions)) and min(positions)>=0
    assert all(p%ell==0 for p in positions)
    K=sum(3**p for p in positions);S=sum(3**p for p in a)
    g=3**d;hs=3**(d+bs);hz=3**(d+bz)
    span=max(positions)+max(a)
    forbidden={p for p in range(span+1) if p%ell}
    forbidden.update((d+bs,d+bz))
    preliminary=sum(3**p for p in forbidden)
    threshold=max(K*S,g*S,6*(hs+hz),3*S,preliminary,81)
    extra=1;e=0
    while extra<=threshold:extra*=3;e+=1
    assert e not in forbidden
    forbidden.add(e);Zstar=preliminary+extra
    width_bound=max(2*Zstar+1,K*S,g*S,81)
    R=1;m=0
    while R<=width_bound:R*=3;m+=1
    hole=d+a[14];s=d+bz-hole;h=m-s
    assert hole%ell==0 and hole not in forbidden and 2<=h<=m-2
    assert bz>a[14] and s%ell==0
    rows={}
    for state,nxt in edges:
        support={p+a[state] for p in positions}
        removed={d+a[nxt]}
        if signs[state]>0:removed.add(d+bs)
        if not zeros[state]:removed.add(d+bz)
        assert removed<=support
        junk=support-removed
        assert not junk&forbidden and all(p%ell==0 for p in junk) and max(junk)<m
        V=sum(3**p for p in junk)
        assert V==K*3**a[state]-g*3**a[nxt]-hs*int(signs[state]>0)-hz*(1-zeros[state])
        assert V>0 and V+Zstar<R and 3**a[state]+(R-1)//2-S>0
        rows[state,nxt]=junk
    assert hole not in rows[13,14] and hole in rows[13,17]
    assert rows[13,14]|{hole}==rows[13,17]|{d+a[17]}
    assert not (rows[13,14]|{hole})&forbidden
    # This missing digit cannot be safely forbidden: the genuine alternative
    # edge needs it as junk. Raising the relevant K coefficient to two also
    # gives that genuine alternative a forbidden Boolean-alphabet digit two.
    pad_exponent=hole-a[13]
    assert pad_exponent in positions
    alternative_v=sum(3**p for p in rows[13,17])
    assert (alternative_v+3**hole)//3**hole%3==2
    assert hz*3**h==3**hole*R
    return dict(a=a,bs=bs,bz=bz,d=d,signs=signs,zeros=zeros,edges=edges,
                rows=rows,positions=positions,K=K,S=S,g=g,hs=hs,hz=hz,
                Zstar=Zstar,forbidden=forbidden,span=span,R=R,m=m,h=h,s=s,
                hole=hole,extra_forbidden=e,ell=ell)


def local(m,h):
    R=3**m;rep=(R-3)//6;jr=(R-1)//2
    assert 2<=h<=m-2
    x=3**h;j=(3**(h-1)-1)//2;a_next=j
    spill,low=divmod(rep*x,R)
    assert low==sum(3**i for i in range(h,m))
    assert spill==sum(3**i for i in range(h-1))
    carry,first=divmod(jr+low+x,R)
    assert carry==1 and first==(x-1)//2
    second=R//3+spill+a_next+carry
    assert second==R//3+3**(h-1)<R
    assert base.digits(first)==set(range(h))
    assert base.digits(second)=={m-1,h-1}
    assert base.digits(1+x)=={0,h}
    assert (R-x)//3**h%3==2
    assert 4*x<R and 2*x+1<R//3 and 2*j+1<R//3
    return 1


def verify():
    c=program();m=c['m'];h=c['h'];R=c['R'];x=3**h;j=(3**(h-1)-1)//2
    assert 6+6*j==x+3 and 12+6*x+12*j==8*x+6
    assert (8*x+6)%6==0
    actual=local(m,h)
    finite=sum(local(w,k) for w in range(4,41) for k in range(2,w-1))
    cycles=base.verify_cycles(c);deltas=base.verify_source_deltas()
    return dict(status='PASS_D_ONLY_NECESSARY_GRID_HOLE_COUNTERFAMILY',
                program_states=30,program_edges=len(c['edges']),
                grid_spacing=c['ell'],marker_capacity=3**c['ell'],
                all_fixed_ROM_rows_checked=len(c['rows']),zero_coordinates_strictly_below_nozero=True,
                all_off_grid_positions_forbidden_through=c['span'],forbidden_positions_count=len(c['forbidden']),
                actual_width=m,nozero_target_exponent=c['d']+c['bz'],
                added_junk_position=c['hole'],position_modulo_grid=c['hole']%c['ell'],
                selected_row=[13,14],genuine_alternative_row=[13,17],
                forbidden_addition_breaks_genuine_alternative=True,
                coefficient_two_padding_breaks_genuine_alternative=True,
                actual_input=f'3^{h}',actual_pump_iterations=f'(3^{h-1}-1)/2',
                actual_false_zero_row=f'3^{h}+3',actual_serial_blocks=f'8*3^{h}+6',
                local_interval_cases=actual+finite,finite_cycle_cases=cycles,exact_symbolic_deltas=deltas,
                retained_masks=11,central_valuation=f'11*{m}*(8*3^{h}+6)',
                even_index_and_positive_kernel_extension_proved=True,
                scope='The written proof gives a complete positive false-witness family for this fixed thirty-state graph and ordered, densely off-grid-forbidden ROM. Every fixed ROM row and actual-width local carry identity is checked exactly. The exponentially long complete history and gigantic packed/Pell integers are NOT materialized. This refutes D-only omission for the stated convolution architecture with this graph, not every possible new machine/compiler or encoding.')


if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,indent=2))
