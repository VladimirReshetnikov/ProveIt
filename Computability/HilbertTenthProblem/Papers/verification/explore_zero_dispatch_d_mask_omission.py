#!/usr/bin/env python3
"""D-only false witness with every branch on a zero-valued fourth counter.

Fixed ROM rows and local identities are evaluated. The enormous duration is
handled by the companion proof, never represented as an enumerated history.
"""
from pathlib import Path
import json
import explore_rom_d_mask_omission as base
import explore_rom_d_mask_grid_hole as grid


def graph():
    signs=[1]*4 + [-1,1,-1,-1,1,1,1,1] + [-1,-1,-1,-1,1,1,1,1] \
          +[-1,-1,-1,-1,-1,1,1,1]+[-1,-1,-1,-1,1,-1,1,1]+[-1]*4
    zeros={1,2,3,11,16,18,19,27,35}
    edges=[(i,i+1) for i in range(39)]+[(11,4),(27,20),(27,36),(35,28),(39,0)]
    assert len(signs)==40 and all(v%4==(u+1)%4 for u,v in edges)
    outgoing={i:[v for u,v in edges if u==i] for i in range(40)}
    branches={i for i,v in outgoing.items() if len(v)>1}
    assert branches=={11,27,35} and branches<=zeros and all(i%4==3 for i in branches)
    return signs,zeros,edges,branches


def program():
    signs,zeros,edges,branches=graph();ell=4;states=40
    assert 3**ell>states
    offsets=[];sums=set();n=0
    while len(offsets)<states+2:
        added=[n+a for a in offsets]+[2*n]
        if len(set(added))==len(added) and not set(added)&sums:
            offsets.append(n);sums.update(added)
        n+=1
    shift=max(offsets)+1;coords=[ell*(shift+a) for a in offsets]
    order=sorted(zeros)+[i for i in range(states) if i not in zeros]
    a=[None]*states
    for i,c in zip(order,coords):a[i]=c
    bs,bz=coords[-2:];d=bz
    assert max(a[i] for i in zeros)<min(a[i] for i in range(states) if i not in zeros)
    pairs=[coords[i]+coords[j] for i in range(states+2) for j in range(i,states+2)]
    assert len(pairs)==len(set(pairs)) and 2*min(coords)>max(coords)
    positions=[d+a[v]-a[u] for u,v in edges]+[d-ai for ai in a]
    positions += [d+bs-a[i] for i in range(states) if signs[i]>0]
    positions += [d+bz-a[i] for i in range(states) if i not in zeros]
    assert min(positions)>=0 and len(set(positions))==len(positions) and all(p%ell==0 for p in positions)
    powers={}
    def pow3(p):
        if p not in powers:powers[p]=3**p
        return powers[p]
    K=sum(pow3(p) for p in positions);S=sum(pow3(p) for p in a)
    g=pow3(d);hs=pow3(d+bs);hz=pow3(d+bz)
    span=max(positions)+max(a)
    forbidden={p for p in range(span+1) if p%ell}|{d+bs,d+bz}
    # Exact geometric sum of every non-grid position, plus both grid ports.
    off_grid=(pow3(span+1)-1)//2-(pow3(ell*(span//ell+1))-1)//(3**ell-1)
    preliminary=off_grid+hs+hz
    extra_exp=span+8;extra=pow3(extra_exp)
    assert extra>max(K*S,g*S,6*(hs+hz),3*S,preliminary,81)
    forbidden.add(extra_exp);Zstar=preliminary+extra
    m=extra_exp+2;R=pow3(m)
    assert R>max(2*Zstar+1,K*S,g*S,81)
    c=d+a[12];s=d+bz-c;h=m-s
    assert 2<=h<=m-2 and c%ell==0 and c not in forbidden
    rows={}
    for state,nxt in edges:
        support={p+a[state] for p in positions}
        removed={d+a[nxt]}
        if signs[state]>0:removed.add(d+bs)
        if state not in zeros:removed.add(d+bz)
        assert removed<=support
        junk=support-removed
        assert junk and not junk&forbidden and max(junk)<m
        V=sum(pow3(p) for p in junk)
        assert V==K*pow3(a[state])-g*pow3(a[nxt])-hs*int(signs[state]>0)-hz*int(state not in zeros)
        assert V+Zstar<R and pow3(a[state])+(R-1)//2-S>0
        rows[state,nxt]=junk
    # The compensating row is deterministic and nozero-labelled. The
    # globally allowed destination belongs to a different truezero branch.
    assert 17 not in zeros and (17,12) not in edges
    assert c not in rows[17,18] and c in rows[11,4] and c not in rows[11,12]
    assert len([v for u,v in edges if u==17])==1
    assert not (rows[17,18]|{c})&forbidden
    pad_exp=c-a[17]
    assert pad_exp not in positions and pad_exp>=0
    assert hz*pow3(h)==pow3(c)*R
    return dict(signs=signs,zeros=zeros,edges=edges,branches=branches,a=a,
                ell=ell,span=span,forbidden=forbidden,m=m,R=R,h=h,c=c,s=s,
                hz_exp=d+bz,rows=rows,pad_exp=pad_exp)


def finite_paths(c):
    cases=0;branch_visits=0
    for x in range(1,17):
        for j in range(1,9):
            values=[2*x,0,0,0];declared_zeros=0;false_zeros=0
            sequence=list(range(4))+list(range(4,12))*j+list(range(12,20)) \
                     +list(range(20,28))*x+list(range(28,36))*j+list(range(36,40))
            for index,state in enumerate(sequence):
                lane=state%4
                if state in c['branches']:
                    assert lane==3 and values[lane]==0;branch_visits+=1
                if state in c['zeros']:
                    declared_zeros+=1
                    if values[lane]!=0:
                        assert state==16 and values[lane]==2*x;false_zeros+=1
                if state==16:assert values==[2*x,2*j,0,0]
                if state==17:assert values[1]==2*j
                values[lane]+=c['signs'][state]
                assert min(values)>=0
                nxt=sequence[index+1] if index+1<len(sequence) else 0
                assert (state,nxt) in c['edges']
            assert values==[0,0,0,0] and false_zeros==1
            assert declared_zeros==6+2*j+x
            assert len(sequence)==16+8*x+16*j
            cases+=1
    return cases,branch_visits


def actual_local(m,h):
    R=3**m;x=3**h;j=(3**(h-1)-1)//2
    assert 2<=h<=m-2
    rep=(R-3)//6;jr=(R-1)//2
    low=(R-x)//2;spill=j
    assert rep*x==low+R*spill
    assert jr+low+x==R+(x-1)//2
    assert R//3+spill+j+1==R//3+3**(h-1)<R
    assert 4*x<R and 2*x+1<R//3
    assert 8+8*j==4*x//3+4
    assert 16+8*x+16*j==32*x//3+8
    assert (16+8*x+16*j)%8==0
    assert (6+2*j+x+1)%2==0


def verify():
    c=program();m,h=c['m'],c['h'];actual_local(m,h)
    local=sum(grid.local(w,k) for w in range(4,33) for k in range(2,w-1))
    paths,visits=finite_paths(c);deltas=base.verify_source_deltas()
    return dict(status='PASS_ZERO_DISPATCH_D_ONLY_COUNTERFAMILY',states=40,edges=len(c['edges']),
                grid_spacing=c['ell'],marker_capacity=3**c['ell'],
                all_branches_on_truezero_fourth_counter=sorted(c['branches']),
                compensating_row=[17,18],compensating_row_is_deterministic_nozero=True,
                hole_required_by_other_zero_branch=[11,4],hole_absent_on_other_branch_edge=[11,12],
                all_fixed_ROM_rows_checked=len(c['rows']),dense_off_grid_span=c['span'],
                forbidden_positions_count=len(c['forbidden']),actual_width=m,
                nozero_target_exponent=c['hz_exp'],added_junk_position=c['c'],
                actual_input=f'3^{h}',actual_pump_iterations=f'(3^{h-1}-1)/2',
                actual_false_zero_row=f'4*3^{h-1}+4',actual_serial_blocks=f'32*3^{h-1}+8',
                local_interval_cases=local+1,finite_complete_paths=paths,
                verified_truezero_branch_visits=visits,exact_symbolic_deltas=deltas,
                retained_masks=11,even_index_and_positive_kernel_extension_proved=True,
                central_valuation=f'11*{m}*(32*3^{h-1}+8)',
                scope='Complete mathematical D-only false-witness family for the stated forty-state four-counter convolution graph. Every multi-successor state acts on a genuinely zero fourth counter in the constructed path; all nonzero-source states are deterministic. Fixed rows and finite/local controls are checked exactly. Exponentially long global packed/Pell integers are not materialized. No universal impossibility or smaller operation count is claimed.')


if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,indent=2))
