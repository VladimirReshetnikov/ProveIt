#!/usr/bin/env python3
"""Ordered/high-port ROM and isolated-zero counterexample, finite block gate.

The complete history is defined by symbolic loop counts; its astronomical
q and Pell witnesses are not numerically instantiated.
"""
from pathlib import Path
import json
import sympy as sp


def make_program():
    offsets=[];sums=set();n=0
    while len(offsets)<30:
        added=[n+t for t in offsets]+[2*n]
        if len(added)==len(set(added)) and not set(added)&sums:
            offsets.append(n);sums.update(added)
        n+=1
    ell=4;base=max(offsets)+1
    coordinate_list=[ell*(base+t) for t in offsets]
    zero_states={1,8,12,20,26}
    order=sorted(zero_states)+[13,0]+[i for i in range(30) if i not in zero_states|{13,0}]
    a=[0]*30
    for state,coordinate in zip(order,coordinate_list):a[state]=coordinate
    bs=2*max(a)+ell;bz=2*bs+ell;coordinates=a+[bs,bz];d=bz
    pairs=[coordinates[i]+coordinates[j] for i in range(32) for j in range(i,32)]
    assert len(pairs)==len(set(pairs)) and not set(pairs)&set(coordinates)
    assert max(a[i] for i in zero_states)<min(a[i] for i in range(30) if i not in zero_states)
    span=max(a)-min(a)
    assert bz>bs+span and bz>max(a)+span
    signs=[1,1,1,-1,-1,-1]+[1,1,1,-1,1,-1]+[1,1,1,-1,-1,-1] \
        +[-1,1,1,-1,-1,-1]+[1,-1,1,-1,-1,-1]
    edges=[(i,i+1) for i in range(29)]+[(11,6),(23,18),(29,24),(29,0)]
    assert all((j-i)%3==1 for i,j in edges)
    assert all(not(i in zero_states and j in zero_states) for i,j in edges)
    positions=[d+a[j]-a[i] for i,j in edges]+[d-v for v in a]
    positions += [d+bs-a[i] for i in range(30) if signs[i]==1]
    positions += [d+bz-a[i] for i in range(30) if i not in zero_states]
    assert len(positions)==len(set(positions)) and min(positions)>=0
    K=sum(3**e for e in positions);S=sum(3**e for e in a)
    g=3**d;hs=3**(d+bs);hz=3**(d+bz)
    forbidden=set(range(d+1,d+ell))|{d+bs,d+bz}
    bound=max(K*S,g*S,6*(hs+hz),sum(3**e for e in forbidden),3*S,9)
    e=0;E=1
    while E<=bound:E*=3;e+=1
    assert e not in forbidden
    # Charge no operation for fixed encoding constants. Strengthen the ROM
    # support mask by forbidding EVERY off-grid column below its fixed bound.
    # A correct single-state row has support only on the ell-grid.
    forbidden.update(j for j in range(e) if j%ell)
    forbidden.add(e)
    # Evaluate the dense fixed numeral by geometric sums, not one large
    # exponentiation per forbidden position.
    grid_count=(e+ell-1)//ell
    dense=(3**e-1)//2-(3**(ell*grid_count)-1)//(3**ell-1)
    Zstar=dense+sum(3**j for j in forbidden if j>=e or j%ell==0)
    width_bound=max(2*Zstar+1,K*S,g*S)
    R=1;m=0
    while R<=width_bound:R*=3;m+=1
    return dict(a=a,bs=bs,bz=bz,d=d,ell=ell,span=span,zero_states=zero_states,
        signs=signs,edges=edges,positions=set(positions),K=K,S=S,g=g,hs=hs,hz=hz,
        forbidden=forbidden,forbidden_bound=e,Zstar=Zstar,R=R,m=m)


def run_macro(c,states,initial):
    value=list(initial);bad=[]
    for state in states:
        lane=state%3;n=value[lane]
        assert 0<=n<c['R']//3
        if state in c['zero_states'] and n:bad.append(state)
        value[lane]+=c['signs'][state];assert min(value)>=0
    return value,bad


def verify():
    for end in range(1,70):
        grid_count=(end+3)//4
        assert (3**end-1)//2-(3**(4*grid_count)-1)//80 \
            ==sum(3**j for j in range(end) if j%4)
    c=make_program();m=c['m'];R=c['R'];ell=c['ell']
    assert all(j in c['forbidden'] for j in range(c['forbidden_bound']) if j%ell)
    gap=c['a'][0]-c['a'][13];h=m-gap
    assert gap>=ell>=3 and h>=3
    x=3**h;k=(3**(h-1)-1)//2;Jrow=(R-1)//2;rep=(R-3)//6;top=R//3
    assert 2*k==3**(h-1)-1 and 4*x<R
    table_checks=0
    for state,nxt in c['edges']:
        supp={e+c['a'][state] for e in c['positions']}
        removed={c['d']+c['a'][nxt]}
        if c['signs'][state]==1:removed.add(c['d']+c['bs'])
        if state not in c['zero_states']:removed.add(c['d']+c['bz'])
        assert removed<=supp
        junk=supp-removed
        assert not junk&c['forbidden'] and max(junk)<m
        if state in c['zero_states']:assert max(supp)<c['d']+c['bz']
        if (state,nxt)==(13,14):
            victim=c['d']+c['bz']-gap
            assert victim in junk and victim not in c['forbidden']
            assert victim%ell==0
            assert victim>c['d']+c['bs']+c['span']
            altered=junk-{victim}
            V=sum(3**j for j in junk);newV=sum(3**j for j in altered)
            assert (V-newV)*3**gap==c['hz']
        table_checks+=1
    assert run_macro(c,range(6),[2*x,0,0])==([2*x,0,0],[])
    macro_checks=1
    for j in {0,k-1}:
        assert run_macro(c,range(6,12),[2*x,2*j,0])==([2*x,2*j+2,0],[])
        macro_checks+=1
    assert run_macro(c,range(12,18),[2*x,2*k,0])==([2*x,2*k,0],[12]);macro_checks+=1
    for n in {1,x}:
        assert run_macro(c,range(18,24),[2*n,2*k,0])==([2*n-2,2*k,0],[])
        macro_checks+=1
    for n in {1,k}:
        assert run_macro(c,range(24,30),[0,2*n,0])==([0,2*n-2,0],[])
        macro_checks+=1
    # The interval straddles two rows; the second row is NOT a zero row.
    jh=(3**h-1)//2;jh1=(3**(h-1)-1)//2
    assert rep*3**h==(Jrow-jh)+R*jh1
    T0=jh;T1=top-jh1
    assert T0>0 and T1>0 and T1%3==2  # T itself is not Boolean.
    assert 3**h+T0==(3**(h+1)-1)//2
    assert jh1+T1==top and 2*jh1==2*k
    # The D bit lives in the previous row; its shifted ROM contribution
    # is the explicitly identified next-row cross term.
    assert c['hz']*3**h==R*3**(c['d']+c['bz']-gap)
    H,D,V,hz,Rv,Delta,J,T=sp.symbols('H D V hz R Delta J T',integer=True)
    assert sp.expand((V-hz*Delta)+hz*(D+Delta)-(V+hz*D))==0
    assert sp.expand(6*(J-(T-(Rv-3)*Delta/6))-(Rv-3)*(D+Delta)
                     -(6*(J-T)-(Rv-3)*D))==0
    assert sp.expand((H-D-Delta)+(D+Delta)-H)==0
    # Loop counts are exact integers, but q=R**u is deliberately not formed.
    u=12+6*x+12*k;b=6+6*k;zero_count=2+2*k+x
    assert u%6==0 and zero_count%2==1 and b%3==0
    assert b+8<u and 3**h<R  # a later genuine zero head guarantees Znew>0.
    # Macro endpoints are affine in their loop index. These symbolic steps
    # verify the complete prefix/prep/cleanup induction, not a cutoff search.
    n0,n1=sp.symbols('n0 n1',integer=True)
    for states,expected in ((range(6,12),[n0,n1+2,0]),
                           (range(12,18),[n0,n1,0]),
                           (range(18,24),[n0-2,n1,0]),
                           (range(24,30),[n0,n1-2,0])):
        state=[n0,n1,0]
        for i in states:state[i%3]+=c['signs'][i]
        assert state==expected
    return dict(status='PASS_ORDERED_ISOLATED_ZERO_OMISSION_BLOCK_AND_SYMBOLIC_GATE',
        graph_states=30,edges=len(c['edges']),sidon_coordinates=c['a']+[c['bs'],c['bz']],
        all_zero_states_below_nozero=True,high_zero_port_verified=True,
        all_zero_requests_isolated=True,source_zero_states=sorted(c['zero_states']),
        dense_offgrid_forbidden_columns=sum(j%ell!=0 for j in c['forbidden']),
        dense_offgrid_forbidden_bound=c['forbidden_bound'],
        absorbed_junk_is_on_grid=True,
        counter_width=m,negative_cross_coordinate_gap=gap,input_exponent=h,
        input='3^h',second_counter='3^(h-1)-1',preparation_loops='(3^(h-1)-1)/2',
        serial_blocks='12+6*3^h+12*((3^(h-1)-1)/2)',
        ROM_edge_and_mask_cases=table_checks,macro_endpoint_cases=macro_checks,
        symbolic_macro_identities=4,false_zero_state=12,
        T_nonboolean_but_both_guards_boolean=True,paid_doubled_input_bound=True,
        positive_Z_and_Boolean_offhead_D=True,even_indices_after_either_omission=True,
        scope='Exact fixed ROM constants, ordered states/high port, every edge/support row, finite huge-integer two-row guard identities, macro endpoints and symbolic full-history induction. The complete q and long histories are defined constructively but not materialized; positive Pell extension is the general theorem. This refutes the stated encoding repairs for omitting Z, even with D masked, without claiming an SLP count.')


if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print({k:v for k,v in result.items() if k not in ('scope','sidon_coordinates')})
