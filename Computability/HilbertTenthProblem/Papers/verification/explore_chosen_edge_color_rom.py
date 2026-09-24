#!/usr/bin/env python3
"""Chosen-edge color convolution: exact conditional row verifier and ledger.

The retained-flags local compatibility theorem is checked. A separate hole
shows why that theorem cannot silently type an unmasked nozero word.
No complete new universal certificate or full false history is claimed.
"""
from pathlib import Path
from collections import Counter
import json
import sympy as sp


def boolean(n):
    if n<0:return False
    while n:
        n,d=divmod(n,3)
        if d>1:return False
    return True


def program():
    # State phases are 0,1,2,1. A row chooses one of these five edges.
    edges=[(0,1),(0,3),(1,2),(3,2),(2,0)]
    phases=[0,1,2,1];signs=[1,1,-1,1];zeros=[1,0,0,0]
    assert all(phases[v]==(phases[u]+1)%3 for u,v in edges)
    ell=3;assert 3**ell>2*len(edges)
    offsets=[0,1,3,7,12]
    pairs=[x+y for i,x in enumerate(offsets) for y in offsets[i:]]
    assert len(pairs)==len(set(pairs))
    step=ell*(len(phases)+2)
    a=[step*(13+x) for x in offsets];d=max(a)
    colors=[{0,ell*(s+1)} for s in range(len(phases))]
    all_color=set(range(0,ell*(len(phases)+1),ell));color_max=max(all_color)
    assert step>color_max+ell
    bs=2*max(a)+color_max+ell;bz=bs+2*max(a)+ell
    out=[];inc=[]
    for i,(src,dst) in enumerate(edges):
        out.extend(d+c-a[i] for c in all_color-colors[dst])
        inc.extend(d+c-a[i] for c in colors[src])
        if signs[src]>0:out.append(d+bs-a[i])
        if not zeros[src]:out.append(d+bz-a[i])
    assert len(out)==len(set(out)) and len(inc)==len(set(inc))
    assert min(out+inc)>=0 and all(p%ell==0 for p in out+inc)
    Ko=sum(3**p for p in out);Ki=sum(3**p for p in inc)
    assert Ki%3==1
    S=sum(3**p for p in a);g=3**d;Jcode=sum(3**p for p in all_color)
    hs=3**(d+bs);hz=3**(d+bz);span=max(out+inc)+max(a)
    forbidden={p for p in range(span+1) if p%ell}
    forbidden.update(range(d,d+color_max+ell))
    forbidden.update((d+bs,d+bz))
    low_forbidden=sum(3**p for p in forbidden)
    bound=max((Ko+Ki)*S,g*Jcode,6*(hs+hz),3*S,low_forbidden,81)
    E=1;e=0
    while E<=bound:E*=3;e+=1
    assert e not in forbidden
    forbidden.add(e);Zstar=low_forbidden+E
    width_bound=max(2*Zstar+1,(Ko+Ki)*S,g*Jcode,81)
    R=1;m=0
    while R<=width_bound:R*=3;m+=1
    return dict(edges=edges,phases=phases,signs=signs,zeros=zeros,ell=ell,a=a,d=d,
                colors=colors,all_color=all_color,color_max=color_max,out=out,inc=inc,
                Ko=Ko,Ki=Ki,S=S,g=g,Jcode=Jcode,hs=hs,hz=hz,bs=bs,bz=bz,
                forbidden=forbidden,Zstar=Zstar,R=R,m=m)


def row(c,e,f):
    src,dst=c['edges'][e]
    raw=Counter(p+c['a'][e] for p in c['out'])
    raw.update(p+c['a'][f] for p in c['inc'])
    lhs=c['Ko']*3**c['a'][e]+c['Ki']*3**c['a'][f]
    V=lhs-c['g']*c['Jcode']-c['hs']*int(c['signs'][src]>0)-c['hz']*(1-c['zeros'][src])
    return raw,V


def verify_ledger():
    R,C,N,H,V,Kp,D,J,q=sp.symbols('R C N H V Kp D J q')
    Ko,Ki,I,G,hs,hz,g=sp.symbols('Ko Ki I G hs hz g')
    # G=g*Jcode and KiI=Ki*I are fixed numerals, computed at compilation.
    old=[('rk','*','R','Ko'),('coef','-','rk','g'),('lhs','*','coef','C'),
         ('sign','*','hs','Kp'),('zero','*','hz','D'),('out1','+','V','sign'),
         ('out2','+','out1','zero'),('rout','*','R','out2'),
         ('terminal','*','gI','J2'),('rhs','+','terminal','rout')]
    new=[('rk','*','R','Ko'),('coef','+','rk','Ki'),('body','*','coef','C'),
         ('terminal','*','KiI','J2'),('lhs','+','body','terminal'),
         ('color','*','G','H'),('sign','*','hs','Kp'),('zero','*','hz','D'),
         ('out1','+','V','color'),('out2','+','out1','sign'),('out3','+','out2','zero'),
         ('rhs','*','R','out3')]
    def run(rows):
        env=dict(R=R,C=C,H=H,V=V,Kp=Kp,D=D,J2=J,
                 Ko=Ko,Ki=Ki,g=g,G=G,hs=hs,hz=hz,gI=g*I,KiI=Ki*I)
        for name,op,left,right in rows:
            assert name not in env
            u,v=env[left],env[right]
            env[name]=u*v if op=='*' else u+v if op=='+' else u-v
        return env['lhs']-env['rhs']
    def count(rows):
        m=sum(r[1]=='*' for r in rows)
        return dict(total=len(rows),multiplications=m,additions=len(rows)-m)
    assert count(old)==dict(total=10,multiplications=6,additions=4)
    assert count(new)==dict(total=12,multiplications=7,additions=5)
    outputs=V+G*H+hs*Kp+hz*D
    local=Ko*C+Ki*N-outputs
    shift=C+I*(q-1)-R*N
    merged=(R*Ko+Ki)*C+Ki*I*J-R*outputs
    assert sp.expand(run(old)-((R*Ko-g)*C-g*I*J-R*(V+hs*Kp+hz*D)))==0
    assert sp.expand(run(new)-merged)==0
    geometry=q-J-1
    assert sp.expand(merged-(R*local+Ki*shift-Ki*I*geometry))==0
    return dict(old_cyclic_route=count(old),chosen_edge_route=count(new),
                delta=dict(multiplications=1,additions=1,total=2),
                exact_elimination_with_q_geometry=True,
                old_primitive_rows=old,new_primitive_rows=new)


def verify():
    c=program();rows={};accepted=0
    for e in range(len(c['edges'])):
        for f in range(len(c['edges'])):
            raw,V=row(c,e,f)
            compatible=c['edges'][e][1]==c['edges'][f][0]
            ok=V>0 and boolean(V) and boolean(V+c['Zstar']) and V+c['Zstar']<c['R']
            assert ok==compatible
            if compatible:
                assert e!=f
                support={p for p,n in raw.items() if n}
                for p in c['all_color']:assert raw[c['d']+p]==1
                for p in range(c['d'],c['d']+c['color_max']+c['ell']):
                    assert raw[p]==int(p-c['d'] in c['all_color'])
                assert max(raw.values())==1
                rows[e,f]=V;accepted+=1
    # Global safe forbidding cannot remove this Kin cross-junk column.
    e,f,u,v=2,4,1,0
    hole=c['d']+c['a'][u]-c['a'][v]
    assert (e,f) in rows and (4,u) in rows
    raw,V=row(c,e,f);legit_raw,legit_V=row(c,4,u)
    assert raw[hole]==0 and legit_raw[hole]==1
    assert V//3**hole%3==0 and legit_V//3**hole%3==1
    assert hole not in c['forbidden'] and hole%c['ell']==0
    changed=V+3**hole
    assert boolean(changed) and boolean(changed+c['Zstar']) and changed+c['Zstar']<c['R']
    hz_exp=c['d']+c['bz'];gap=hz_exp-hole;h=c['m']-gap
    assert gap>=2 and 2<=h<=c['m']-2
    x=3**h;j=(3**(h-1)-1)//2;rep=(c['R']-3)//6
    assert c['hz']*x==c['R']*3**hole and 4*x<c['R']
    low=(c['R']-3**h)//2
    spill=(3**(h-1)-1)//2
    assert rep*x==low+c['R']*spill
    carry,first=divmod((c['R']-1)//2+low+x,c['R'])
    second=c['R']//3+spill+j+carry
    assert carry==1 and first==(x-1)//2 and boolean(first)
    assert second==c['R']//3+3**(h-1)<c['R'] and boolean(second)
    D,Vv,hz,delta=sp.symbols('D V hz delta')
    assert sp.expand(Vv+hz*delta+hz*(D-delta)-(Vv+hz*D))==0
    # Cyclic shift is extracted by coprimality once R,q are powers of three.
    shift_cases=0;I=3**c['a'][0]
    for cycle in ((0,2,4),(1,3,4),(0,2,4,1,3,4)):
        R=c['R'];q=R**len(cycle)
        C=sum(3**c['a'][e]*R**j for j,e in enumerate(cycle))
        start=3**c['a'][cycle[0]]
        N=(C+start*(q-1))//R
        assert R*N==C+start*(q-1)
        assert N==sum(3**c['a'][e]*R**j for j,e in enumerate(cycle[1:]+cycle[:1]))
        assert 0<N<q and boolean(N);shift_cases+=1
    return dict(status='PASS_CONDITIONAL_CHOSEN_EDGE_ROWS_AND_FLAG_HOLE',
                graph_states=4,edge_symbols=len(c['edges']),grid_spacing=c['ell'],
                raw_coefficient_capacity=3**c['ell'],edge_coordinates=c['a'],
                exact_pair_cases=len(c['edges'])**2,compatible_pairs=accepted,
                cyclic_shift_cases=shift_cases,ledger=verify_ledger(),
                current_edge_pair=[e,f],globally_legitimate_pair=[4,u],
                incoming_lookup_edge=v,hole_exponent=hole,hole_on_grid=True,
                hole_outside_forbidden_color_block=True,actual_width=c['m'],
                pulse_exponent=h,paid_input_margin=True,local_guard_repair=True,
                scope='Exact conditional fixed-row compatibility and twelve-operation eliminated route. The additional on-grid hole defeats automatic nozero-flag typing at the ROM/two-row-guard interface. The flags were typed in the compatibility test. No complete enlarged outer certificate, full false accepting history, or improved universal operation count is asserted.')


if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,indent=2))
