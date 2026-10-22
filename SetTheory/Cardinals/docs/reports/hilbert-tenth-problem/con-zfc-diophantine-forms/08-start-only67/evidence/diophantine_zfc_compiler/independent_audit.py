#!/usr/bin/env python3
"""Independent finite audits; never enumerate the full window alphabet.

Imports only the newly authored explicit constants module, not upstream code.
The general proof is in INDEPENDENT_AUDIT.md; tests alone do not prove it.
"""
from itertools import product
from random import Random
import json
import explicit_constants as ec


def check_fold_prefixes():
    rng=Random(215435)
    saved=ec.TM.copy()
    steps=0
    try:
        for trial in range(100):
            for q,s in product(range(215), range(2)):
                ec.TM[q,s]=(rng.randrange(2),rng.choice([-1,1]),rng.randrange(215))
            logical={}; physical={0:6}; q=0; x=0; fq=4; fx=0
            for _ in range(100):
                bit=logical.get(x,0)
                w,m,nq=ec.TM[q,bit]
                logical[x]=w; x+=m; q=nq
                fw,fm,fq=ec.delta(fq,physical.get(fx,0))
                physical[fx]=fw; fx+=fm
                assert fx<=0
                rq,track=divmod(fq-4,2)
                assert q==rq and x==(-fx if track==0 else fx-1)
                for p in range(0,min(physical)-1,-1):
                    pair,flag=ec.SYMBOL_TO_PAIR[physical.get(p,0)]
                    assert flag==(p==0)
                    assert pair==(logical.get(-p,0),logical.get(p-1,0))
                steps+=1
    finally:
        ec.TM.clear();ec.TM.update(saved)
    return steps


def check_helices():
    saved=ec.TM.copy(); rng=Random(4354366); examples=[]
    forbidden=(ec.tile(0,ec.Q0),)*9
    assert forbidden==(7,)*9 and ec.allowed_window(forbidden)
    try:
        for moves in [(-1,), (1,),(-1,1), (1,-1),(-1,-1,1,1),
                      tuple([-1]*12+[1]*24+[-1]*12),
                      tuple(rng.choice([-1,1]) for _ in range(60))]:
            for q,m in enumerate(moves):
                for s in range(2):ec.TM[q,s]=(q%2,m,215 if q==len(moves)-1 else q+1)
            for u in (2,3,5):
                tape={x:1 for x in range(-u,1)};head=0;q=ec.Q0
                rows=[(tape.copy(),head,q)]
                while q!=ec.HALT:
                    w,m,q=ec.delta(q,tape.get(head,0));tape[head]=w;head+=m
                    rows.append((tape.copy(),head,q))
                    assert len(rows)<200
                leftmost=min(min(t) for t,_,_ in rows)
                width=ec.next_power_of_five(max(u+6,4-leftmost))
                margin=width-u-4
                height=ec.next_power_of_five(max(25,len(rows)+2))
                xq=width-3;xs=xq-1
                G=[[ec.V]+[ec.H]*(width-1),
                   [ec.V]+[ec.LEFT]*margin+[ec.INPUT]*u+[ec.START_HEAD]+[ec.RIGHT]*2]
                for y in range(2,height):
                    t,h,st=rows[min(y-1,len(rows)-1)]
                    G.append([ec.V]+[ec.tile(t.get(x-xq,0),st if x-xq==h else None)
                                          for x in range(1,width)])
                def cell(x,y):return G[(y+x//width)%height][x%width]
                def window(x,y):return tuple(cell(x+dx,y+dy) for dy in (-1,0,1) for dx in (-1,0,1))
                N=width*height
                cyclic={(-(x-xs)-width*(y-1))%N:window(x,y)
                        for x,y in product(range(width),range(height))}
                assert len(cyclic)==N
                assert all(ec.allowed_window(w) for w in cyclic.values())
                assert cyclic[0]==ec.START_WINDOW and cyclic[u-1]==ec.END_WINDOW
                assert sum(w==ec.START_WINDOW for w in cyclic.values())==1
                assert sum(w==ec.END_WINDOW for w in cyclic.values())==1
                assert forbidden not in cyclic.values()
                for i in range(N):
                    c,r,n=cyclic[i],cyclic[(i-1)%N],cyclic[(i-width)%N]
                    assert all(c[3*rr+cc+1]==r[3*rr+cc] for rr in range(3) for cc in range(2))
                    assert all(c[3*(rr+1)+cc]==n[3*rr+cc] for rr in range(2) for cc in range(3))
                examples.append(dict(u=u,width=width,height=height,period=N,original_steps=len(moves)))
    finally:
        ec.TM.clear();ec.TM.update(saved)
    return examples


def check_layouts():
    rng=Random(751574366);cases=[]
    for a,k in ((2,2),(2,3),(2,17),(2,100),(2,511),(3,2),(3,173),(4,4),(4,260),(5,19)):
        windows=[];seen=set()
        while len(windows)<k:
            w=tuple(rng.randrange(a) for _ in range(9))
            if w not in seen:seen.add(w);windows.append(w)
        p=ec.compiler_layout(windows,a);E=set(p['native']);e0=p['dummy'][0]
        # Independently derive the clause population and native support count.
        ell=p['A'].bit_length()-1
        assert p['m']==2*(ell-1+9*a+4+p['padding'])+12*a+2
        assert len(E)==p['m']+1
        assert sum(c.bit_count() for c in p['MF'].values())==p['m']+1
        assert min(E)==0 and 1 in E
        assert all(e==0 or e>2 for e in p['MF'])
        assert p['MF'][0]==4
        assert p['mass']+1<=2**p['b']//4-1
        assert 2**p['b']//4+1<=2**p['b']-2
        # Anchor difference uniqueness and disjoint synchronized field targets.
        u1,u2,v1,v2=p['anchors']
        assert [(x,y) for x in E for y in E if y-x==18*p['M0']]==[(v1,v2)]
        assert e0+1<max(E)
        assert p['T2']-p['T1']>2*max(E)
        assert p['L']-(p['T2']-p['T1'])>max(E)
        # Every native basis bit and all original tests, derived independently.
        tests=[(p['T1'],lambda site,e:p['coefficients'].get(e,0) if site==0 else 0),
               (p['T2'],lambda site,e:p['coefficients'].get(e,0) if site==0 else 0)]
        for r,c,s in product(range(2),range(3),range(a)):
            dst=p['payload'][r,c,s];src=p['payload'][r+1,c,s]
            tests.append((dst,lambda site,e,dst=dst,src=src:int((site==0 and e==src) or (site==2 and e==dst))))
        for r,c,s in product(range(3),range(2),range(a)):
            rdst=p['payload'][r,c,s];csrc=p['payload'][r,c+1,s];dst=p['H']+rdst
            tests.append((dst,lambda site,e,rdst=rdst,csrc=csrc:int((site==0 and e==csrc) or (site==1 and e==rdst))))
        for src,dst in ((u1,v1),(u2,v2)):
            tests.append((dst,lambda site,e,src=src,dst=dst:int((site==0 and e==src) or (site==2 and e==dst))))
        count=0
        for dst,expected in tests:
            for site,e in product(range(3),E):
                got=p['DC'].get(dst-e,0) if site==0 else int(dst-e==p['H']) if site==1 else int(dst==e)
                assert got==expected(site,e)
                count+=1
        cases.append(dict(a=a,k=k,padding=p['padding'],dummy_count=len(p['dummy']),epsilon=p['epsilon'],basis_checks=count))
    return cases

if __name__=='__main__':
    result={'fold_prefix_steps':check_fold_prefixes(),'helices':check_helices(),'layouts':check_layouts(),
            'full_window_enumeration':False,'upstream_python_executed':False}
    print(json.dumps(result,indent=2))
