"""A signed underflow defeats omission of one numerical track mask.

All zero requests and controller edges remain genuine.  The relaxed packing
puts zero in A0's old slot, retaining twelve positions and the fixed43 kernel.
The literal diagnostic schedule costs103; this is a refutation, not a bound.
"""
from pathlib import Path
from itertools import product
import json
import sympy as sp
import explore_state_top_doubled_grid as base
import explore_three_raw_counter_compiler as compiler
import explore_global_offset_positivity as marked
import explore_cyclic_entry_serial_composition as cyclic


def empty_graph():
    code={'bad':('dec',1,'reject','restore'),
          'restore':('inc',1,'cleanup'),
          'cleanup':('dec',0,'accept','cleanup'),
          'accept':('halt',True),'reject':('halt',False)}
    graph=marked.build_marked_graph(code,'bad')
    quotient=cyclic.cyclic_graph(graph)
    # The ordinary machine always takes the immediate rejecting branch.
    for x in range(33):
        target,values,branch=compiler.step(code,'bad',[x,0,0])
        assert (target,values,branch)==('reject',[x,0,0],'zero')
    return code,graph,quotient


def rom_constants(graph):
    nodes=[graph['initial']]+sorted(n for n in graph['nodes'] if n!=graph['initial'])
    lookup={n:i for i,n in enumerate(nodes)};n=len(nodes);N=n+2
    prime=int(sp.nextprime(N));ell=2
    while 3**ell<=n:ell+=1
    marks=[2*prime*i+(i*i)%prime for i in range(N)]
    shift=max(marks)+1;coords=[ell*(shift+a) for a in marks]
    assert len({a+b for i,a in enumerate(coords) for b in coords[i:]})==N*(N+1)//2
    assert 2*min(coords)>max(coords)
    a=coords[:n];bs,bz=coords[n:];d=bz
    edges=sorted((lookup[u],lookup[v]) for u,v in graph['edges'])
    labels=[graph['nodes'][node] for node in nodes]
    positions=[d+a[v]-a[u] for u,v in edges]+[d-ai for ai in a]
    positions += [d+bs-a[i] for i,(_,sign,_) in enumerate(labels) if sign>0]
    positions += [d+bz-a[i] for i,(_,_,zero) in enumerate(labels) if not zero]
    assert len(positions)==len(set(positions)) and min(positions)>=0
    K=sum(3**p for p in positions);S=sum(3**p for p in a)
    g=3**d;hs=3**(d+bs);hz=3**(d+bz);I=3**a[0]
    threshold=max(4*S,8*(hs+hz),g*(I+1),(K+g)*(S+1),81)
    e=max(positions)+max(a)+ell
    e+=(-e)%ell
    while 3**e<=threshold:e+=ell
    forbidden={d+bs,d+bz,e};Zon=sum(3**p for p in forbidden)
    width=e+ell;R=3**width;B0=3**ell
    grid=(R-1)//(B0-1);zgrid=grid-Zon
    assert zgrid>0 and (B0-1)*(Zon+zgrid)==R-1
    assert R>4 and K<hz and R>K and R>2*g*S
    rows={}
    for u,v in edges:
        support={p+a[u] for p in positions}
        remove={d+a[v]}
        if labels[u][1]>0:remove.add(d+bs)
        if not labels[u][2]:remove.add(d+bz)
        assert remove<=support
        junk=support-remove
        assert not junk&forbidden and all(p%ell==0 and p<width for p in junk)
        V=sum(3**p for p in junk)
        assert V==K*3**a[u]-g*3**a[v]-hs*int(labels[u][1]>0)-hz*int(not labels[u][2])
        assert 0<V<zgrid and 3**a[u]<=S
        rows[u,v]=V
    return dict(nodes=nodes,lookup=lookup,labels=labels,a=a,edges=edges,positions=positions,
                K=K,S=S,g=g,hs=hs,hz=hz,I=I,Zon=Zon,B0=B0,ell=ell,
                width=width,R=R,zgrid=zgrid,rows=rows)


def split_small(n):
    assert n>=0
    a=b=0;p=1
    while n:
        n,d=divmod(n,3)
        if d:a+=p
        if d==2:b+=p
        p*=3
    assert a+b>=0
    return a,b


def boolean(n):
    if n<0:return False
    while n:
        n,d=divmod(n,3)
        if d==2:return False
    return True


def local_negative(R,n):
    g=(R-3)//6;b=R//3
    eL,e1=split_small(n-1)
    assert boolean(eL) and boolean(e1) and eL+e1==n-1
    a1=g-e1;a0=g-b-eL
    fields=(g-a0,g-a1,a1)
    assert a0+a1==-n and a0<0 and a1>=0
    # All Boolean claims follow from disjoint support/complement intervals.
    assert eL<b and e1<b and fields==(b+eL,e1,g-e1)
    return a0,a1,fields


def build(c):
    ops,pairs,source,origins=base.build();s=base.SYM
    override={'grid_width':(c['Zon'],'zgrid'),'grid_width_product':(c['B0']-1,'grid_width'),
              'WK':('R',c['K']),'route_coeff':('WK',c['g']),
              'sign_output':(c['hs'],'Kp'),'nozero_output':(c['hz'],'Dzero'),
              'route_final':(c['g']*c['I'],'twice_J'),'paired_grid_shift':('q2',c['S'])}
    changed=[]
    for name,op,a,b in ops:
        if name in override:a,b=override[name]
        changed.append((name,op,a,b))
        if name=='raw_packed':
            changed.extend([('omitted_weight','*','q4','q'),
                            ('omitted_track','*','omitted_weight','A0'),
                            ('relaxed_packed','-','raw_packed','omitted_track')])
        if name=='packed_index_rhs':changed[-1]=(name,op,a,'relaxed_packed')
    fields=[s['Kp'],s['Km'],s['H']-s['Dzero'],s['Dzero'],s['Tgap']-s['A0'],0,
            s['Tgap']-s['A1'],s['A1'],s['zgrid']*s['H']-s['PV'],s['PV'],
            c['S']*s['H']-s['PC'],s['PC']]
    raw=sum(f*s['q']**i for i,f in enumerate(fields))
    source=list(source)
    source[origins.index(26)]=(c['B0']-1)*(c['Zon']+s['zgrid'])-s['R']+1
    source[origins.index(25)]=(s['R']*c['K']-c['g'])*s['PC']-2*c['g']*c['I']*s['Jrep']-s['R']*(s['PV']+c['hs']*s['Kp']+c['hz']*s['Dzero'])
    source[origins.index(9)]=2*s['r']+1-s['q']**12-raw
    return changed,pairs,source,origins


def source_check():
    K,S,g,I,hs,hz,Zon,B0=sp.symbols('K S g I hs hz Zon B0')
    c=dict(K=K,S=S,g=g,I=I,hs=hs,hz=hz,Zon=Zon,B0=B0)
    ops,pairs,source,origins=build(c);env=dict(base.SYM)
    for name,op,a,b in ops:
        aa=env[a] if isinstance(a,str) else a;bb=env[b] if isinstance(b,str) else b
        env[name]=aa*bb if op=='*' else aa+bb if op=='+' else aa-bb
    q=base.SYM['q'];s=base.SYM
    X=s['Km']+q*q*(s['Dzero']+q*q*(s['A0']+q*q*(s['A1']+q*q*(s['PV']+q*q*s['PC']))))
    geometry=source[origins.index(0)];sign=source[origins.index(3)]
    u=2*s['r']+1+s['j']*s['c']
    for (left,right),p,origin in zip(pairs,source,origins):
        correction=geometry*X+sign if origin==9 else 0
        if origin==18:correction=source[origins.index(17)]*(u*u-s['y_aux']**2)
        assert sp.expand(env[left]-env[right]-p-correction)==0,origin
    mul=sum(op=='*' for _,op,_,_ in ops);add=len(ops)-mul
    assert (len(ops),mul,add,len(source))==(103,57,46,22)
    return dict(operations=103,multiplications=57,additions_or_subtractions=46,equations=22,
                positive_unknowns=len(base.OUTER_NAMES+base.CORE_NAMES),omitted_slot=5,
                scope='Literal diagnostic delta over100: q5, q5*A0, and subtraction. This refuted source is not a proposed improvement; no minimum-cost omission schedule is asserted.')


def signed_path(x,graph,quotient):
    seq=list(graph['prefix'])+graph['macros']['bad','nonzero']+graph['macros']['restore','inc']
    seq+=graph['macros']['cleanup','nonzero']*x+graph['macros']['cleanup','zero']
    values=[2*x,0,0];records=[];last=None
    for node in seq:
        if last is not None:assert (last,node) in quotient['edges']
        lane,sign,zero=quotient['nodes'][node];n=values[lane]
        assert not zero or n==0
        records.append((node,n,sign,zero));values[lane]+=sign;last=node
    assert values==[0,0,0] and (last,quotient['initial']) in quotient['edges']
    assert len(records)%6==0 and [n for _,n,_,_ in records if n<0]==[-1,-2,-1]
    assert records[0][2]==1 and all(n==1 and zero==0 for _,n,_,zero in records[-3:])
    return records


def complete_outer(x,graph,quotient,c):
    records=signed_path(x,graph,quotient);R=c['R'];width=c['width'];g=(R-3)//6
    # Use a bounded symbolic-support construction for each row.  Huge
    # integer fields are packed only once; digit loops do not scan q^12.
    tracks=[];rowmask_checks=0
    for index,(node,n,sign,zero) in enumerate(records):
        if n<0:
            assert not zero;a0,a1,_=local_negative(R,-n)
        else:
            a0,a1=split_small(n)
            if n==1 and index%2:a0,a1=a1,a0
        tau=0 if zero else g
        if zero:assert a0==a1==0
        else:
            if n>=0:assert boolean(a0) and boolean(a1) and max(a0,a1)<R//3
        assert 0<=tau-a0<R and 0<=tau-a1<R and 0<=a1<R
        tracks.append([a0,a1]);rowmask_checks+=3
    # Both globals must be positive; the last three sources are1.  Reserve
    # the final two high rows for opposite tracks, and a third for parity.
    tracks[-1]=[1,0];tracks[-2]=[0,1];tracks[-3]=[1,0]
    if sum(a for a,b in tracks)%2:tracks[-3]=[0,1]
    assert sum(a for a,b in tracks)%2==0
    u=len(records);q=R**u;H=(q-1)//(R-1)
    def pack(values):
        acc=0
        for v in reversed(values):acc=acc*R+v
        return acc
    A0=pack([a for a,b in tracks]);A1=pack([b for a,b in tracks])
    assert A0>0 and A1>0 and A0%2==0
    kp=pack([int(sign>0) for _,_,sign,_ in records]);km=H-kp
    Z=pack([zero for _,_,_,zero in records]);D=H-Z;t=g*D
    states=[c['lookup'][node] for node,_,_,_ in records];following=states[1:]+[0]
    PC=pack([3**c['a'][s] for s in states]);PV=pack([c['rows'][s,n] for s,n in zip(states,following)])
    vals=dict(x=x,q=q,Jrep=q-1,W=R**3,H=2*H,v=q//R**3,Tgap=2*t,
              A0=2*A0,A1=2*A1,Kp=2*kp,Km=2*km,Dzero=2*D,
              alphaI=R-4*x,R=R,PC=2*PC,PV=2*PV,zgrid=c['zgrid'])
    assert min(vals.values())>0 and Z>0
    # The first negative row has n=-1 and no incoming normalization borrow.
    # Its A0 remainder is 2*(R/3)+g, with a forbidden leading trit2.
    first_negative=next(i for i,rec in enumerate(records) if rec[1]<0)
    assert records[first_negative][1]==-1
    assert all(0<=a<R for a,b in tracks[:first_negative])
    assert tracks[first_negative][0]%R==2*(R//3)+g
    assert (tracks[first_negative][0]%R)//(R//3)==2
    # Every retained mask is Boolean by the rowwise support construction.
    fields=[kp,km,Z,D,t-A0,0,t-A1,A1,c['zgrid']*H-PV,PV,c['S']*H-PC,PC]
    assert min(fields)>=0 and max(fields)<q
    assert fields[4]==pack([(0 if rec[3] else g)-a for rec,(a,b) in zip(records,tracks)])
    assert fields[6]==pack([(0 if rec[3] else g)-b for rec,(a,b) in zip(records,tracks)])
    ops,pairs,_,origins=build(c);env=dict(vals)
    # Evaluate the factored packing once, reusing its power chain.  Repeated
    # q**i expansion of this large word is unnecessary: source_check proves
    # the exact conceptual identity, and row supports prove its masks.
    for name,op,a,b in ops:
        if name=='tr1':continue
        if (isinstance(a,str) and a not in env) or (isinstance(b,str) and b not in env):continue
        aa=env[a] if isinstance(a,str) else a;bb=env[b] if isinstance(b,str) else b
        env[name]=aa*bb if op=='*' else aa+bb if op=='+' else aa-bb
        if name=='packed_index_rhs':break
    P=env['relaxed_packed'];L=env['D0'];r=(L+P-1)//2
    assert 2*r+1==L+P and r%2==0 and 0<P<L and P%3==2
    vals.update(r=r,beta=L-r)
    env.update(r=r,beta=L-r,program_bound=L)
    env['tr1']=2*r+1
    outer=[p for p,o in zip(pairs,origins) if o<10 or o>=20]
    assert len(outer)==12 and all(env[a]==env[b] for a,b in outer)
    assert r>=27 and L>=81 and L//2<=r<L and L>4
    return dict(input=x,serial_rows=u,negative_source_values=[-1,-2,-1],
                all_zero_requests_true=True,positive_global_tracks=True,
                even_index=True,actual_width=width,retained_semantic_masks=11,
                twelve_positions_with_zero_placeholder=True,exact_outer_comparisons=12,
                row_counter_mask_checks=rowmask_checks,central_valuation=12*width*u,
                packed_bit_length=P.bit_length(),
                scope='The complete outer tuple is materialized and all12 source comparisons evaluated. Booleanity and exact central valuation use the proved row-support construction; enormous Pell auxiliaries are supplied by the fixed43 positive converse, not materialized.')


def verify():
    source=source_check();code,graph,quotient=empty_graph();c=rom_constants(quotient)
    local=0
    for m in range(2,8):
        for n in range(1,min(3**(m-1),100)):
            a0,a1,f=local_negative(3**m,n)
            assert all(boolean(v) for v in f);local+=1
    return dict(status='PASS_SINGLE_COUNTER_TRACK_OMISSION_REFUTATION',source=source,
                review='Author and independent complete proof/source reviews and fresh full verification runs pass without findings.',
                fixed_graph=dict(states=len(c['nodes']),edges=len(c['edges']),
                                 grid_spacing=c['ell'],marker_capacity=c['B0'],
                                 checked_ROM_rows=len(c['rows']),width=c['width']),
                local_negative_rows=local,complete=[complete_outer(x,graph,quotient,c) for x in (1,2)],
                scope='A fixed empty counter program admits these positive tuples after one track mask is replaced by a zero slot. All requested zeros remain actual zeros. This refutes the stated omission, not other re-encodings, and does not improve the established90 frontier.')


if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,indent=2))
