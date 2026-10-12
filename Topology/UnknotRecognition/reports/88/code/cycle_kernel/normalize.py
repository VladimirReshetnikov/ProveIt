"""Polynomial marked-cut kernel for binary powers of arbitrary graph tiles.

No topology assertion is returned. The expanded source graph is never constructed
when its repetition count exceeds the explicit bounded preprocessing size.
"""
from __future__ import annotations
from dataclasses import dataclass
from .model import Graph,Builder,DSU,components,power_explicit,chain,induced
from .partitions import boundary_partition,stabilize,rank,product

@dataclass
class Raw:
    nodes: set
    edges: list  # (layer_offset, original edge index)
    pairs: list  # source vertex equalities
    left: tuple=()
    right: tuple=()

@dataclass
class Seam:
    raw: Raw
    left: tuple
    right: tuple
    kind: str

@dataclass
class NormalForm:
    source: Graph
    labels: tuple
    groups: tuple
    through: tuple
    permutation: dict
    seams: tuple
    templates: dict
    raw_templates: dict
    input_indices: dict
    output_indices: dict
    floating: Graph

def raw_add(builder:Builder,u:Graph,raw:Raw,shift:int=0):
    for j,v in sorted(raw.nodes):builder.vertex((j+shift,v))
    for j,e in raw.edges:
        a,b=u.edges[e];builder.edge((j+shift,a),(j+shift,b))
    for (j,a),(k,b) in raw.pairs:builder.identify((j+shift,a),(k+shift,b))

def raw_components(u:Graph,groups,ids,offset=0)->Raw:
    vs=set(v for c in ids for v in groups[c])
    return Raw({(offset,v) for v in vs},[(offset,e) for e,(a,b) in enumerate(u.edges) if a in vs and b in vs],[])

def merge_raw(*rs:Raw)->Raw:
    nodes=set();ed=[];eq=[]
    for r in rs:nodes.update(r.nodes);ed.extend(r.edges);eq.extend(r.pairs)
    return Raw(nodes,ed,eq)

def shifted(r:Raw,k:int)->Raw:
    return Raw({(j+k,v) for j,v in r.nodes},[(j+k,e) for j,e in r.edges],
               [((j+k,a),(h+k,b)) for (j,a),(h,b) in r.pairs])

def normal_form(u:Graph)->NormalForm:
    """Normalize a stable tile: rank(U^2)=rank(U) is checked explicitly."""
    u.validate_tile(); p=boundary_partition(u)
    if rank(product(p,p))!=rank(p):raise ValueError('source tile is not rank-stable')
    lab,groups=components(u)
    lset={lab[x] for x in u.left};rset={lab[x] for x in u.right}
    th=tuple(sorted(lset&rset)); thset=set(th)
    sideleft=rset-thset; sideright=lset-thset
    r0=raw_components(u,groups,sideleft,0)
    r1=raw_components(u,groups,sideright,1)
    raw=merge_raw(r0,r1)
    raw.nodes.update((0,v) for v in u.right)
    raw.nodes.update((1,v) for v in u.left)
    raw.pairs=[((0,a),(1,b)) for a,b in zip(u.right,u.left)]
    nodes=sorted(raw.nodes);idx={x:i for i,x in enumerate(nodes)};d=DSU(len(nodes))
    for (j,a),(k,b) in raw.pairs:d.union(idx[j,a],idx[k,b])
    for j,e in raw.edges:
        a,b=u.edges[e];d.union(idx[j,a],idx[j,b])
    buckets={}
    for x in nodes:buckets.setdefault(d.find(idx[x]),set()).add(x)
    seams=[]
    for ns in sorted(buckets.values(),key=lambda z:min(z)):
        ls=tuple(sorted({lab[v] for j,v in ns if j==0 and lab[v] in thset}))
        rs=tuple(sorted({lab[v] for j,v in ns if j==1 and lab[v] in thset}))
        if len(ls)>1 or len(rs)>1:raise AssertionError('stable seam merges through components')
        ed=[(j,e) for j,e in raw.edges if (j,u.edges[e][0]) in ns]
        eq=[(a,b) for a,b in raw.pairs if a in ns]
        kind=('B' if ls and rs else 'L' if ls else 'R' if rs else 'F')
        seams.append(Seam(Raw(ns,ed,eq),ls,rs,kind))
    pi={}
    for z in seams:
        if z.kind=='B':
            a,b=z.left[0],z.right[0]
            if a in pi and pi[a]!=b:raise AssertionError('nonfunctional through matching')
            pi[a]=b
    if set(pi)!=thset or set(pi.values())!=thset:raise AssertionError('through matching is not a permutation')
    ins={};outs={};tm={};rt={}
    for a in th:
        inp=sorted({i for z in seams if z.kind=='B' and z.right==(a,)
                    for i,v in enumerate(u.left) if (1,v) in z.raw.nodes and lab[v] in thset})
        out=sorted({i for z in seams if z.kind=='B' and z.left==(a,)
                    for i,v in enumerate(u.left) if (1,v) in z.raw.nodes and lab[v] in thset})
        if not inp or not out:raise AssertionError('empty through interface')
        chosen=[raw_components(u,groups,[a])]
        chosen += [z.raw for z in seams if z.kind in ('L','B') and z.left==(a,)]
        chosen += [shifted(z.raw,-1) for z in seams if z.kind=='R' and z.right==(a,)]
        rr=merge_raw(*chosen)
        rr.left=tuple((0,u.left[i]) for i in inp)
        rr.right=tuple((1,u.left[i]) for i in out)
        b=Builder();raw_add(b,u,rr)
        g=b.finish(rr.left,rr.right)[0]
        if set(g.left)&set(g.right) or len(components(g)[1])!=1:
            raise AssertionError('decorated through piece is not a connected disjoint-port piece')
        ins[a]=tuple(inp);outs[a]=tuple(out);tm[a]=g;rt[a]=rr
    for a in th:
        if outs[a]!=ins[pi[a]]:raise AssertionError('ordered decorated interfaces disagree')
    float_ids=set(range(len(groups)))-lset-rset
    floating=induced(u,[v for a in float_ids for v in groups[a]])
    return NormalForm(u,lab,groups,th,pi,tuple(seams),tm,rt,ins,outs,floating)

def cycle_from(pi,a):
    out=[a];b=pi[a]
    while b!=a:
        if b in out:raise AssertionError('invalid component permutation')
        out.append(b);b=pi[b]
    return out

def _attach(b:Builder,gs:list[Graph],keys:list,source_ports,target_ports):
    if len(gs)!=len(keys):raise ValueError('chain metadata mismatch')
    if not gs:
        if len(source_ports)!=len(target_ports):raise AssertionError('empty channel endpoint mismatch')
        for x,y in zip(source_ports,target_ports):b.identify(x,y)
        return
    for i,(g,key) in enumerate(zip(gs,keys)):
        b.add(g,key)
        if i:
            for x,y in zip(gs[i-1].right,g.left):b.identify((keys[i-1],x),(key,y))
    if len(source_ports)!=len(gs[0].left) or len(target_ports)!=len(gs[-1].right):
        raise AssertionError('channel endpoint mismatch')
    for x,y in zip(source_ports,gs[0].left):b.identify(x,(keys[0],y))
    for x,y in zip(gs[-1].right,target_ports):b.identify((keys[-1],x),y)

def stable_kernel(u:Graph,n:int,k:int=3,reduce:bool=True):
    if type(n)is not int or n<1:raise ValueError('positive repetition count required')
    if type(k)is not int or k<0:raise ValueError('nonnegative integer threshold required')
    if not reduce and n>10000:raise ValueError('literal normal-form expansion cap')
    if n<=2:return power_explicit(u,n),dict(mode='literal-stable',copies=n)
    nf=normal_form(u);b=Builder();th=set(nf.through)
    lset={nf.labels[x] for x in u.left};rset={nf.labels[x] for x in u.right}
    # Finite end context. Its raw tokens retain actual (binary) source layer IDs.
    ctx=[raw_components(u,nf.groups,th,0),raw_components(u,nf.groups,th,n-1),
         raw_components(u,nf.groups,lset-th,0),raw_components(u,nf.groups,rset-th,n-1)]
    ctx += [z.raw for z in nf.seams if z.kind in ('L','B')]
    ctx += [shifted(z.raw,n-2) for z in nf.seams if z.kind=='R']
    context=merge_raw(*ctx);raw_add(b,u,context)
    m=n-2;cutoff=4 if k==3 else k+2;channel_records=[]
    for a in nf.through: # a labels the SECOND source layer in this channel
        cy=cycle_from(nf.permutation,a);ell=len(cy);q,t=divmod(m,ell)
        qq=min(q,cutoff) if reduce else q
        labs=cy*qq+cy[:t]
        endpoint=cy[t]  # label in the final source layer; m modulo ell
        gs=[nf.templates[c] for c in labs];keys=[('channel',a,j) for j in range(len(labs))]
        source_ports=[(1,u.left[i]) for i in nf.input_indices[a]]
        target_ports=[(n-1,u.left[i]) for i in nf.input_indices[endpoint]]
        _attach(b,gs,keys,source_ports,target_ports)
        channel_records.append(dict(start=a,cycle=cy,quotient_hex=hex(q),remainder=t,
                                    retained_periods=qq,retained_pieces=len(labs)))
    # Detached components have no named ports: retain their exact two-mark effect.
    floatcap=max(2,k+1)
    counts=(n,n-1)
    fb=Builder()
    for z in nf.seams:
        if z.kind=='F':raw_add(fb,u,z.raw)
    seamfloat=fb.finish()[0]
    for tag,g,count in (('intrinsic',nf.floating,n),('seam',seamfloat,n-1)):
        keep=min(count,floatcap) if reduce else count
        # Isolated vertices are harmless; keeping bounded copies avoids any special semantic rule.
        for j in range(keep):b.add(g,('floating',tag,j))
    out=b.finish([(0,x) for x in u.left],[(n-1,x) for x in u.right])[0]
    meta=dict(mode='stable-channels',through=len(nf.through),permutation=[[a,nf.permutation[a]] for a in nf.through],
              channels=channel_records,cutoff=cutoff,island_cutoff=floatcap,
              template_vertices=sum(g.n for g in nf.templates.values()),
              template_edges=sum(len(g.edges) for g in nf.templates.values()),
              seam_kinds={z:sum(x.kind==z for x in nf.seams) for z in ('L','R','B','F')})
    return out,meta

def kernel_power(tile:Graph,n:int,k:int=3,*,connected_fastpath:bool=True):
    tile.validate_tile()
    if type(n)is not int or n<1:raise ValueError('positive integer repetition count required')
    if type(k)is not int or k<0:raise ValueError('nonnegative integer threshold required')
    p=boundary_partition(tile);cert=stabilize(p);s=cert['s']
    if connected_fastpath and len(components(tile)[1])==1:
        c=4 if k==3 else k+2
        g=power_explicit(tile,min(n,c),cap=max(c,10000))
        return g,dict(mode='connected',source_count_hex=hex(n),threshold=k,retained=min(n,c),stabilization=cert)
    q,t=divmod(n,s)
    if q==0:
        g=power_explicit(tile,n)
        return g,dict(mode='literal-prefix',stabilization=cert,source_count_hex=hex(n),threshold=k)
    u=power_explicit(tile,s,cap=max(s,10000))
    g,detail=stable_kernel(u,q,k)
    if t:g=chain([g,power_explicit(tile,t,cap=max(t,10000))])
    return g,dict(mode='arbitrary',source_count_hex=hex(n),threshold=k,stabilization=cert,
                  macro_count_hex=hex(q),tail=t,normalization=detail)
