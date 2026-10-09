"""Complete disk selection for an explicit finite surface-patch system.

Input sites each have a finite list of orientable simplicial patches. Corresponding
ports have a fixed seam type and subdivision. Every port is paired once, except
one permanent boundary anchor. All patches are nonempty and every component
meets a port. This is a complete optimizer for this supplied finite model, not a
complete producer of normal-surface choices for a knot exterior.
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import Sequence
from .core import Candidate, SignedPartition, reduce_family, integer, BudgetExceeded
from .surfaces import Surface, SurfaceInfo, inspect, barycentric_subdivision, realize_partition

@dataclass(frozen=True,slots=True)
class SeamPair:
    a: tuple[int,int]
    b: tuple[int,int]
    reverse: bool=False

@dataclass(frozen=True,slots=True)
class PatchSystem:
    options: tuple[tuple[Surface,...],...]
    pairs: tuple[SeamPair,...]
    anchor: tuple[int,int]
    order: tuple[int,...]

@dataclass(frozen=True,slots=True)
class PatchAnswer:
    minimum_cost: int | None
    disk_exists: bool
    choices: tuple[int,...] | None
    history: tuple[dict,...]
    temporary_width: int


def validate(system:PatchSystem) -> tuple[tuple[SurfaceInfo,...],...]:
    n=len(system.options)
    if n<1 or sorted(system.order)!=list(range(n)) or any(type(i) is not int for i in system.order):
        raise ValueError('order must enumerate all sites exactly once')
    if (type(system.anchor) is not tuple or len(system.anchor)!=2 or
        any(type(i) is not int for i in system.anchor) or system.anchor[0]!=system.order[0]):
        raise ValueError('anchor site must be first')
    info=[]; ports=set(); formats={}
    for v,opts in enumerate(system.options):
        if not opts:raise ValueError('every site needs a nonempty option list')
        records=[]; schema=None
        for s in opts:
            i=inspect(s)
            if not i.orientable or i.signature is None:
                raise ValueError('patch options must be orientable and live')
            f=tuple((kind,len(path)) for kind,path in zip(i.seam_types,s.seams))
            if schema is None:schema=f
            elif schema!=f:raise ValueError('incompatible seam schemas at a site')
            records.append(i)
        for p,f in enumerate(schema):
            ports.add((v,p));formats[(v,p)]=f
        info.append(tuple(records))
    if system.anchor not in ports:raise ValueError('missing anchor')
    used={system.anchor}
    for pair in system.pairs:
        if not isinstance(pair,SeamPair) or type(pair.reverse) is not bool:
            raise ValueError('invalid seam pair')
        if any(type(p) is not tuple or len(p)!=2 or any(type(i) is not int for i in p) for p in (pair.a,pair.b)):
            raise ValueError('invalid port identifier')
        if pair.a not in ports or pair.b not in ports or pair.a==pair.b or pair.a[0]==pair.b[0]:
            raise ValueError('pairs must use valid ports on distinct sites')
        if pair.a in used or pair.b in used:raise ValueError('port used twice')
        if formats[pair.a]!=formats[pair.b]:raise ValueError('paired seam schemas differ')
        used.update((pair.a,pair.b))
    if used!=ports:raise ValueError('every nonanchor port must be paired')
    return tuple(info)


def solve(system:PatchSystem,*,reduced:bool=True,max_dimension:int=1<<20,
          max_candidates:int=1_000_000) -> PatchAnswer:
    integer(max_candidates,'max_candidates');integer(max_dimension,'max_dimension')
    if max_candidates<0 or max_dimension<1:raise ValueError('invalid resource budget')
    infos=validate(system);n=len(infos);processed=set();active=[];states=[];history=[];width=0
    # A state is (signed partition, additive cost, choices indexed by sites).
    for step,site in enumerate(system.order):
        new_ports=[(site,j) for j in range(len(system.options[site][0].seams))]
        temporary=active+new_ports;width=max(width,len(temporary));positions={p:i for i,p in enumerate(temporary)}
        closing=[p for p in system.pairs if p.a in positions and p.b in positions and
                 (p.a[0]==site or p.b[0]==site)]
        removed={p for pair in closing for p in (pair.a,pair.b)}
        keep=[i for i,p in enumerate(temporary) if p not in removed]
        next_active=[temporary[i] for i in keep]
        if not keep:raise AssertionError('permanent anchor was lost')
        generation=[];rejected=0;attempted=0
        constraints=tuple((positions[p.a],positions[p.b],1^int(p.reverse)) for p in closing)
        arc_charge=sum(infos[p.a[0]][0].seam_types[p.a[1]]=='arc' for p in closing)
        prior=states if step else [(None,0,(-1,)*n)]
        for prev,base_cost,choices in prior:
            for option,info in enumerate(infos[site]):
                attempted+=1
                if attempted>max_candidates:raise BudgetExceeded('patch transition exceeds candidate budget')
                p=info.signature if prev is None else prev.disjoint(info.signature)
                cost=base_cost-info.euler+arc_charge
                if constraints:p=SignedPartition.from_edges(p.r,p.edges()+constraints)
                if p is not None:p=p.restrict(keep)
                if p is None:
                    rejected+=1;continue
                new_choice=list(choices);new_choice[site]=option
                generation.append((p,cost,tuple(new_choice)))
        # Deterministic exact-state baseline and tie handling on both routes.
        best={}
        for state in generation:
            p,c,_=state
            if p not in best or c<best[p][1]:best[p]=state
        states=list(best.values());before=len(states)
        if reduced and states:
            candidates=[Candidate(p,c,str(i),'patch-interface') for i,(p,c,_) in enumerate(states)]
            red=reduce_family(candidates,max_dimension=max_dimension,max_candidates=max_candidates)
            states=[states[i] for i in red.certificate.selected]
        history.append({'site':site,'attempted':attempted,'rejected':rejected,'unique_before':before,
                        'retained':len(states),'frontier':len(next_active),'temporary_ports':len(temporary)})
        processed.add(site);active=next_active
        if not states:
            return PatchAnswer(None,False,None,tuple(history),width)
    if active!=[system.anchor] or any(p.r!=1 or p.blocks!=1 for p,_,_ in states):
        raise AssertionError('unexpected terminal frontier')
    p,cost,choices=min(states,key=lambda s:s[1])
    if cost < -1:
        raise AssertionError('Euler bound violated: invalid transition contract')
    return PatchAnswer(cost,cost==-1,choices,tuple(history),width)


def assemble(system:PatchSystem,choices:Sequence[int]) -> Surface:
    """Independent global mesh quotient, using a barycentric subdivision.

    Subdivision makes the quotient a genuine simplicial complex even where two
    original triangles share all three glued boundary edges. No signed-state
    joins, cut rows, or local DP transitions are used.
    """
    validate(system)
    if len(choices)!=len(system.options) or any(type(c) is not int or not 0<=c<len(opts) for c,opts in zip(choices,system.options)):
        raise ValueError('one valid option index per site required')
    pieces=[barycentric_subdivision(opts[c]) for opts,c in zip(system.options,choices)]
    ids={}
    for site,s in enumerate(pieces):
        for v in sorted({v for face in s.triangles for v in face}):ids[(site,v)]=len(ids)
    parent=list(range(len(ids)))
    def find(x):
        while parent[x]!=x:
            parent[x]=parent[parent[x]];x=parent[x]
        return x
    for pair in system.pairs:
        a=pieces[pair.a[0]].seams[pair.a[1]];b=pieces[pair.b[0]].seams[pair.b[1]]
        if pair.reverse:b=tuple(reversed(b))
        for x,y in zip(a,b):parent[find(ids[(pair.b[0],y)])]=find(ids[(pair.a[0],x)])
    new_ids={};tris=[]
    for site,s in enumerate(pieces):
        for face in s.triangles:
            out=[]
            for v in face:
                root=find(ids[(site,v)])
                if root not in new_ids:new_ids[root]=len(new_ids)
                out.append(new_ids[root])
            tris.append(tuple(out))
    surface=Surface(tuple(tris));inspect(surface,require_live=False);return surface


def verify_witness(system:PatchSystem,answer:PatchAnswer) -> bool:
    """Replay a positive/optimal witness's geometry, not its optimality claim.

    False/no-solution answers need replay of the entire DP or a completeness
    certificate; this routine deliberately does not certify them.
    """
    if answer.choices is None or type(answer.minimum_cost) is not int or type(answer.disk_exists) is not bool:return False
    try:
        info=inspect(assemble(system,answer.choices),require_live=False)
        return (info.components==1 and info.orientable and info.boundary_components>0 and
                -info.euler==answer.minimum_cost and info.is_disk==answer.disk_exists)
    except (ValueError,TypeError,IndexError):return False


def grid_system(rows:int,columns:int,*,signed:bool=True) -> PatchSystem:
    """Explicit surface-patch benchmark generator, not a knot-exterior model."""
    from .core import partitions
    if type(rows) is not int or type(columns) is not int or rows<1 or columns<1:
        raise ValueError('positive grid dimensions required')
    n=rows*columns;edges=[]
    def v(i,j):return j*rows+i
    for j in range(columns):
        for i in range(rows):
            if i+1<rows:edges.append((v(i,j),v(i+1,j)))
            if j+1<columns:edges.append((v(i,j),v(i,j+1)))
    counts=[0]*n;counts[0]=1;pairs=[]
    for a,b in edges:
        pairs.append(SeamPair((a,counts[a]),(b,counts[b]),False));counts[a]+=1;counts[b]+=1
    options=[]
    for d in counts:
        if d==0:raise ValueError('isolated nonanchor site')
        ps=[p for p in partitions(d) if signed or not any(p.offsets)]
        options.append(tuple(realize_partition(p) for p in ps))
    return PatchSystem(tuple(options),tuple(pairs),(0,0),tuple(range(n)))
