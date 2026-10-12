"""Binary chamber connectivity after cutting a supplied normal surface.

The result counts connected cut-open pieces. It does not construct cut manifold
triangulations, boundary patterns, regluing data or a knot-recognition verdict.
The finite one-torus-boundary source contract is inherited from the validated
normal geometry. No disc, chamber or face-region family is expanded.
"""
from .interval_orbits import IntervalPairing,count_orbits
from .normal_surface_geometry import _prepare,_coordinates,_quad,_fingerprint


def _exceptional_chambers(rows,check):
    marks=[];offset=0
    for row in rows:
        check();q=sum(row[4:]);marks.append(offset)
        if q:marks.append(offset+q)
        offset+=q+1
        for count in row[:4]:
            check()
            if count:marks.append(offset)
            offset+=count
    return marks


def _chamber_system(prepared,rows,check):
    layout=[];total=0
    for row in rows:
        check();q=sum(row[4:]);kind=next((j for j in range(3)if row[4+j]),None)
        chain=total;total+=q+1;arms=[]
        for v in range(4):check();arms.append(total);total+=row[v]
        layout.append((chain,arms,q,kind))

    def local(t,f,v,rank):
        chain,arms,q,kind=layout[t]
        if rank<rows[t][v]:return arms[v]+rank,1
        if kind is None or _quad(f,v)!=kind:raise ArithmeticError('invalid face chamber rank')
        if v in (0,kind+1):return chain+rank-rows[t][v],1
        return chain+q-rank+rows[t][v],-1

    def central(t,f):
        chain,arms,q,kind=layout[t]
        return chain+(q if kind is not None and f in (0,kind+1)else 0)

    pairs=[]
    for t,f,u,g,p in prepared['pairs']:
        check();a,b=central(t,f),central(u,g)
        pairs.append(IntervalPairing(a,a,b,b))
        for v in range(4):
            check()
            if v==f:continue
            w=p[v];size=rows[t][v]+rows[t][4+_quad(f,v)]
            if size!=rows[u][w]+rows[u][4+_quad(g,w)]:raise ArithmeticError('face chamber counts differ')
            bounds=sorted({0,rows[t][v],rows[u][w],size})
            for low,stop in zip(bounds,bounds[1:]):
                check()
                if low==stop:continue
                a,sa=local(t,f,v,low);b,sb=local(u,g,w,low)
                aa=a+sa*(stop-low-1);bb=b+sb*(stop-low-1)
                pairs.append(IntervalPairing(min(a,aa),max(a,aa),min(b,bb),max(b,bb),sa!=sb))
    return total,pairs


def normal_complement_components(triangulation,coordinates,*,max_cycles=None,
        record_certificate=False,classify_prisms=False,periodic_rule='fine_wilf',sweep_direction='forward',check=lambda:None):
    """Count connected components of the cut-open supplied manifold.

    Unlimited orbit work is polynomial in tetrahedra and binary coordinate
    size. max_cycles bounds begun orbit cycles; it is not a wall-time bound.
    Incomplete results contain no component count or certificate. Callbacks
    propagate. There is no normal-multiplicity division: parallel surfaces
    can create additional cut components, including one-sided even multiples.
    classify_prisms optionally counts components avoiding the <=6T non-prism
    chambers. They are interval bundles over normal midsections; marked core
    components may also be interval bundles. Both queries share max_cycles.
    """
    check()
    if type(record_certificate)is not bool:raise ValueError('record_certificate must be bool')
    if type(classify_prisms)is not bool:raise ValueError('classify_prisms must be bool')
    if max_cycles is not None and(type(max_cycles)is not int or max_cycles<0):
        raise ValueError('max_cycles must be a nonnegative integer or None')
    prepared=_prepare(triangulation,check);analysed=_coordinates(prepared,coordinates,check)
    size,pairs=_chamber_system(prepared,analysed['rows'],check)
    query=count_orbits(size,pairs,max_cycles=max_cycles,periodic_rule=periodic_rule,
        sweep_direction=sweep_direction,record_certificate=record_certificate,check=check)
    result=dict(status='COMPLETE'if query.complete else 'INCONCLUSIVE',
        tetrahedra=len(analysed['rows']),normal_disks=analysed['normal_disks'],
        maximum_coordinate_bits=analysed['maximum_coordinate_bits'],
        chamber_points=size,interval_pairings=len(pairs),cycles=query.cycles,stats=dict(query.stats),
        trust='cut component count for the supplied finite triangulation and surface; no knot verdict')
    if not query.complete:
        result['reason']='orbit-cycle allowance exhausted';return result
    cone=None;marks=None
    if classify_prisms:
        marks=_exceptional_chambers(analysed['rows'],check)
        coned=pairs.copy()
        for point in marks[1:]:
            check();coned.append(IntervalPairing(0,0,point,point))
        remaining=None if max_cycles is None else max_cycles-query.cycles
        cone=count_orbits(size,coned,max_cycles=remaining,periodic_rule=periodic_rule,
            sweep_direction=sweep_direction,record_certificate=record_certificate,check=check)
        result['cycles']+=cone.cycles
        result['product_query']=dict(cycles=cone.cycles,interval_pairings=len(coned),stats=dict(cone.stats))
        if not cone.complete:
            result.update(status='INCONCLUSIVE',reason='shared orbit-cycle allowance exhausted');return result
        core=query.orbits-cone.orbits+1;product=cone.orbits-1
        if not 1<=core<=len(marks) or product<0:raise ArithmeticError('invalid exceptional-component count')
        result.update(core_components=core,prismatic_components=product,exceptional_chambers=len(marks))
    result['cut_components']=query.orbits
    if record_certificate:
        result['certificate']=dict(schema='normal-cut-components-v1',
            input_sha256=_fingerprint(triangulation,analysed,check),cut_components=query.orbits,
            orbit_certificate=query.certificate)
        if classify_prisms:
            result['certificate'].update(schema='normal-cut-components-v2',
                core_components=core,prismatic_components=product,core_cone_certificate=cone.certificate)
    check();return result
