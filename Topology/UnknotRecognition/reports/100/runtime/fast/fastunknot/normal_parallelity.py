"""Complete source parallelity bases and bounded complementary handle charts."""
from .interval_orbits import IntervalPairing
from .normal_surface_geometry import _prepare, _coordinates, _fingerprint
from .normal_parallelity_geometry import _parallelity_geometry
from .weighted_transversal import weighted_orbit_transversal
from .weighted_orbits import weighted_orbit_histogram


def _pair(a, b, lo, hi):
    s,o=a;t,p=b
    left=sorted((s*lo+o,s*(hi-1)+o));right=sorted((t*lo+p,t*(hi-1)+p))
    return IntervalPairing(*left,*right,s!=t)


def _systems(g, check):
    polygons=g['polygons'];v_pairs=[];b_pairs=[];p_pairs=[];fibre_pairs=[];v_weights=[];p_weights=[];carriers=[]
    size=g['polygon_points']
    for p in polygons:
        check();degree=len(p['edges']);dimension={'prism':0,'face_strip':1,'edge_cap':2}[p['kind']]
        value=[1-degree,0,0,0,0,0,0];value[2+dimension]=1
        if p['start']<p['stop']:p_weights.append((p['start'],p['stop'],value))
        for start in p['corner_starts']:carriers.append((start,start+p['stop']-p['start'],p['start']))
    for link in g['gluings']:
        check();p,q=polygons[link['left']],polygons[link['right']];a,b=link['left_map'],link['right_map'];lo,hi=link['rank_start'],link['rank_stop']
        p_pairs.append(_pair(a,b,lo,hi))
        points=sorted((a[0]*lo+a[1],a[0]*(hi-1)+a[1]));p_weights.append((points[0],points[1]+1,[1,0,0,0,0,0,0]))
        for end in (0,1):
            ca=p['corner_starts'][(link['left_edge']+end)%len(p['edges'])]-p['start']
            cb=q['corner_starts'][(link['right_edge']+(end^link['ends_reverse']))%len(q['edges'])]-q['start']
            v_pairs.append(_pair((a[0],a[1]+ca),(b[0],b[1]+cb),lo,hi))
        for sheet in (0,1):
            fibre_pairs.append(_pair((a[0],a[1]+sheet*size),(b[0],b[1]+(sheet^link['fibre_flip'])*size),lo,hi))
    b_pairs=list(v_pairs)
    for edge in g['free_edges']:
        check();p=polygons[edge['polygon']];lo,hi=edge['rank_start'],edge['rank_stop'];a,b=[p['corner_starts'][(edge['edge']+end)%len(p['edges'])]-1 for end in (0,1)]
        b_pairs.append(_pair((1,a),(1,b),lo,hi))
        for start in (a,b):v_weights.append((start+lo,start+hi,[1,int(not edge['original_boundary'])]))
        if edge['original_boundary']:p_weights.append((p['start']+lo-1,p['start']+hi-1,[0,0,0,0,0,1,0]))
        else:
            p_weights.append((p['start']+lo-1,p['start']+hi-1,[0,0,0,0,0,0,1<<edge['port']]))
    carriers.sort()
    return v_pairs,b_pairs,v_weights,p_pairs,p_weights,fibre_pairs,carriers


def _push_marks(rows, carriers, coordinate, check):
    weights=[];index=0
    for row in rows:
        if coordinate==1 and row['weight'][0]==0:continue
        lo,hi=row['start'],row['stop']
        while lo<hi:
            check()
            while carriers[index][1]<=lo:index+=1
            a,b,target=carriers[index];stop=min(hi,b);value=[0]*7;value[coordinate]=1
            weights.append((target+lo-a,target+stop-a,value));lo=stop
    return weights


def _orientations(histogram, double, check):
    counts={tuple(row['weight']):row['orbits']for row in histogram};cover={tuple(row['weight']):row['orbits']for row in double}
    output={};nonorientable={}
    for value in sorted(set(counts)|set(cover),key=lambda w:(sum(w[2:5]),w)):
        check()
        if sum(value[2:5])<=0:raise ArithmeticError('empty product-base profile')
        half=tuple(x//2 for x in value)if all(x%2==0 for x in value)else None
        excess=cover.get(value,0)-nonorientable.get(half,0)
        if excess<0 or excess%2:raise ArithmeticError('inconsistent fibre orientation cover')
        orientable=excess//2;twisted=counts.get(value,0)-orientable
        if twisted<0:raise ArithmeticError('negative twisted-base multiplicity')
        nonorientable[value]=twisted
        if orientable or twisted:output[value]=(orientable,twisted)
    return output


def _summary(g,vertices,boundary,polygons,double,cut_chi,check):
    classified=_orientations(polygons['histogram'],double['histogram'],check);profiles=[];seen=[]
    for value,(ori,twisted)in classified.items():
        check();chi,b,h0,h1,h2,old,mask=value;ports=[]
        if b<0 or old<0 or mask<0 or mask.bit_length()>len(g['ports']):raise ArithmeticError('invalid base boundary profile')
        while mask:
            bit=mask&-mask;ports.append(bit.bit_length()-1);mask-=bit
        copies=ori+twisted
        if ports:
            if copies!=1:raise ArithmeticError('core port occurs on several bundles')
            seen.extend(ports)
        for orientable,n in ((True,ori),(False,twisted)):
            if not n:continue
            complexity=2-b-chi
            if (orientable and(complexity<0 or complexity%2))or(not orientable and complexity<1):raise ArithmeticError('invalid base genus')
            profiles.append(dict(euler_characteristic=chi,boundary_components=b,orientable=orientable,
                genus=complexity//2 if orientable else None,crosscaps=None if orientable else complexity,
                product=orientable,multiplicity=n,handles=[h0,h1,h2],original_boundary_edges=old,core_ports=ports))
    if sorted(seen)!=list(range(len(g['ports']))):raise ArithmeticError('incomplete core-port partition')
    core_counts=[len(g['core'][f'handles{i}'])for i in range(4)];core_chi=sum((-1)**i*n for i,n in enumerate(core_counts))
    base_chi=sum(p['multiplicity']*p['euler_characteristic']for p in profiles)
    attach_vertices=sum(r['stop']-r['start']for r in vertices['representative_runs']if r['weight'][1])
    attach_chi=attach_vertices-len(g['ports'])
    if core_chi+base_chi-attach_chi!=cut_chi:raise ArithmeticError('parallelity/core Euler gluing failed')
    bcount=sum(r['stop']-r['start']for r in boundary['representative_runs']if r['weight'][0])
    if bcount!=sum(p['multiplicity']*p['boundary_components']for p in profiles):raise ArithmeticError('base boundary count disagrees')
    return dict(bundle_components=sum(p['multiplicity']for p in profiles),base_profiles=profiles,
                core_handle_counts=core_counts,core_euler_characteristic=core_chi,
                bundle_euler_characteristic=base_chi,attachment_euler_characteristic=attach_chi,
                core_attachment_vertices=attach_vertices)


def normal_cut_parallelity(triangulation,coordinates,*,max_cycles=None,record_certificate=False,check=lambda:None):
    """Recover all source 0/1/2 product handles, their bases and core charts.

    The complementary handles are bounded by 30*T. They are inherited raw
    core handles, without an admissibility or pattern-essentiality claim.
    All four discovery queries share max_cycles. Incomplete work has no
    geometric result or certificate; external cancellation propagates.
    """
    check()
    if type(record_certificate)is not bool:raise ValueError('record_certificate must be bool')
    if max_cycles is not None and(type(max_cycles)is not int or max_cycles<0):raise ValueError('max_cycles must be nonnegative or None')
    prepared=_prepare(triangulation,check);analysed=_coordinates(prepared,coordinates,check)
    g=_parallelity_geometry(prepared,analysed,check)
    vp,bp,vw,pp,pw,dp,carriers=_systems(g,check);remaining=max_cycles;stats={}
    result=dict(status='INCONCLUSIVE',trust='source parallelity bases and bounded inherited core charts; no hierarchy or knot verdict')
    def allowance(query,name):
        nonlocal remaining
        stats[name]=query['stats']
        if remaining is not None:remaining-=query['stats']['orbit_cycles']
        result['stats']=stats
        return query['status']=='COMPLETE'
    vertices=weighted_orbit_transversal(g['corner_points'],vp,vw,dimension=2,max_cycles=remaining,record_certificate=record_certificate,check=check)
    if not allowance(vertices,'vertices'):return result
    boundary=weighted_orbit_transversal(g['corner_points'],bp,vw,dimension=2,max_cycles=remaining,record_certificate=record_certificate,check=check)
    if not allowance(boundary,'boundary'):return result
    pw+=_push_marks(vertices['representative_runs'],carriers,0,check)+_push_marks(boundary['representative_runs'],carriers,1,check)
    polygons=weighted_orbit_histogram(g['polygon_points'],pp,pw,dimension=7,max_cycles=remaining,record_certificate=record_certificate,check=check)
    if not allowance(polygons,'polygons'):return result
    dw=[(lo+s*g['polygon_points'],hi+s*g['polygon_points'],v)for lo,hi,v in pw for s in(0,1)]
    double=weighted_orbit_histogram(2*g['polygon_points'],dp,dw,dimension=7,max_cycles=remaining,record_certificate=record_certificate,check=check)
    if not allowance(double,'fibre_cover'):return result
    summary=_summary(g,vertices,boundary,polygons,double,analysed['euler_characteristic'],check)
    result.update(status='COMPLETE',geometry=g,summary=summary)
    if record_certificate:
        result['certificate']=dict(schema='normal-cut-parallelity-v1',input_sha256=_fingerprint(triangulation,analysed,check),
            geometry=g,summary=summary,vertex_selector=vertices['certificate'],boundary_selector=boundary['certificate'],
            polygon_weights=polygons['certificate'],fibre_cover=double['certificate'])
    check();return result
