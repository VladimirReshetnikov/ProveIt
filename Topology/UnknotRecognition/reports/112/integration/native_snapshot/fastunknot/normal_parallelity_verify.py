"""Independent source-core reconstruction and complete parallelity proof replay."""
from .integer_codec import encoded_integer,certificate_equal
from .interval_orbits import IntervalPairing
from .normal_surface_geometry import _prepare,_coordinates,_fingerprint
from .normal_parallelity_reference import _reference_parallelity
from .weighted_transversal_verify import verify_weighted_orbit_transversal
from .weighted_orbit_verify import verify_weighted_orbit_certificate


def _isometry(left,right,lo,hi):
    s,o=left;t,p=right;domain=sorted((s*lo+o,s*(hi-1)+o));image=sorted((t*lo+p,t*(hi-1)+p))
    return IntervalPairing(*domain,*image,s!=t)


def _reference_queries(g,check):
    vp=[];pp=[];dp=[];weights=[];vertex_weights=[];carriers=[];polygons=g['polygons'];n=g['polygon_points']
    for p in polygons:
        check();degree=len(p['vertices']);coordinate={'prism':2,'face_strip':3,'edge_cap':4}[p['kind']]
        value=[0]*7;value[0]=1-degree;value[coordinate]=1;weights.append((p['start'],p['stop'],value))
        for start in p['corner_starts']:carriers.append((start,start+p['stop']-p['start'],p['start']))
    for link in g['gluings']:
        check();lo,hi=link['rank_start'],link['rank_stop'];a,b=link['left_map'],link['right_map'];p,q=polygons[link['left']],polygons[link['right']]
        pp.append(_isometry(a,b,lo,hi));domain=sorted((a[0]*lo+a[1],a[0]*(hi-1)+a[1]))
        weights.append((domain[0],domain[1]+1,[1,0,0,0,0,0,0]))
        for corner in(0,1):
            left=(link['left_edge']+corner)%len(p['vertices']);right=(link['right_edge']+(1-corner if link['ends_reverse']else corner))%len(q['vertices'])
            vp.append(_isometry((a[0],a[1]+p['corner_starts'][left]-p['start']),(b[0],b[1]+q['corner_starts'][right]-q['start']),lo,hi))
        for sheet in(0,1):
            target=1-sheet if link['fibre_flip']else sheet
            dp.append(_isometry((a[0],a[1]+sheet*n),(b[0],b[1]+target*n),lo,hi))
    bp=list(vp)
    for edge in g['free_edges']:
        check();p=polygons[edge['polygon']];lo,hi=edge['rank_start'],edge['rank_stop'];a=p['corner_starts'][edge['edge']]-1;b=p['corner_starts'][(edge['edge']+1)%len(p['vertices'])]-1
        bp.append(_isometry((1,a),(1,b),lo,hi))
        marker=0 if edge['original_boundary']else 1
        vertex_weights.extend([(a+lo,a+hi,[1,marker]),(b+lo,b+hi,[1,marker])])
        value=[0]*7;value[5 if edge['original_boundary']else 6]=1 if edge['original_boundary']else 2**edge['port']
        weights.append((p['start']+lo-1,p['start']+hi-1,value))
    return vp,bp,vertex_weights,pp,weights,dp,sorted(carriers)


def _reference_marks(selector,carriers,coordinate,check):
    answer=[]
    for row in selector['representative_runs']:
        check();lo,hi=encoded_integer(row['start']),encoded_integer(row['stop'])
        if coordinate==1 and encoded_integer(row['weight'][0])==0:continue
        for first,last,target in carriers:
            a,b=max(lo,first),min(hi,last)
            if a<b:
                value=[0]*7;value[coordinate]=1;answer.append((target+a-first,target+b-first,value))
    return answer


def _reference_summary(g,vertex,boundary,base,cover,cut_chi,check):
    counts={tuple(map(encoded_integer,r['weight'])):encoded_integer(r['orbits'])for r in base['histogram']}
    doubled={tuple(map(encoded_integer,r['weight'])):encoded_integer(r['orbits'])for r in cover['histogram']}
    nonorientable={};profiles=[];seen=[]
    for w in sorted(set(counts)|set(doubled),key=lambda w:(sum(w[2:5]),w)):
        check()
        if sum(w[2:5])<1:return None
        half=tuple(x//2 for x in w)if not any(x%2 for x in w)else None
        product_twice=doubled.get(w,0)-nonorientable.get(half,0)
        if product_twice<0 or product_twice%2:return None
        product=product_twice//2;twisted=counts.get(w,0)-product
        if twisted<0:return None
        nonorientable[w]=twisted
        if not product and not twisted:continue
        chi,b,h0,h1,h2,old,mask=w
        if b<0 or old<0 or mask<0 or mask.bit_length()>len(g['ports']):return None
        ports=[i for i,digit in enumerate(format(mask,'b')[::-1])if digit=='1']
        if ports:
            if product+twisted!=1:return None
            seen.extend(ports)
        complexity=2-b-chi
        for orientable,multiplicity in((True,product),(False,twisted)):
            if not multiplicity:continue
            if orientable and(complexity<0 or complexity%2)or not orientable and complexity<1:return None
            profiles.append(dict(euler_characteristic=chi,boundary_components=b,orientable=orientable,
                genus=complexity//2 if orientable else None,crosscaps=None if orientable else complexity,product=orientable,
                multiplicity=multiplicity,handles=[h0,h1,h2],original_boundary_edges=old,core_ports=ports))
    if sorted(seen)!=list(range(len(g['ports']))):return None
    core=[len(g['core'][f'handles{i}'])for i in range(4)];core_chi=core[0]-core[1]+core[2]-core[3]
    base_chi=sum(p['multiplicity']*p['euler_characteristic']for p in profiles)
    attachment_vertices=sum(encoded_integer(r['stop'])-encoded_integer(r['start'])for r in vertex['representative_runs']if encoded_integer(r['weight'][1]))
    attachment_chi=attachment_vertices-len(g['ports'])
    bcount=sum(encoded_integer(r['stop'])-encoded_integer(r['start'])for r in boundary['representative_runs']if encoded_integer(r['weight'][0]))
    if core_chi+base_chi-attachment_chi!=cut_chi or bcount!=sum(p['multiplicity']*p['boundary_components']for p in profiles):return None
    return dict(bundle_components=sum(p['multiplicity']for p in profiles),base_profiles=profiles,
                core_handle_counts=core,core_euler_characteristic=core_chi,bundle_euler_characteristic=base_chi,
                attachment_euler_characteristic=attachment_chi,core_attachment_vertices=attachment_vertices)


def verify_normal_cut_parallelity(triangulation,coordinates,certificate,*,max_operations=None,check=lambda:None):
    """Authenticate source handles, base topology, fibre cover and core interfaces.

    The operation cap counts the four supplied discovery traces. It returns
    unverified on exhaustion. Malformed proofs return False, source geometry
    errors raise NormalOrbitError, and callback exceptions propagate.
    """
    check()
    if max_operations is not None and(type(max_operations)is not int or max_operations<0):raise ValueError('max_operations must be nonnegative or None')
    keys={'schema','input_sha256','geometry','summary','vertex_selector','boundary_selector','polygon_weights','fibre_cover'}
    if type(certificate)is not dict or set(certificate)!=keys or certificate['schema']!='normal-cut-parallelity-v1':return False
    traces=[]
    for field in('vertex_selector','boundary_selector','polygon_weights','fibre_cover'):
        proof=certificate[field]
        if type(proof)is not dict:return False
        if field.endswith('selector'):
            proof=proof.get('weighted_certificate')
            if type(proof)is not dict:return False
        trace=proof.get('orbit_proof')
        if type(trace)is not dict or type(trace.get('operations'))is not list:return False
        traces.append(trace['operations'])
    if max_operations is not None and sum(map(len,traces))>max_operations:return False
    prepared=_prepare(triangulation,check);analysed=_coordinates(prepared,coordinates,check)
    if certificate['input_sha256']!=_fingerprint(triangulation,analysed,check):return False
    g=_reference_parallelity(prepared,analysed,check)
    if not certificate_equal(certificate['geometry'],g):return False
    if any(len(g['core'][f'handles{i}']) > bound*len(coordinates) for i,bound in enumerate((6,8,12,4))):return False
    if len(g['ports'])>66*len(coordinates):return False
    vp,bp,vw,pp,pw,dp,carriers=_reference_queries(g,check);v,b,p,d=[certificate[k]for k in('vertex_selector','boundary_selector','polygon_weights','fibre_cover')]
    if not verify_weighted_orbit_transversal(g['corner_points'],vp,vw,v,dimension=2,check=check):return False
    if not verify_weighted_orbit_transversal(g['corner_points'],bp,vw,b,dimension=2,check=check):return False
    pw+=_reference_marks(v,carriers,0,check)+_reference_marks(b,carriers,1,check)
    if not verify_weighted_orbit_certificate(g['polygon_points'],pp,pw,p,dimension=7,check=check):return False
    weights=[(lo+sheet*g['polygon_points'],hi+sheet*g['polygon_points'],value)for lo,hi,value in pw for sheet in(0,1)]
    if not verify_weighted_orbit_certificate(2*g['polygon_points'],dp,weights,d,dimension=7,check=check):return False
    expected=_reference_summary(g,v,b,p,d,analysed['euler_characteristic'],check)
    return expected is not None and certificate_equal(certificate['summary'],expected)
