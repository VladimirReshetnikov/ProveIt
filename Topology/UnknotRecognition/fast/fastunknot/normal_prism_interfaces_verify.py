"""Independent source-face clipping and core-interface partition replay."""
from bisect import bisect_left
from .normal_surface_geometry import _prepare,_coordinates,_fingerprint
from .integer_codec import encoded_integer,certificate_equal
from .weighted_orbit_verify import verify_weighted_orbit_certificate


def _reference_interface_system(prepared,rows,check):
    cells=[];chains=[];tips=[];quads=[];local=[];offset=0
    for t,row in enumerate(rows):
        check();q=sum(row[4:]);quads.append(next((j for j in range(3)if row[4+j]),None));chains.append(offset)
        owned={}
        records=[(offset,'central'if q==0 else'quad_a',None)]
        if q:records.append((offset+q,'quad_b',None))
        offset+=q+1;corners=[]
        for v in range(4):
            corners.append(offset)
            if row[v]:records.append((offset,'triangle_tip',v))
            offset+=row[v]
        tips.append(corners)
        for point,kind,v in records:
            index=len(cells);owned[point]=index
            cells.append(dict(id=index,tetrahedron=t,kind=kind,vertex=v,chamber=point))
        local.append(owned)
    removed=sorted(c['chamber']for c in cells);size=offset-len(removed)
    def shifted(p):return p-bisect_left(removed,p)
    def face(t,f):
        check();kind=quads[t];q=sum(rows[t][4:]);parts={}
        if kind is None:single=None;centre=chains[t]
        elif f in (0,kind+1):single=kind+1 if f==0 else 0;centre=chains[t]+q
        else:single=next(v for v in range(4)if v not in (0,kind+1,f));centre=chains[t]
        for v in range(4):
            if v==f:continue
            m=rows[t][v];part=[]
            if m:part.append((0,m,1,tips[t][v]))
            if v==single:
                sign=1 if v in (0,kind+1)else -1
                part.append((m,m+q,sign,chains[t]+(q if sign<0 else 0)-sign*m))
            parts[v]=part
        return centre,parts
    pairs=[];bands=[];ports=[];contacts=[]
    def piece(t,f,u,g,v,lo,end,sa,oa,sb,ob):
        events={}
        for p in local[t]:
            rank=sa*(p-oa)
            if lo<=rank<end:events[rank]=True
        for p in local[u]:
            rank=sb*(p-ob)
            if lo<=rank<end:events[rank]=True
        def gap(a,b):
            check()
            left=sorted((shifted(sa*a+oa),shifted(sa*(b-1)+oa)))
            right=sorted((shifted(sb*a+ob),shifted(sb*(b-1)+ob)))
            bands.append((left[0],left[1]+1))
            if right[0]<left[0]:left,right=right,left
            pairs.append([*left,*right,1 if sa==sb else -1])
        start=lo
        for rank in sorted(events):
            check()
            if start<rank:gap(start,rank)
            a,b=sa*rank+oa,sb*rank+ob;lc=local[t].get(a);rc=local[u].get(b)
            location=dict(source_tetrahedron=t,source_face=f,target_tetrahedron=u,target_face=g,corner=v,rank=rank)
            if lc is not None and rc is not None:contacts.append(dict(location,left_cell=lc,right_cell=rc))
            else:ports.append(dict(location,id=len(ports),core_cell=lc if lc is not None else rc,
                core_side='source'if lc is not None else'target',prism_point=shifted(b if lc is not None else a)))
            start=rank+1
        if start<end:gap(start,end)
    for t,f,u,g,p in prepared['pairs']:
        check();a,left=face(t,f);b,right=face(u,g)
        piece(t,f,u,g,-1,0,1,1,a,1,b)
        for v in sorted(left):
            overlap=[]
            for a,b,sa,oa in left[v]:
                for c,d,sb,ob in right[p[v]]:
                    lo,end=max(a,c),min(b,d)
                    if lo<end:overlap.append((lo,end,sa,oa,sb,ob))
            for lo,end,sa,oa,sb,ob in sorted(overlap):piece(t,f,u,g,v,lo,end,sa,oa,sb,ob)
    d=2+len(ports);weights=[]
    def indicator(i):value=[0]*d;value[i]=1;return value
    if size:weights.append((0,size,indicator(0)))
    for lo,end in bands:check();weights.append((lo,end,indicator(1)))
    for port in ports:
        check();p=port['prism_point'];weights.append((p,p+1,indicator(2+port['id'])))
    return size,pairs,d,weights,dict(core_cells=cells,core_faces=contacts,ports=ports,prism_points=size)


def verify_normal_prism_interfaces(triangulation,coordinates,certificate,*,max_operations=None,check=lambda:None):
    """Verify every source-labelled port and weighted 0/1-handle profile.

    Invalid input geometry raises NormalOrbitError. Malformed proofs return
    False; external cancellation propagates. A replay limit is unverified,
    never a parallelity or knot conclusion.
    """
    check()
    if max_operations is not None and(type(max_operations)is not int or max_operations<0):raise ValueError('invalid max_operations')
    if(type(certificate)is not dict or set(certificate)!={'schema','input_sha256','structure','weighted_certificate'}
            or certificate.get('schema')!='normal-prism-interfaces-v1'):return False
    prepared=_prepare(triangulation,check);analysed=_coordinates(prepared,coordinates,check)
    if certificate['input_sha256']!=_fingerprint(triangulation,analysed,check):return False
    proof=certificate['weighted_certificate']
    if type(proof)is not dict or type(proof.get('orbit_proof'))is not dict:return False
    trace=proof['orbit_proof']
    if type(trace.get('operations'))is not list:return False
    if max_operations is not None and len(trace['operations'])>max_operations:return False
    size,pairs,d,weights,expected=_reference_interface_system(prepared,analysed['rows'],check)
    if len(expected['core_cells'])>6*len(analysed['rows'])or len(expected['ports'])>24*len(analysed['rows']):return False
    if not verify_weighted_orbit_certificate(size,pairs,weights,proof,dimension=d,check=check):return False
    attached=[];free=[];seen=[]
    for row in proof['histogram']:
        check();w=[encoded_integer(x)for x in row['weight']];copies=encoded_integer(row['orbits'])
        if w[0]<1 or w[1]<0 or any(x not in (0,1)for x in w[2:]):return False
        profile=dict(prism_cells=w[0],face_bands=w[1],ribbon_euler_characteristic=w[0]-w[1])
        ports=[i for i,x in enumerate(w[2:])if x]
        if ports:
            if copies!=1:return False
            seen.extend(ports);attached.append(dict(profile,ports=ports))
        else:free.append(dict(profile,multiplicity=copies))
    if sorted(seen)!=list(range(len(expected['ports']))):return False
    attached.sort(key=lambda r:r['ports']);free.sort(key=lambda r:(r['prism_cells'],r['face_bands']))
    expected.update(attached_regions=attached,unattached_profiles=free,face_attached_components=len(attached),
        unattached_components=sum(r['multiplicity']for r in free))
    return certificate_equal(certificate['structure'],expected)
