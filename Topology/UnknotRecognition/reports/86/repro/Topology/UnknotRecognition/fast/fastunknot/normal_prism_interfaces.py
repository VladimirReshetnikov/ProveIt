"""Binary prism face regions and source-labelled core interfaces.

Counts face-connected prism blocks, including those attached inside marked
cut components. Ribbon counts concern 0/1-handles only; edge/vertex handles,
full parallelity bundles and ordered boundary curves are not reconstructed.
"""
from bisect import bisect_left
from .interval_orbits import IntervalPairing
from .normal_surface_geometry import _prepare,_coordinates,_quad,_fingerprint
from .weighted_orbits import weighted_orbit_histogram


def _interface_system(prepared,rows,check,port_encoding='vector'):
    cells=[];layout=[];total=0
    for t,row in enumerate(rows):
        check();q=sum(row[4:]);typ=next((j for j in range(3)if row[4+j]),None)
        chain=total;tips=[];by_point={}
        def mark(point,kind,vertex=None):
            index=len(cells);cells.append(dict(id=index,tetrahedron=t,kind=kind,vertex=vertex,chamber=point));by_point[point]=index
        mark(chain,'central'if q==0 else'quad_a')
        if q:mark(chain+q,'quad_b')
        total+=q+1
        for v,count in enumerate(row[:4]):
            check();tips.append(total)
            if count:mark(total,'triangle_tip',v)
            total+=count
        layout.append((chain,tips,q,typ,by_point))
    marks=[c['chamber']for c in cells]
    def compress(point):return point-bisect_left(marks,point)
    def arm(t,f,v):
        chain,tips,q,typ,_=layout[t]
        result=[];tri=rows[t][v]
        if tri:result.append((0,tri,1,tips[v]))
        if typ is not None and _quad(f,v)==typ:
            sign=1 if v in (0,typ+1)else -1
            result.append((tri,tri+q,sign,chain+(0 if sign==1 else q)-sign*tri))
        return result
    def centre(t,f):
        chain,tips,q,typ,_=layout[t]
        return chain+(q if typ is not None and f in (0,typ+1)else 0)
    pairs=[];bands=[];ports=[];core_faces=[]
    def region(t,f,u,g,v,lo,stop,sa,oa,sb,ob):
        check();bad=[]
        for point in layout[t][4]:
            r=sa*(point-oa)
            if lo<=r<stop:bad.append(r)
        for point in layout[u][4]:
            r=sb*(point-ob)
            if lo<=r<stop:bad.append(r)
        cuts=sorted({lo,stop,*bad,*(r+1 for r in bad)})
        for start,end in zip(cuts,cuts[1:]):
            check();left=sa*start+oa;right=sb*start+ob
            lc=layout[t][4].get(left);rc=layout[u][4].get(right)
            location=dict(source_tetrahedron=t,source_face=f,target_tetrahedron=u,target_face=g,corner=v,rank=start)
            if lc is not None or rc is not None:
                if end-start!=1:raise ArithmeticError('exceptional face span not singleton')
                if lc is not None and rc is not None:
                    core_faces.append(dict(location,left_cell=lc,right_cell=rc))
                else:
                    ports.append(dict(location,id=len(ports),core_cell=lc if lc is not None else rc,
                        core_side='source'if lc is not None else'target',prism_point=compress(right if lc is not None else left)))
                continue
            a,aa=compress(left),compress(sa*(end-1)+oa)
            b,bb=compress(right),compress(sb*(end-1)+ob)
            pairs.append(IntervalPairing(min(a,aa),max(a,aa),min(b,bb),max(b,bb),sa!=sb))
            bands.append((min(a,aa),max(a,aa)+1))
    for t,f,u,g,p in prepared['pairs']:
        check();a,b=centre(t,f),centre(u,g)
        region(t,f,u,g,-1,0,1,1,a,1,b)
        for v in range(4):
            if v==f:continue
            pieces=[]
            for lo_a,hi_a,sa,oa in arm(t,f,v):
                for lo_b,hi_b,sb,ob in arm(u,g,p[v]):
                    lo=max(lo_a,lo_b);hi=min(hi_a,hi_b)
                    if lo<hi:pieces.append((lo,hi,sa,oa,sb,ob))
            for lo,hi,sa,oa,sb,ob in sorted(pieces):region(t,f,u,g,v,lo,hi,sa,oa,sb,ob)
    size=total-len(cells)
    if len(cells)>6*len(rows)or len(ports)>24*len(rows):raise ArithmeticError('core interface bound failed')
    bitset=port_encoding=='bitset'or(port_encoding=='auto'and len(ports)>1)
    dimension=3 if bitset else 2+len(ports);weights=[]
    def unit(j):value=[0]*dimension;value[j]=1;return value
    if size:weights.append((0,size,unit(0)))
    for lo,hi in bands:check();weights.append((lo,hi,unit(1)))
    for port in ports:
        check();p=port['prism_point']
        value=[0,0,1<<port['id']]if bitset else unit(2+port['id'])
        weights.append((p,p+1,value))
    structure=dict(core_cells=cells,core_faces=core_faces,ports=ports,prism_points=size)
    return size,pairs,dimension,weights,structure


def _profiles(histogram,ports,check,port_encoding='vector'):
    attached=[];free=[];seen=[]
    bitset=port_encoding=='bitset'or(port_encoding=='auto'and len(ports)>1)
    for row in histogram:
        check();w=row['weight'];copies=row['orbits']
        if w[0]<1 or w[1]<0:raise ArithmeticError('invalid ribbon weight')
        if bitset:
            mask=w[2];indices=[]
            if mask<0 or mask.bit_length()>len(ports):raise ArithmeticError('invalid port bitset')
            while mask:
                check();bit=mask&-mask;indices.append(bit.bit_length()-1);mask-=bit
        else:
            if any(x not in (0,1)for x in w[2:]):raise ArithmeticError('invalid ribbon weight')
            indices=[i for i,x in enumerate(w[2:])if x]
        profile=dict(prism_cells=w[0],face_bands=w[1],ribbon_euler_characteristic=w[0]-w[1])
        if indices:
            if copies!=1:raise ArithmeticError('interface port cannot belong to repeated regions')
            seen.extend(indices);attached.append(dict(profile,ports=indices))
        else:free.append(dict(profile,multiplicity=copies))
    if sorted(seen)!=list(range(len(ports))):raise ArithmeticError('interface partition incomplete')
    attached.sort(key=lambda r:r['ports']);free.sort(key=lambda r:(r['prism_cells'],r['face_bands']))
    return dict(attached_regions=attached,unattached_profiles=free,
        face_attached_components=len(attached),unattached_components=sum(r['multiplicity']for r in free))


def normal_prism_face_regions(triangulation,coordinates,*,max_cycles=None,record_certificate=False,
        port_encoding='auto',check=lambda:None):
    """Recover exact core-face ports and weighted prism-region profiles.

    Ribbon Euler values omit edge/vertex handles; they are not the full base
    Euler values of a maximal parallelity bundle. Source geometry retains the
    existing finite orientable one-torus contract. Caps produce no structure.
    Auto uses one exact additive bitset when there are more than one port;
    vector retains the version-one proof format, bitset uses version two.
    Port uniqueness in the owned source prevents binary carries.
    """
    check()
    if type(record_certificate)is not bool:raise ValueError('record_certificate must be bool')
    if port_encoding not in ('auto','vector','bitset'):raise ValueError('invalid port_encoding')
    if max_cycles is not None and(type(max_cycles)is not int or max_cycles<0):raise ValueError('invalid max_cycles')
    prepared=_prepare(triangulation,check);analysed=_coordinates(prepared,coordinates,check)
    size,pairs,d,weights,structure=_interface_system(prepared,analysed['rows'],check,port_encoding)
    query=weighted_orbit_histogram(size,pairs,weights,dimension=d,max_cycles=max_cycles,check=check,record_certificate=record_certificate)
    result=dict(status=query['status'],tetrahedra=len(analysed['rows']),interval_pairings=len(pairs),weight_dimension=d,stats=query['stats'],
        trust='source-labelled prism face connectivity and 0/1-handle profiles; not a full parallelity bundle or knot verdict')
    if query['status']!='COMPLETE':return result
    structure.update(_profiles(query['histogram'],structure['ports'],check,port_encoding))
    result['structure']=structure
    if query['orbit_count']!=structure['face_attached_components']+structure['unattached_components']:
        raise ArithmeticError('prism region total disagrees')
    bitset=port_encoding=='bitset'or(port_encoding=='auto'and len(structure['ports'])>1)
    if record_certificate:result['certificate']=dict(schema='normal-prism-interfaces-v2'if bitset else'normal-prism-interfaces-v1',
        input_sha256=_fingerprint(triangulation,analysed,check),structure=structure,weighted_certificate=query['certificate'])
    check();return result
