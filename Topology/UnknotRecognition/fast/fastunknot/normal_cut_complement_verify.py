"""Independent cut-chamber construction and orbit-trace replay.

Shares the established manifold and normal-coordinate validation boundary.
Does not import the complement producer or any orbit planner. Its affine
face-region intersections are reconstructed from the actual source geometry.
"""
from .integer_codec import encoded_integer
from .interval_orbit_verify import verify_orbit_certificate
from .normal_surface_geometry import _prepare,_coordinates,_fingerprint


def _reference_chambers(prepared,rows,check):
    chains=[];tips=[];types=[];size=0
    for row in rows:
        check();chains.append(size);size+=1+sum(row[4:])
        offsets=[]
        for count in row[:4]:check();offsets.append(size);size+=count
        tips.append(offsets);types.append(next((q for q in range(3)if row[4+q]),None))

    def face(t,f):
        check();typ=types[t];length=sum(rows[t][4:]);parts={}
        if typ is None:singleton=None;centre=chains[t]
        else:
            side=(0,typ+1)
            if f in side:
                singleton=next(v for v in side if v!=f);centre=chains[t]+length
            else:
                singleton=next(v for v in range(4)if v not in side and v!=f);centre=chains[t]
        for v in range(4):
            check()
            if v==f:continue
            count=rows[t][v];segments=[]
            if count:segments.append((0,count,1,tips[t][v]))
            if v==singleton:
                direction=1 if v in (0,typ+1)else -1
                intercept=chains[t]+(0 if direction==1 else length)-direction*count
                segments.append((count,count+length,direction,intercept))
            parts[v]=segments
        return centre,parts

    result=[]
    def emit(low,stop,sign_a,offset_a,sign_b,offset_b):
        a,aa=sign_a*low+offset_a,sign_a*(stop-1)+offset_a
        b,bb=sign_b*low+offset_b,sign_b*(stop-1)+offset_b
        left,right=sorted((a,aa)),sorted((b,bb))
        if right[0]<left[0]:left,right=right,left
        return [*left,*right,1 if sign_a==sign_b else -1]

    for t,f,u,g,p in prepared['pairs']:
        check();a,left=face(t,f);b,right=face(u,g)
        result.append([min(a,b),min(a,b),max(a,b),max(a,b),1])
        for v in sorted(left):
            check();pieces=[]
            for low_a,end_a,sa,oa in left[v]:
                for low_b,end_b,sb,ob in right[p[v]]:
                    check();low=max(low_a,low_b);end=min(end_a,end_b)
                    if low<end:pieces.append((low,emit(low,end,sa,oa,sb,ob)))
            result.extend(row for _,row in sorted(pieces))
    return size,result


def verify_normal_complement_certificate(triangulation,coordinates,certificate,*,
        max_operations=None,check=lambda:None):
    """Verify the supplied cut-component count without rerunning any search.

    Invalid source geometry raises NormalOrbitError, as in existing native
    topology checkers. Malformed certificates return False. Operation bounds
    are verification limits, never component or recognition conclusions.
    """
    check()
    if max_operations is not None and(type(max_operations)is not int or max_operations<0):
        raise ValueError('max_operations must be a nonnegative integer or None')
    if(type(certificate)is not dict or set(certificate)!={'schema','input_sha256','cut_components','orbit_certificate'}
            or certificate.get('schema')!='normal-cut-components-v1'):return False
    prepared=_prepare(triangulation,check);analysed=_coordinates(prepared,coordinates,check)
    if certificate['input_sha256']!=_fingerprint(triangulation,analysed,check):return False
    trace=certificate['orbit_certificate']
    if type(trace)is not dict or type(trace.get('operations'))is not list:return False
    if max_operations is not None and len(trace['operations'])>max_operations:return False
    try:
        claimed=encoded_integer(certificate['cut_components'])
        orbit_count=encoded_integer(trace.get('orbit_count'))
    except (ValueError,TypeError):return False
    if claimed<1 or claimed!=orbit_count:return False
    size,pairs=_reference_chambers(prepared,analysed['rows'],check)
    return verify_orbit_certificate(size,pairs,trace,check=check)
