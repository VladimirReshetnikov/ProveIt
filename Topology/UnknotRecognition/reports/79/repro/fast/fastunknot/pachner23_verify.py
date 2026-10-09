"""Independent relative-boundary check of a canonical 2-3 replacement.

Compare formal bipyramid boundary gluings and the unchanged exterior. No
replacement producer or external topology engine is imported.
"""
from .normal_surface_geometry import _prepare,NormalOrbitError


def _boundary_signature(rows,region,outside,check):
    occurrences={}
    for t,labels in region.items():
        for f in range(4):
            key=tuple(sorted(labels[v] for v in range(4) if v!=f))
            occurrences.setdefault(key,[]).append((t,f))
    answer={}
    for key,where in occurrences.items():
        check()
        if len(where)==2:
            (t,f),(u,g)=where;r=rows[t][f]
            if (r is None or r['tetrahedron']!=u or r['permutation'][f]!=g
                    or any(region[t][v]!=region[u][r['permutation'][v]] for v in range(4) if v!=f)):
                return None
            continue
        if len(where)!=1:return None
        t,f=where[0];r=rows[t][f]
        if r is None:answer[key]=('boundary',);continue
        u,p=r['tetrahedron'],r['permutation'];g=p[f]
        if u in region:
            target=tuple(sorted(region[u][v] for v in range(4) if v!=g))
            mapping=tuple(sorted((region[t][v],region[u][p[v]]) for v in range(4) if v!=f))
            answer[key]=('region',target,mapping)
        else:
            mapping=tuple(sorted((region[t][v],p[v]) for v in range(4) if v!=f))
            answer[key]=('outside',outside[u],g,mapping)
    return answer


def verify_pachner_23(before,after,certificate,*,check=lambda:None):
    """Check a relative-boundary replacement, including ambient identifications."""
    check()
    if (type(certificate) is not dict or set(certificate)!={'schema','tetrahedron','face'}
            or certificate['schema']!='pachner-23-v1'
            or type(certificate['tetrahedron']) is not int or type(certificate['face']) is not int):return False
    try:
        a=_prepare(before,check)['tetrahedra'];b=_prepare(after,check)['tetrahedra']
    except NormalOrbitError:return False
    t,f=certificate['tetrahedron'],certificate['face']
    if not 0<=t<len(a) or not 0<=f<4 or len(b)!=len(a)+1:return False
    r=a[t][f]
    if r is None or r['tetrahedron']==t:return False
    u,p=r['tetrahedron'],r['permutation'];g=p[f]
    shared=[v for v in range(4) if v!=f]
    left=[shared.index(v) if v!=f else 3 for v in range(4)]
    right=[left[p.index(v)] if v!=g else 4 for v in range(4)]
    old_region={t:left,u:right};survivors=[v for v in range(len(a)) if v not in old_region]
    lookup={v:i for i,v in enumerate(survivors)};start=len(survivors)
    new_region={start:[3,4,0,1],start+1:[3,4,1,2],start+2:[3,4,2,0]}
    for v in survivors:
        check()
        for f,r in enumerate(a[v]):
            s=b[lookup[v]][f]
            if r is None:
                if s is not None:return False
            elif r['tetrahedron'] not in old_region:
                if s!=dict(tetrahedron=lookup[r['tetrahedron']],permutation=r['permutation']):return False
    old=_boundary_signature(a,old_region,{v:v for v in survivors},check)
    new=_boundary_signature(b,new_region,{i:v for i,v in enumerate(survivors)},check)
    check()
    return old is not None and len(old)==6 and old==new
