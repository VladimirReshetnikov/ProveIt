"""Independent relative-boundary replay of a supplied 3-2 replacement."""
from .normal_surface_geometry import _prepare, NormalOrbitError
from .pachner23_verify import _boundary_signature


def verify_pachner_32(before,after,certificate,*,check=lambda:None):
    check()
    if (type(certificate) is not dict or set(certificate) != {'schema','region'}
            or certificate['schema'] != 'pachner-32-v1'
            or type(certificate['region']) is not list or len(certificate['region']) != 3):
        return False
    try:
        a = _prepare(before,check)['tetrahedra']
        b = _prepare(after,check)['tetrahedra']
    except NormalOrbitError:
        return False
    if len(b) != len(a)-1:return False
    region = {}
    for item in certificate['region']:
        if type(item) is not dict or set(item) != {'tetrahedron','vertices'}:return False
        t,row = item['tetrahedron'],item['vertices']
        if (type(t) is not int or not 0 <= t < len(a) or t in region
                or type(row) is not list or len(row) != 4
                or any(type(v) is not int or not 0 <= v < 5 for v in row)
                or len(set(row)) != 4):return False
        region[t] = row
    expected = {frozenset((3,4,0,1)),frozenset((3,4,1,2)),frozenset((3,4,2,0))}
    if {frozenset(row) for row in region.values()} != expected:return False
    survivors = [t for t in range(len(a)) if t not in region]
    index = {t:i for i,t in enumerate(survivors)}
    start = len(survivors)
    for t in survivors:
        check()
        for f,r in enumerate(a[t]):
            actual = b[index[t]][f]
            if r is None:
                if actual is not None:return False
            elif r['tetrahedron'] not in region:
                if actual != dict(tetrahedron=index[r['tetrahedron']],permutation=r['permutation']):return False
    old = _boundary_signature(a,region,{t:t for t in survivors},check)
    new = _boundary_signature(b,{start:(0,1,2,3),start+1:(0,1,2,4)},
                              {i:t for i,t in enumerate(survivors)},check)
    check()
    return old is not None and len(old) == 6 and old == new
