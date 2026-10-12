"""A rank-minor certificate for a one-vertex coherent normal-surface family.

This bounds only primitive integral coherent-height surfaces on the supplied
triangulation. It is never a negative knot certificate or a topology proof.
"""
from .integer_codec import encoded_integer
from .integer_determinant import bareiss
from .normal_surface_geometry import _prepare,_coordinates,_edge,NormalOrbitError
from .normal_cocycle_verify import _primitive_cochain


def inspect_one_vertex_family(triangulation,certificate,*,check=lambda:None):
    """Return family invariants, or None for an invalid certificate.

    A nonzero (E-1)-minor and a primitive integral kernel vector prove that
    all integral cocycles are its multiples. With one vertex coboundaries
    vanish, so the only primitive coherent vectors come from the two signs.
    Surface connectivity and topology require a separate surface certificate.
    """
    check()
    fields={'schema','heights','coordinates','minor_rows','minor_columns','determinant'}
    if (type(certificate) is not dict or set(certificate)!=fields
            or certificate['schema']!='one-vertex-cocycle-family-v1'):return None
    try:
        p=_prepare(triangulation,check)
        a=_coordinates(p,certificate['coordinates'],check)
    except NormalOrbitError:return None
    if p['vertices']!=1:return None
    supplied=certificate['heights']
    if type(supplied) is not list or len(supplied)!=len(p['tetrahedra']):return None
    h=[]
    for row in supplied:
        check()
        if type(row) is not list or len(row)!=4:return None
        try:h.append([encoded_integer(x) for x in row])
        except ValueError:return None
    values=_primitive_cochain(p,h,True,check)
    if values is None or any(a['weights'][e]!=abs(value) for e,value in values.items()):return None
    labels=sorted(values);index={e:i for i,e in enumerate(labels)};matrix=[]
    faces=p['boundary_faces']+[(t,f) for t,f,u,g,perm in p['pairs']]
    for t,f in faces:
        check();x,y,z=(v for v in range(4) if v!=f);row=[0]*len(labels)
        for v,w,sign in ((x,y,1),(y,z,1),(x,z,-1)):
            local=_edge(t,v,w);row[index[p['edge_roots'][local]]]+=sign*(-1 if p['edge_orientations'][local] else 1)
        if sum(c*values[e] for c,e in zip(row,labels)):return None
        matrix.append(row)
    rr,cc=certificate['minor_rows'],certificate['minor_columns'];rank=len(labels)-1
    for selection,limit in ((rr,len(matrix)),(cc,len(labels))):
        if (type(selection) is not list or len(selection)!=rank
                or any(type(i) is not int or not 0<=i<limit for i in selection)
                or len(set(selection))!=rank):return None
    try:claimed=encoded_integer(certificate['determinant'])
    except ValueError:return None
    if not claimed:return None
    minor=[[matrix[r][c] for c in cc] for r in rr]
    determinant=bareiss(minor,lambda amount:check())
    if determinant!=claimed:return None
    check()
    return dict(cocycle_rank=1,global_edges=len(labels),rank_minor_size=rank,
                primitive_euler_characteristic=a['euler_characteristic'],
                primitive_normal_pieces=a['normal_disks'],
                trust='primitive coherent-height family on this triangulation only')
