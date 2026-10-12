"""Source-cell reconstruction and independent geometric cancellation replay."""
from collections import Counter

from .integer_codec import certificate_equal, encoded_integer
from .normal_parallelity_reference import _reference_parallelity
from .normal_surface_geometry import _prepare, _coordinates, _fingerprint, _EDGES


def verify_source_handle_reduction(triangulation, certificate, *, max_moves=None, check=lambda:None):
    """Check exact geometric incidence multiplicities, then the cocore path.

    No scheduler, source-handle producer or knot recognizer is called. The
    original source and cancellation trace retain the attaching charts.
    """
    check()
    if max_moves is not None and(type(max_moves)is not int or max_moves<0):raise ValueError('max_moves must be nonnegative or None')
    fields={'schema','input_sha256','boundary_pattern','moves','remaining','summary','compressing_disc'}
    if type(certificate)is not dict or set(certificate)!=fields or certificate['schema']!='source-handle-reduction-v1' or certificate['boundary_pattern']!='empty':return False
    moves=certificate['moves']
    if type(moves)is not list or max_moves is not None and len(moves)>max_moves:return False
    p=_prepare(triangulation,check);a=_coordinates(p,[[0]*7 for _ in p['tetrahedra']],check)
    if certificate['input_sha256']!=_fingerprint(triangulation,a,check):return False
    core=_reference_parallelity(p,a,check)['core'];one={r['id']:r for r in core['handles1']};two={r['edge']:r for r in core['handles2']}
    three={r['vertex']for r in core['handles3']};initial=[len(core[f'handles{i}'])for i in range(4)]
    faces=set(one);edges=set(two);vertex_incidence={e:list(p['endpoints'][e])for e in edges}
    for move in moves:
        check()
        if type(move)is not dict:return False
        if move.get('kind')=='cancel_23':
            if set(move)!={'kind','two_handle','three_handle'}:return False
            e,v=move['two_handle'],move['three_handle']
            if type(e)is not int or type(v)is not int or e not in edges or v not in three:return False
            if [w for w in vertex_incidence[e]if w in three]!=[v]:return False
            edges.remove(e);three.remove(v)
        elif move.get('kind')=='cancel_12':
            if three or set(move)!={'kind','one_handle','two_handle'}:return False
            f,e=move['one_handle'],move['two_handle']
            if type(f)is not int or type(e)is not int or f not in faces or e not in edges:return False
            incident=[]
            for edge in sorted(edges):
                for sector in two[edge]['cycle']:
                    check()
                    if sector['dimension']==1 and sector['handle']==f:incident.append(edge)
            if incident!=[e]:return False
            faces.remove(f);edges.remove(e)
        else:return False
    if three:return False
    degree=Counter()
    for e in edges:
        for sector in two[e]['cycle']:
            check()
            if sector['dimension']==1:
                if sector['handle']not in faces:return False
                degree[sector['handle']]+=1
    remaining=dict(one_handles=sorted(faces),two_handles=sorted(edges),three_handles=[])
    summary=dict(initial_handle_counts=initial,remaining_handle_counts=[initial[0],len(faces),len(edges),0],
        characteristic_zero_handle_indices=[dict(one_handle=i,index=-4+2*degree[i],multiplicity=2)for i in sorted(faces)])
    if not certificate_equal(certificate['remaining'],remaining)or not certificate_equal(certificate['summary'],summary):return False
    disc=certificate['compressing_disc']
    if disc is not None:
        if type(disc)is not dict or set(disc)!={'one_handle','connecting_path','boundary_witness'}:return False
        f=disc['one_handle'];path=disc['connecting_path']
        if type(f)is not int or f not in faces or degree[f] or type(path)is not list:return False
        start,target=one[f]['ends'];current=start
        for step in path:
            check()
            if type(step)is not dict or set(step)!={'one_handle','forward'} or type(step['one_handle'])is not int or type(step['forward'])is not bool:return False
            i=step['one_handle']
            if i not in faces or i==f:return False
            left,right=one[i]['ends']
            if not step['forward']:left,right=right,left
            if current!=left:return False
            current=right
        if current!=target:return False
        witness=disc['boundary_witness']
        if type(witness)is not dict or set(witness)!={'dual_values','corner_potentials','boundary_cycle','period'}:return False
        values=witness['dual_values'];potentials=witness['corner_potentials'];cycle=witness['boundary_cycle']
        if type(values)is not list or len(values)!=len(one) or type(potentials)is not list or len(potentials)!=len(p['tetrahedra']):return False
        if any(type(row)is not list or len(row)!=4 for row in potentials)or type(cycle)is not list or not cycle:return False
        try:
            values=list(map(encoded_integer,values));potentials=[list(map(encoded_integer,row))for row in potentials];period=encoded_integer(witness['period'])
        except ValueError:return False
        if not period or any(values[i]!=(1 if i==f else 0)for i in faces):return False
        # Check the extension by source equations, independently of the producer's reverse substitutions.
        for edge in two.values():
            total=0
            for sector in edge['cycle']:
                check()
                if sector['dimension']!=1:continue
                i=sector['handle'];owner=one[i];sign=1 if (sector['tetrahedron'],sector['face'])==(owner['tetrahedron'],owner['face'])else -1
                total+=sign*values[i]
            if total:return False
        for i,face in one.items():
            t,u,opposite,perm=face['tetrahedron'],face['target_tetrahedron'],face['face'],face['permutation']
            for v in range(4):
                check()
                if v!=opposite and potentials[u][perm[v]]-potentials[t][v]!=values[i]:return False
        first=None;current=None;total=0
        for step in cycle:
            check()
            if type(step)is not dict or set(step)!={'edge','forward'} or type(step['edge'])is not int or type(step['forward'])is not bool:return False
            e=step['edge']
            if e not in p['boundary_incidence']:return False
            t,j=divmod(e,6);a,b=_EDGES[j];left,right=p['vertex_roots'][4*t+a],p['vertex_roots'][4*t+b];value=potentials[t][b]-potentials[t][a]
            if not step['forward']:left,right,value=right,left,-value
            if first is None:first=left;current=left
            if current!=left:return False
            current=right;total+=value
        if current!=first or total!=period:return False
    check();return True
