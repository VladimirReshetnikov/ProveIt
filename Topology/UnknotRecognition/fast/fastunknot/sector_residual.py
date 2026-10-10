"""Exact signed-residual filtering of radius-one/two compatible sector windows.

This is a positive source-surface search. Window failure is inconclusive for
a knot diagram. The residual filter covers the full type-assignment window:
deletions are dominated by the base sector, and positive nonbase coordinates
must be zero residuals or an oppositely signed proportional pair.
"""
from fractions import Fraction
from itertools import combinations,product
from math import gcd,lcm

from .normal_surface_geometry import _prepare,_coordinates
from .normal_sector import sector_rays
from .sector_sparse import PreparedSectorSource
from .normal_disk_kernel import _count_prepared_discs,_DiskCertificateVerifier


def _add(vector,other,scale,check):
    result=vector.copy()
    for i,value in other.items():
        check()
        result[i]=result.get(i,0)+scale*value
        if not result[i]:del result[i]
    return result


def _projective(vector,check):
    if not vector:return (),0
    denominator=1
    for value in vector.values():
        check();denominator=lcm(denominator,value.denominator)
    integers={i:int(value*denominator)for i,value in vector.items()}
    divisor=0
    for value in integers.values():check();divisor=gcd(divisor,value)
    sign=1 if integers[min(integers)]>0 else -1
    return tuple((i,value//(divisor*sign))for i,value in sorted(integers.items())),sign


def _full_quad_columns(prepared,check,retain_potentials=False):
    """Eliminate triangle incidence by a sparse forest, keeping all Q types."""
    count=len(prepared['tetrahedra']);adjacency=[[]for _ in range(4*count)]
    edges=[];constraints=[]
    for equation in prepared['matching']:
        check()
        triangles={4*(i//7)+i%7:value for i,value in equation.items()if i%7<4}
        label={3*(i//7)+i%7-4:value for i,value in equation.items()if i%7>=4}
        if not triangles:
            constraints.append(label);continue
        if len(triangles)!=2 or sorted(triangles.values())!=[-1,1]:
            raise ArithmeticError('unexpected triangle incidence equation')
        a=next(i for i,v in triangles.items()if v==1)
        b=next(i for i,v in triangles.items()if v==-1)
        edges.append((a,b,label));adjacency[a].append((b,label))
        adjacency[b].append((a,{i:-v for i,v in label.items()}))
    potentials=[None]*(4*count)
    for start in range(4*count):
        check()
        if potentials[start]is not None:continue
        potentials[start]={};queue=[start]
        for a in queue:
            check()
            for b,label in adjacency[a]:
                if potentials[b]is None:
                    potentials[b]=_add(potentials[a],label,1,check);queue.append(b)
    for a,b,label in edges:
        check()
        row=_add(_add(potentials[b],potentials[a],-1,check),label,-1,check)
        if row:constraints.append(row)
    rows=sorted({_projective(row,check)[0]for row in constraints if row})
    columns=[{}for _ in range(3*count)]
    for r,row in enumerate(rows):
        check()
        for i,value in row:columns[i][r]=value
    return (columns,len(rows),potentials)if retain_potentials else (columns,len(rows))


def _reduce(vector,basis,check):
    for pivot,row in sorted(basis.items()):
        check()
        if pivot in vector:vector=_add(vector,row,-vector[pivot],check)
    return vector


def _reduce_with_coefficients(vector,basis,representations,check):
    coefficients={}
    for pivot,row in sorted(basis.items()):
        check()
        if pivot in vector:
            value=vector[pivot]
            vector=_add(vector,row,-value,check)
            coefficients=_add(coefficients,representations[pivot],value,check)
    return vector,coefficients


def _signature(rows):
    return tuple(next((q for q in range(3)if row[4+q]),-1)for row in rows)


def _plan_window(prepared,rows,radius,check,base_basis=None):
    base=_signature(rows);basis={};representations={}
    if base_basis is None:columns,count=_full_quad_columns(prepared,check)
    else:columns,count,potentials=_full_quad_columns(prepared,check,True)
    selected=tuple((t,q)for t,q in enumerate(base)if q>=0)
    for index,(t,q) in enumerate(selected):
        check()
        if base_basis is None:vector=_reduce(columns[3*t+q],basis,check)
        else:vector,coefficients=_reduce_with_coefficients(columns[3*t+q],basis,representations,check)
        if vector:
            pivot=min(vector);scale=Fraction(vector[pivot])
            basis[pivot]={i:value/scale for i,value in vector.items()}
            if base_basis is not None:
                combination=_add({index:1},coefficients,-1,check)
                representations[pivot]={i:value/scale for i,value in combination.items()}
    zero=[];groups={}
    residuals={};coefficients_by_type={}
    for t,q in product(range(len(base)),range(3)):
        check()
        if q==base[t]:continue
        if base_basis is None:vector=_reduce(columns[3*t+q],basis,check)
        else:
            vector,coefficients=_reduce_with_coefficients(columns[3*t+q],basis,representations,check)
            residuals[t,q]=vector;coefficients_by_type[t,q]=coefficients
        key,sign=_projective(vector,check)
        if not key:zero.append((t,q))
        else:groups.setdefault(key,{1:[],-1:[]})[sign].append((t,q))
    opposite=[];zero_pairs=[]
    if radius==2:
        for group in groups.values():
            for a,b in product(group[1],group[-1]):
                check()
                if a[0]!=b[0]:opposite.append(tuple(sorted((a,b))))
        for a,b in combinations(zero,2):
            check()
            if a[0]!=b[0]:zero_pairs.append((a,b))
    opposite=sorted(set(opposite));zero_pairs=sorted(zero_pairs)
    edits=[()] + [(item,)for item in zero]+opposite+zero_pairs
    plan=dict(base_types=base,edits=edits,stats=dict(radius=radius,
        global_cycle_rows=count,base_rank=len(basis),
        base_nullity=sum(q>=0 for q in base)-len(basis),
        zero_columns=len(zero),projective_groups=len(groups),opposite_pairs=len(opposite),
        zero_pairs=len(zero_pairs),candidate_sectors=len(edits)))
    if base_basis is not None:
        from .sector_window_basis import WindowBasis
        plan['_matching_updates']=WindowBasis(selected,base_basis,residuals,coefficients_by_type,potentials)
    return plan


def plan_sector_window(triangulation,coordinates,*,radius=2,check=lambda:None):
    """Plan a complete radius-one/two type window from an actual normal vector."""
    if type(radius)is not int or radius not in (1,2):
        raise ValueError('sector window radius must be one or two')
    prepared=_prepare(triangulation,check);rows=_coordinates(prepared,coordinates,check)['rows']
    return _plan_window(prepared,rows,radius,check)


def search_sector_window(triangulation,coordinates,*,radius=2,max_cycles=None,
                         check=lambda:None,stats=None):
    """Find an independently replayed disc in the full small type window.

    Callback work and orbit-cycle allowances are shared across all sectors.
    A positive proof is a normal-disc-count proof on the supplied source;
    the caller must separately authenticate any input-diagram relationship.
    No negative knot certificate is produced, even after complete exhaustion.
    """
    if type(radius)is not int or radius not in (1,2):
        raise ValueError('sector window radius must be one or two')
    if max_cycles is not None and (type(max_cycles)is not int or max_cycles<0):
        raise ValueError('invalid orbit allowance')
    if stats is None:stats={}
    stats.update(radius=radius,sectors_queried=0,rays=0,orbit_cycles=0,
                 incomplete_disc_queries=0,window_complete=False,full_basis_builds=0,basis_updates=0,
                 euler_screens=0,euler_corners=0,euler_pruned_sectors=0,
                 base_potential_builds=0,potential_transpositions=0,potential_columns_cached=0,mode_projections=0)
    source=PreparedSectorSource(triangulation,check=check)
    rows=_coordinates(source.prepared,coordinates,check)['rows'];base=_signature(rows)
    base_kernel=None;source_euler=None;disc_verifier=None
    def query(edits,matching_basis=None,matching_model=None,projection=None):
        nonlocal base_kernel,disc_verifier
        signature=list(base)
        for t,q in edits:signature[t]=q
        allowed=[(t,q)for t,q in enumerate(signature)if q>=0]
        if matching_basis is None:
            kernel=source.build(allowed,check=check);stats['full_basis_builds']+=1
        else:
            stats['basis_updates']+=1
            if not matching_basis:
                stats['sectors_queried']+=1
                return None
            if len(matching_basis)==1 and any(x<0 for x in matching_basis[0]):
                stats['euler_screens']+=1;stats['euler_pruned_sectors']+=1
                stats['sectors_queried']+=1
                return None
            from .sector_window_basis import projected_window_kernel
            forms=matching_model.project_modes(projection,check,stats)
            if source_euler.excludes_positive(allowed,matching_basis,forms,check,stats):
                stats['sectors_queried']+=1
                return None
            kernel=projected_window_kernel(triangulation,source.prepared,allowed,matching_basis,
                matching_model.potentials,check,corner_forms=forms)
        if not edits:base_kernel=kernel
        stats['sectors_queried']+=1
        if len(kernel.basis)==3:
            from .sector_planar import sector_planar_discovery_rays
            candidates=sector_planar_discovery_rays(kernel,check=check)
        else:candidates=sector_rays(kernel,check=check)
        for vector in candidates:
            check();stats['rays']+=1
            analysed=_coordinates(source.prepared,vector,check)
            if analysed['euler_characteristic']<=0:continue
            remaining=None if max_cycles is None else max_cycles-stats['orbit_cycles']
            count=_count_prepared_discs(triangulation,source.prepared,analysed,max_cycles=remaining,
                check=check,record_certificate=True)
            stats['orbit_cycles']+=count['stats']['orbit_cycles']
            if count['status']!='COMPLETE':
                stats['incomplete_disc_queries']+=1;continue
            proof=count['certificate']
            if disc_verifier is None:disc_verifier=_DiskCertificateVerifier(triangulation,check)
            if not disc_verifier.verify(triangulation,vector,proof,check=check):
                raise ArithmeticError('independent sector-window disc replay rejected')
            if count['contains_compressing_disk']:
                return dict(status='DISC_FOUND',coordinates=vector,disc_certificate=proof,
                    allowed_types=allowed,edits=edits,matching_nullity=len(kernel.basis),stats=stats)
        return None
    answer=query(())
    if answer is not None:return answer
    plan=_plan_window(source.prepared,rows,radius,check,base_kernel.basis);stats.update(plan['stats'])
    from .sector_euler import SourceEuler
    source_euler=SourceEuler(source.prepared,plan['_matching_updates'].potentials,check)
    for edits in plan['edits'][1:]:
        check();allowed,basis,projection=plan['_matching_updates'].for_edits(edits,check,projection=True)
        expected=tuple((t,q)for t,q in enumerate(base)if q>=0 and t not in {t for t,_ in edits})+tuple(edits)
        if allowed!=tuple(sorted(expected)):raise ArithmeticError('matching update support mismatch')
        answer=query(edits,basis,plan['_matching_updates'],projection)
        if answer is not None:return answer
    stats['window_complete']=stats['incomplete_disc_queries']==0
    return dict(status='INCONCLUSIVE',reason='no certified disc in the tested sector window',stats=stats)
