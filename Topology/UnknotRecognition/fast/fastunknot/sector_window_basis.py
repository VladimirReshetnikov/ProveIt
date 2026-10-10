"""Exact small-parameter matching updates for a source residual window."""
from fractions import Fraction

from .normal_sector import _nullspace,_rref,SectorKernel,_dot
from .normal_surface_geometry import _coordinates


def canonical_matching_basis(vectors,width,check):
    """Use the native nullspace gauge: rightmost independent free columns."""
    reduced,pivots=_rref([list(reversed(row))for row in vectors],width,check)
    ordered=sorted((width-1-p,tuple(reversed(row)))for p,row in zip(pivots,reduced))
    return tuple(row for _,row in ordered)


class WindowBasis:
    """Old source kernel plus residual/coefficient decompositions.

    Each record represents A_j = A_S*c_j + r_j in the same exact quotient.
    Candidate edits are the zero/signed-pair classes proved by the planner.
    """
    def __init__(self,base_support,base_basis,residuals,coefficients,potentials):
        self.base_support=tuple(base_support)
        self.base_basis=tuple(tuple(row)for row in base_basis)
        self.residuals=residuals
        self.coefficients=coefficients
        self.potentials=potentials

    def for_edits(self,edits,check):
        k=len(self.base_support);added=tuple(edits);width=k+len(added)
        vectors=[tuple(row)+(Fraction(0),)*len(added)for row in self.base_basis]
        if len(added)==1 or (len(added)==2 and not self.residuals[added[0]]and not self.residuals[added[1]]):
            for a,item in enumerate(added):
                check()
                if self.residuals[item]:raise ArithmeticError('nonzero singleton residual')
                coefficients=self.coefficients[item]
                vectors.append(tuple(-coefficients.get(i,0)for i in range(k))+
                    tuple(Fraction(i==a)for i in range(len(added))))
        elif len(added)==2:
            first,second=added;left,right=self.residuals[first],self.residuals[second]
            if not left or not right:raise ArithmeticError('mixed zero/nonzero residual pair')
            pivot=min(left);ratio=-Fraction(left[pivot])/right[pivot]
            if ratio<=0 or any(left.get(i,0)+ratio*right.get(i,0)for i in left.keys()|right.keys()):
                raise ArithmeticError('pair residuals do not cancel positively')
            a,b=self.coefficients[first],self.coefficients[second]
            vectors.append(tuple(-a.get(i,0)-ratio*b.get(i,0)for i in range(k))+(Fraction(1),ratio))
        elif added:raise ValueError('matching updates accept at most two edits')
        replaced={t for t,_ in added}
        removed=[i for i,(t,_)in enumerate(self.base_support)if t in replaced]
        if removed:
            parameters=_nullspace([[row[i]for row in vectors]for i in removed],len(vectors),check)
            vectors=[tuple(sum(z*row[i]for z,row in zip(parameter,vectors))for i in range(width))
                     for parameter in parameters]
        labelled=[(item,i)for i,item in enumerate(self.base_support)if i not in removed]
        labelled += [(item,k+i)for i,item in enumerate(added)]
        labelled.sort();support=tuple(item for item,_ in labelled)
        restricted=[tuple(row[i]for _,i in labelled)for row in vectors]
        return support,canonical_matching_basis(restricted,len(support),check)


class ProjectedWindowKernel(SectorKernel):
    """Source matching space with potentials expressed in free Q coordinates."""
    def lift(self,quadrilaterals,check=lambda:None):
        q=tuple(quadrilaterals)
        if (len(q)!=len(self.support)or any(type(x)is not int or x<0 for x in q)
                or any(_dot(row,q)for row in self.cycle_rows)):
            raise ValueError('quadrilateral vector is outside the updated cone')
        values={c:_dot(self.potentials[c],q)for c in self.classes}
        for group in self.groups:
            minimum=min(values[c]for c in group)
            for c in group:
                value=values[c]-minimum
                if value.denominator!=1:raise ArithmeticError('updated lift is not integral')
                values[c]=int(value)
        rows=[[0]*7 for _ in self.prepared['tetrahedra']]
        for corner,c in enumerate(self.corner_class):
            check();rows[corner//4][corner%4]=values.get(c,0)
        for (t,kind),value in zip(self.support,q):rows[t][4+kind]=value
        _coordinates(self.prepared,rows,check)
        return rows


def projected_corner_forms(support,basis,global_potentials,check):
    """Project retained source potentials once onto a matching basis."""
    indices={3*t+q:i for i,(t,q)in enumerate(support)}
    result=[]
    for potential in global_potentials:
        check()
        selected=[(indices[j],value)for j,value in potential.items()if j in indices]
        result.append(tuple(sum(value*vector[i]for i,value in selected)for vector in basis))
    return tuple(result)


def projected_window_kernel(raw,prepared,support,basis,global_potentials,check,*,corner_forms=None):
    """Build the exact matching cone directly from the updated Q basis.

    The basis is source-derived and in native free-coordinate gauge. Equal
    projected potentials at one global vertex are contracted. Linear Q
    constraints and one triangle-offset factor per remaining vertex group
    describe the complete standard cone, so generic rank/support fallbacks
    remain available at higher nullity.
    """
    support=tuple(support);basis=tuple(tuple(row)for row in basis)
    k=len(support);d=len(basis)
    free=[]
    for vector in basis:
        check()
        # Rightmost leading coordinate is the free unit of the canonical row.
        p=next(i for i in range(k-1,-1,-1)if vector[i])
        if vector[p]!=1:raise ArithmeticError('matching basis is not canonical')
        free.append(p)
    if len(set(free))!=d or any(vector[p]!=int(i==j)for i,vector in enumerate(basis)for j,p in enumerate(free)):
        raise ArithmeticError('matching free-coordinate identity failed')
    by_vertex={};corner_class=[None]*(4*len(prepared['tetrahedra']))
    coefficient_forms={}
    if corner_forms is None:
        corner_forms=projected_corner_forms(support,basis,global_potentials,check)
    for corner,form in enumerate(corner_forms):
        check()
        vertex=prepared['vertex_roots'][corner]
        group=by_vertex.setdefault(vertex,{})
        representative=group.setdefault(form,corner);corner_class[corner]=representative
        coefficient_forms[representative]=form
    groups=tuple(tuple(sorted(group.values()))for _,group in sorted(by_vertex.items())if len(group)>1)
    classes=tuple(sorted(c for group in groups for c in group));lookup={c:i for i,c in enumerate(classes)}
    potentials={}
    for c in classes:
        row=[Fraction(0)]*k
        for p,value in zip(free,coefficient_forms[c]):row[p]=value
        potentials[c]=tuple(row)
    cycle_rows=[]
    for j in range(k):
        check()
        if j in free:continue
        row=[Fraction(0)]*k;row[j]=1
        for p,vector in zip(free,basis):row[p]-=vector[j]
        cycle_rows.append(tuple(row))
    matrix=[(Fraction(0),)*len(classes)+row for row in cycle_rows]
    for group in groups:
        anchor=group[0]
        for c in group[1:]:
            check();row=[Fraction(0)]*(len(classes)+k)
            row[lookup[c]]=1;row[lookup[anchor]]=-1
            for j in range(k):row[len(classes)+j]=potentials[anchor][j]-potentials[c][j]
            matrix.append(tuple(row))
    stats=dict(tetrahedra=len(prepared['tetrahedra']),allowed_types=k,matching_nullity=d,
        matching_rank=k-d,triangle_classes=len(classes),kernel_variables=len(classes)+k,
        kernel_equations=len(matrix),projected_window_kernel=True)
    return ProjectedWindowKernel(raw,prepared,support,tuple(corner_class),classes,groups,tuple(matrix),
        potentials,tuple(cycle_rows),basis,stats)
