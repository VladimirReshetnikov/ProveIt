"""Exact small-parameter matching updates for a source residual window."""
from fractions import Fraction

from .normal_sector import _nullspace,_rref,SectorKernel,_dot
from .normal_surface_geometry import _coordinates


def canonical_matching_basis(vectors,width,check,*,return_transform=False):
    """Use the native nullspace gauge: rightmost independent free columns."""
    rows=[list(reversed(row))for row in vectors]
    if return_transform:
        for i,row in enumerate(rows):row.extend(Fraction(i==j)for j in range(len(rows)))
    # Only matching columns are eligible pivots. The trailing identity, if
    # supplied, records exactly the same row operations on the thin modes.
    reduced,pivots=_rref(rows,width,check)
    ordered=sorted((width-1-p,tuple(reversed(row[:width])),tuple(row[width:]))
                   for p,row in zip(pivots,reduced))
    basis=tuple(row for _,row,_ in ordered)
    return (basis,tuple(transform for _,_,transform in ordered))if return_transform else basis


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
        self._base_modes=None
        self._column_modes={}
        self._potential_columns=None

    def for_edits(self,edits,check,*,projection=False):
        k=len(self.base_support);added=tuple(edits);width=k+len(added)
        vectors=[tuple(row)+(Fraction(0),)*len(added)for row in self.base_basis]
        new_modes=[]
        if len(added)==1 or (len(added)==2 and not self.residuals[added[0]]and not self.residuals[added[1]]):
            for a,item in enumerate(added):
                check()
                if self.residuals[item]:raise ArithmeticError('nonzero singleton residual')
                coefficients=self.coefficients[item]
                vectors.append(tuple(-coefficients.get(i,0)for i in range(k))+
                    tuple(Fraction(i==a)for i in range(len(added))))
                new_modes.append(((item,Fraction(1)),))
        elif len(added)==2:
            first,second=added;left,right=self.residuals[first],self.residuals[second]
            if not left or not right:raise ArithmeticError('mixed zero/nonzero residual pair')
            pivot=min(left);ratio=-Fraction(left[pivot])/right[pivot]
            if ratio<=0 or any(left.get(i,0)+ratio*right.get(i,0)for i in left.keys()|right.keys()):
                raise ArithmeticError('pair residuals do not cancel positively')
            a,b=self.coefficients[first],self.coefficients[second]
            vectors.append(tuple(-a.get(i,0)-ratio*b.get(i,0)for i in range(k))+(Fraction(1),ratio))
            new_modes.append(((first,Fraction(1)),(second,ratio)))
        elif added:raise ValueError('matching updates accept at most two edits')
        if projection:
            mode_parameters=tuple(tuple(Fraction(i==j)for j in range(len(vectors)))for i in range(len(vectors)))
        replaced={t for t,_ in added}
        removed=[i for i,(t,_)in enumerate(self.base_support)if t in replaced]
        if removed:
            parameters=_nullspace([[row[i]for row in vectors]for i in removed],len(vectors),check)
            if projection:mode_parameters=parameters
            vectors=[tuple(sum(z*row[i]for z,row in zip(parameter,vectors))for i in range(width))
                     for parameter in parameters]
        labelled=[(item,i)for i,item in enumerate(self.base_support)if i not in removed]
        labelled += [(item,k+i)for i,item in enumerate(added)]
        labelled.sort();support=tuple(item for item,_ in labelled)
        restricted=[tuple(row[i]for _,i in labelled)for row in vectors]
        if not projection:return support,canonical_matching_basis(restricted,len(support),check)
        basis,transform=canonical_matching_basis(restricted,len(support),check,return_transform=True)
        weights=tuple(tuple(sum(a*row[i]for a,row in zip(z,mode_parameters))
                            for i in range(len(self.base_basis)+len(new_modes)))for z in transform)
        return support,basis,(tuple(new_modes),weights)

    def _corrected_column(self,item,check,stats):
        check()
        if item not in self._column_modes:
            if self._potential_columns is None:
                columns={}
                for corner,potential in enumerate(self.potentials):
                    check()
                    for j,value in potential.items():columns.setdefault(j,[]).append((corner,value))
                self._potential_columns=columns
                if stats is not None:stats['potential_transpositions']+=1
            t,q=item;terms={3*t+q:Fraction(1)}
            for i,value in self.coefficients[item].items():
                a,b=self.base_support[i];terms[3*a+b]=-value
            values={}
            for j,coefficient in terms.items():
                check()
                for corner,value in self._potential_columns.get(j,()):
                    check();values[corner]=values.get(corner,0)+coefficient*value
                    if not values[corner]:del values[corner]
            # Publish only a completed column; an interrupted construction
            # never leaves a partial cached vector for another query.
            self._column_modes[item]=values
            if stats is not None:stats['potential_columns_cached']=len(self._column_modes)
        return self._column_modes[item]

    def project_modes(self,plan,check,stats=None):
        """Apply tracked small row operations to lazily cached source modes.

        A corrected column is P_j-P_S*c_j. It need not be a matching mode
        alone when its residual is nonzero; the recorded cancelling pair
        and subsequent replacement/gauge operations give the actual kernel.
        """
        check();new_modes,weights=plan;d0=len(self.base_basis)
        entries=[]
        for row in weights:
            check();terms=[]
            for i,value in enumerate(row[:d0]):
                if not value:continue
                if self._base_modes is None:
                    forms=projected_corner_forms(self.base_support,self.base_basis,self.potentials,check)
                    self._base_modes=tuple({c:form[j]for c,form in enumerate(forms)if form[j]}for j in range(d0))
                    if stats is not None:stats['base_potential_builds']+=1
                terms.append((self._base_modes[i],value))
            for mode,value in zip(new_modes,row[d0:]):
                if value:
                    for item,scale in mode:
                        terms.append((self._corrected_column(item,check,stats),value*scale))
            entries.append(terms)
        projected=[]
        for terms in entries:
            values={}
            for column,coefficient in terms:
                check()
                for corner,value in column.items():
                    values[corner]=values.get(corner,0)+(value if coefficient==1 else coefficient*value)
            projected.append(values)
        forms=[]
        for corner in range(len(self.potentials)):
            check()
            forms.append(tuple(values.get(corner,0)for values in projected))
        if stats is not None:stats['mode_projections']+=1
        return tuple(forms)


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
