"""Source-derived Euler screening before standard window geometry.

For compact manifold sources, canonical Euler characteristic is convex on
the normalized Q cone. Nonpositive values at every Q corner therefore
exclude positive Euler throughout the sector. Positive values are only a
reason to continue the ordinary independent disc queries.
"""
from itertools import combinations

from .normal_surface_geometry import _EDGES, _edge, _quad
from .normal_sector import _dot, _nullspace, _primitive, _rref, SearchLimit


def _q_corner_parameters(basis, check, stats, *, max_bases=None, prefix='euler_'):
    """Enumerate every feasible Q extreme direction, without lifting it.

    The coordinate hyperplanes suffice even when the feasible cone has a
    smaller span than the matching kernel. At an extreme ray their active
    normals have rank d-1 in that full kernel. Positive rescaling is irrelevant
    to the Euler sign, so no integral normal coordinates are constructed.
    """
    d=len(basis);k=len(basis[0])
    planes=[]
    for i in range(k):
        check();normal=_primitive(row[i] for row in basis)
        if any(normal):planes.append(normal)
    ordered=sorted(planes)
    planes=tuple(row for i,row in enumerate(ordered)if i==0 or row!=ordered[i-1])
    stats[prefix+'hyperplanes']=stats.get(prefix+'hyperplanes',0)+len(planes)
    for indices in combinations(range(len(planes)),d-1):
        check()
        if max_bases is not None and stats.get(prefix+'bases_attempted',0)>=max_bases:
            raise SearchLimit('candidate-basis allowance exhausted')
        stats[prefix+'bases_attempted']=stats.get(prefix+'bases_attempted',0)+1
        null=_nullspace([planes[i] for i in indices],d,check)
        if len(null)!=1:continue
        parameters=tuple(null[0])
        q=tuple(sum(parameters[j]*basis[j][i] for j in range(d))for i in range(k))
        if not any(q):continue
        if next(x for x in q if x)<0:
            q=tuple(-x for x in q);parameters=tuple(-x for x in parameters)
        if any(x<0 for x in q):continue
        # Emit only the lexicographically first independent active subset.
        # This is deterministic deduplication with polynomial work per
        # candidate, without a hash table whose collisions could square the
        # number of candidates. Column pivots select that unique subset.
        active=[i for i,normal in enumerate(planes)if not _dot(normal,parameters)]
        _,pivots=_rref([[planes[i][j]for i in active]for j in range(d)],len(active),check)
        if indices!=tuple(active[i]for i in pivots):continue
        yield parameters


class SourceEuler:
    """Compile the source's V-E+F functional and its signed Q extension."""
    def __init__(self, prepared, potentials, check):
        n=len(prepared['tetrahedra']);coefficients=[[1]*7 for _ in range(n)]
        seen=set()
        for t in range(n):
            check()
            for a,b in _EDGES:
                root=prepared['edge_roots'][_edge(t,a,b)]
                if root in seen:continue
                seen.add(root)
                coefficients[t][a]+=1;coefficients[t][b]+=1
                for q in range(3):
                    if q!=_quad(a,b):coefficients[t][4+q]+=1
        for t,f in prepared['boundary_faces']+[(t,f)for t,f,_,_,_ in prepared['pairs']]:
            check()
            for v in range(4):
                if v!=f:coefficients[t][v]-=1
            for q in range(3):coefficients[t][4+q]-=1
        self.coefficients=tuple(tuple(row)for row in coefficients)
        linear=[row[4+q]for row in coefficients for q in range(3)]
        groups={};links={}
        for corner,potential in enumerate(potentials):
            check()
            vertex=prepared['vertex_roots'][corner]
            groups.setdefault(vertex,[]).append(corner)
            weight=coefficients[corner//4][corner%4]
            links[vertex]=links.get(vertex,0)+weight
            for j,value in potential.items():
                check();linear[j]+=weight*value
        if any(value not in (1,2)for value in links.values()):
            raise ArithmeticError('source Euler functional disagrees with compact vertex links')
        self.linear=tuple(linear)
        self.groups=tuple((tuple(group),links[v])for v,group in sorted(groups.items()))

    def canonical_value(self, support, basis, forms, parameters, check):
        """Exact Euler of the rational canonical lift, without allocating it."""
        q=tuple(sum(z*row[i]for z,row in zip(parameters,basis))for i in range(len(support)))
        value=sum(self.linear[3*t+typ]*x for (t,typ),x in zip(support,q))
        for group,weight in self.groups:
            check()
            value-=weight*min(_dot(forms[c],parameters)for c in group)
        return value

    def aggregate(self,support,basis,forms,check):
        """Compile anchor-shifted distinct forms once for this Q section.

        Constant vertex groups contribute only a linear term. Every other
        minimum uses its distinct nonzero differences from a fixed anchor.
        Hash grouping is exact, with no approximate equality or threshold.
        """
        linear=[sum(self.linear[3*t+typ]*row[i]for i,(t,typ)in enumerate(support))for row in basis]
        groups=[];distinct=0
        for corners,weight in self.groups:
            check();anchor=forms[corners[0]];unique={}
            for corner in corners:
                check();unique.setdefault(forms[corner],None)
            for i,value in enumerate(anchor):
                if value:linear[i]-=weight*value
            if len(unique)>1:
                differences=tuple(tuple(a-b for a,b in zip(form,anchor))for form in unique if form!=anchor)
                groups.append((weight,differences));distinct+=len(differences)+1
        return tuple(linear),tuple(groups),distinct

    @staticmethod
    def aggregated_value(envelope,parameters,check):
        linear,groups,_=envelope;value=_dot(linear,parameters)
        for weight,differences in groups:
            check()
            value-=weight*min(0,min(_dot(form,parameters)for form in differences))
        return value

    def excludes_positive(self, support, basis, forms, check, stats):
        """Check Q corners, using planar clipping or a generic Q arrangement.

        Empty and lower-dimensional sections are handled by the same exact
        chart clipping as native planar enumeration. A callback interruption
        propagates; partial corner checks cannot exclude a sector.
        """
        check()
        if len(basis)==1:
            stats['euler_screens']+=1
            # Canonical free-coordinate gauge has a positive unit slot, so
            # a negative entry makes the nonnegative Q cone empty.
            row=basis[0]
            if not any(x<0 for x in row):
                stats['euler_corners']+=1
                value=sum(self.linear[3*t+typ]*x for (t,typ),x in zip(support,row))
                for group,weight in self.groups:
                    check();value-=weight*min(forms[c][0]for c in group)
                if value>0:return False
            stats['euler_pruned_sectors']+=1
            return True
        stats['euler_screens']+=1
        if len(basis)>3:
            parameters_stream=_q_corner_parameters(basis,check,stats)
        else:
            from .sector_planar import _section_chart,_section_polygon,_value
            chart=_section_chart(basis,check);corners=_section_polygon(chart,check)
            free=[next(i for i in range(len(support)-1,-1,-1)if row[i])for row in basis]
            parameters_stream=(tuple(_value(chart['forms'][i],point)for i in free)for point in corners)
        envelope=None
        for index,parameters in enumerate(parameters_stream):
            check();stats['euler_corners']+=1
            if index==0:value=self.canonical_value(support,basis,forms,parameters,check)
            else:
                if envelope is None:
                    envelope=self.aggregate(support,basis,forms,check)
                    stats['euler_aggregations']=stats.get('euler_aggregations',0)+1
                    stats['euler_distinct_forms']=stats.get('euler_distinct_forms',0)+envelope[2]
                value=self.aggregated_value(envelope,parameters,check)
            if value>0:return False
        stats['euler_pruned_sectors']+=1
        return True
