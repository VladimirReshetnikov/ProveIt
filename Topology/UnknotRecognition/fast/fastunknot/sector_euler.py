"""Source-derived Euler screening before standard window geometry.

For compact manifold sources, canonical Euler characteristic is convex on
the normalized Q cone. Nonpositive values at every Q corner therefore
exclude positive Euler throughout the sector. Positive values are only a
reason to continue the ordinary independent disc queries.
"""
from .normal_surface_geometry import _EDGES, _edge, _quad
from .normal_sector import _dot


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
        """Check every Q corner at nullity <=3; return False above that.

        Empty and lower-dimensional sections are handled by the same exact
        chart clipping as native planar enumeration. A callback interruption
        propagates; partial corner checks cannot exclude a sector.
        """
        check()
        if len(basis)>3:return False
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
        from .sector_planar import _section_chart,_section_polygon,_value
        stats['euler_screens']+=1
        chart=_section_chart(basis,check);corners=_section_polygon(chart,check)
        free=[next(i for i in range(len(support)-1,-1,-1)if row[i])for row in basis]
        envelope=None
        for index,point in enumerate(corners):
            check();stats['euler_corners']+=1
            parameters=tuple(_value(chart['forms'][i],point)for i in free)
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
