"""Exact two-slope tree elimination for homogeneous compatible cones."""
from fractions import Fraction as F
from itertools import product
from .exact import rays_by_zeros, rays_by_supports, dot, primitive


def local_rays(node, oracle=False):
    b=len(node.names); q=len(node.ports)
    found=set(); count=0; dims=[]
    for signs in product((-1,1),repeat=q):
        M=[tuple(row[:b])+tuple(row[b+j]*signs[j] for j in range(q)) for row in node.matrix]
        if oracle:
            rays=rays_by_supports(M,b+q,node.pairs)
        else:
            rays,stats=rays_by_zeros(M,b+q,node.pairs)
            count+=stats['candidates']; dims.append(stats['raw_nullity'])
        for r in rays:
            found.add(tuple(r[:b])+tuple(r[b+j]*signs[j] for j in range(q)))
    return tuple(sorted(found)), {'candidates':count,'raw_nullities':dims,'rays':len(found)}


class Prepared:
    """Compile local rays once; reuse under objectives and coordinate deletions."""
    def __init__(self, model):
        self.model=model.validate()
        self.rays=[]; self.stats=[]
        for node in model.nodes:
            rays,stats=local_rays(node)
            self.rays.append(rays); self.stats.append(stats)
        self.order=model.order()

    def solve(self, objective, zeros=()):
        model=self.model
        names=set(model.names())
        if not set(objective)<=names or not set(zeros)<=names:
            raise ValueError('unknown original coordinate')
        objective={k:F(v) for k,v in objective.items()}
        zeros=set(zeros)
        messages={}
        for v in self.order:
            node=model.nodes[v]; b=len(node.names)
            pos={e:b+j for j,e in enumerate(node.ports)}
            slopes={-1:None,1:None}
            recipes={}
            for ray in self.rays[v]:
                if any(ray[j] for j,s in enumerate(node.names) if s in zeros):
                    continue
                score=dot([objective.get(s,0) for s in node.names],ray[:b])
                valid=True
                for e,j in pos.items():
                    if e==v or not ray[j]:
                        continue
                    sign=1 if ray[j]>0 else -1
                    entry=messages[e][sign]
                    if entry is None:
                        valid=False; break
                    score+=entry[0]*abs(ray[j])
                if not valid:
                    continue
                t=ray[pos[v]] if v else 0
                if not t:
                    if score>0:
                        x,flux=self._assemble(v,ray,messages)
                        return {'status':'POSITIVE','coordinates':{s:str(x[s]) for s in model.names()},
                                'fluxes':{str(e):str(flux[e]) for e in range(1,len(model.nodes))},
                                'objective':str(sum(objective.get(s,0)*x[s] for s in model.names())),
                                'origin_node':v}
                else:
                    sign=1 if t>0 else -1
                    alpha=score/abs(t)
                    if slopes[sign] is None or alpha>slopes[sign]:
                        slopes[sign]=alpha; recipes[sign]=ray
            messages[v]={s:(slopes[s],recipes[s]) if slopes[s] is not None else None for s in (-1,1)}
        return {'status':'NONPOSITIVE',
                'messages':{str(v):{str(s):None if messages[v][s] is None else str(messages[v][s][0])
                                   for s in (-1,1)} for v in self.order},
                'local_rays':[[list(r) for r in rays] for rays in self.rays]}

    def _assemble(self,v,ray,messages):
        model=self.model
        x={s:F(0) for s in model.names()}
        flux={e:F(0) for e in range(1,len(model.nodes))}
        stack=[(v,ray,F(1))]
        while stack:
            u,r,scale=stack.pop()
            node=model.nodes[u]; b=len(node.names)
            for j,s in enumerate(node.names):
                x[s]=scale*r[j]
            for j,e in enumerate(node.ports):
                t=scale*r[b+j]
                flux[e]=t
                if e!=u and t:
                    sign=1 if t>0 else -1
                    childray=messages[e][sign][1]
                    child=model.nodes[e]
                    p=len(child.names)+child.ports.index(e)
                    stack.append((e,childray,abs(t)/abs(childray[p])))
        return x,flux

    def minimal_positive_support(self,objective,zeros=()):
        """At most n+1 exact calls. Keeps only original coordinate faces.

        The returned support is minimal among positive admissible supports,
        hence its primitive source vector is an extreme ray when source-bound.
        """
        disabled=set(zeros)
        answer=self.solve(objective,disabled)
        calls=1
        if answer['status']!='POSITIVE':
            return answer,tuple(sorted(disabled)),calls
        for s in self.model.names():
            if s in disabled:
                continue
            trial=self.solve(objective,disabled|{s}); calls+=1
            if trial['status']=='POSITIVE':
                disabled.add(s); answer=trial
        return answer,tuple(sorted(disabled)),calls


def verify(model, objective, packet, zeros=()):
    """Independent positive arithmetic or exhaustive local negative replay.

    Negative replay uses support enumeration, NOT producer zero-set enumeration.
    It is intentionally exponential in local bag size. No topology is inferred.
    """
    try:
        model.validate(); names=model.names(); zeros=set(zeros)
        if not set(objective)<=set(names) or not zeros<=set(names):
            return False
        c={s:F(objective.get(s,0)) for s in names}
        if packet['status']=='POSITIVE':
            if set(packet['coordinates'])!=set(names):
                return False
            if set(packet['fluxes'])!={str(e) for e in range(1,len(model.nodes))}:
                return False
            x={s:F(packet['coordinates'][s]) for s in names}
            f={e:F(packet['fluxes'][str(e)]) for e in range(1,len(model.nodes))}
            if any(a<0 for a in x.values()) or any(x[s] for s in zeros):
                return False
            for node in model.nodes:
                z=[x[s] for s in node.names]+[f[e] for e in node.ports]
                if any(dot(row,z) for row in node.matrix):
                    return False
                if any(z[i] and z[j] for i,j in node.pairs):
                    return False
            score=sum(c[s]*x[s] for s in names)
            return score>0 and F(packet['objective'])==score
        if packet['status']!='NONPOSITIVE' or len(packet['local_rays'])!=len(model.nodes):
            return False
        computed={}
        for v in model.order():
            node=model.nodes[v]; b=len(node.names)
            rays,_=local_rays(node,oracle=True)
            delivered=tuple(tuple(r) for r in packet['local_rays'][v])
            if delivered!=rays or any(type(a) is not int for r in delivered for a in r):
                return False
            slopes={-1:None,1:None}
            for r in rays:
                if any(r[i] for i,s in enumerate(node.names) if s in zeros):
                    continue
                score=sum(c[s]*r[i] for i,s in enumerate(node.names))
                feasible=True; parent_flux=0
                for i,e in enumerate(node.ports):
                    t=r[b+i]
                    if e==v:
                        parent_flux=t; continue
                    if t:
                        a=computed[e][1 if t>0 else -1]
                        if a is None:
                            feasible=False; break
                        score+=a*abs(t)
                if not feasible:
                    continue
                if parent_flux==0:
                    if score>0:
                        return False
                else:
                    sign=1 if parent_flux>0 else -1
                    a=score/abs(parent_flux)
                    if slopes[sign] is None or a>slopes[sign]:
                        slopes[sign]=a
            encoded=packet['messages'][str(v)]
            if set(encoded)!={'-1','1'}:
                return False
            for sign in (-1,1):
                val=encoded[str(sign)]
                if (val is None)!=(slopes[sign] is None):
                    return False
                if val is not None and F(val)!=slopes[sign]:
                    return False
            computed[v]=slopes
        return set(packet['messages'])=={str(v) for v in range(len(model.nodes))}
    except (ValueError,TypeError,KeyError,IndexError,ZeroDivisionError,OverflowError):
        return False
