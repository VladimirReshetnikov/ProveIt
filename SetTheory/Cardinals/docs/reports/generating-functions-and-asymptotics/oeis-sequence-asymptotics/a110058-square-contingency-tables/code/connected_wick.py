"""Independent exact, bounded connected-Wick Laurent coefficient computation.

No numerical fitting, analytic remainder assertion, or modification of frozen files.
This program uses Python integer arithmetic and fractions. Resource guards are part
of its specification: cost <= 3, total degree <= 18, vertices <= 6, and at most
100000 labelled graphs / degree list. No integer-string safety limits are changed.
"""
from collections import Counter, defaultdict
from fractions import Fraction as F
from functools import lru_cache
from itertools import product, permutations
from math import factorial, comb
import argparse
import sys
sys.dont_write_bytecode = True
from common import (degree_specification, emit, expected_specifications, integer,
                    new_file_path, require)

MAX_VERTICES = 6
MAX_EDGES = 9
MAX_LABELLED = 100000


def all_specs(cost):
    """All unordered degrees >=3 with sum(degree-2)=2*cost."""
    integer(cost, 1, 3, "diagram cost")
    def rec(rem, low, out):
        if rem == 0:
            yield tuple(x+2 for x in out)
        for x in range(low, rem+1):
            yield from rec(rem-x, x, out+(x,))
    return list(rec(2*cost, 1, ()))


def graph_keys(ds):
    """All symmetric nonnegative edge multiplicities of the specified degrees.

    Each loop consumes two half-edges. Edges are filled a vertex at a time,
    distributing all remaining half-edges among subsequent vertices; hence no
    residual unmatched stubs and no duplicate adjacency matrices are produced.
    """
    ds = degree_specification(ds)
    r = len(ds)
    positions = tuple((i,j) for i in range(r) for j in range(i,r))
    position_index = {p:k for k,p in enumerate(positions)}
    def assign_vertex(i, rem, key):
        if i == r:
            yield tuple(key)
            return
        def distribute(j, left, rr, kk):
            if j == r:
                if left == 0:
                    yield from assign_vertex(i+1, rr, kk)
                return
            for count in range(min(left,rr[j])+1):
                rrr=rr.copy(); rrr[j]-=count
                kkk=kk.copy(); kkk[position_index[i,j]]=count
                yield from distribute(j+1,left-count,rrr,kkk)
        for loops in range(rem[i]//2+1):
            rr=rem.copy(); rr[i]=0
            kk=key.copy(); kk[position_index[i,i]]=loops
            yield from distribute(i+1,rem[i]-2*loops,rr,kk)
    yield from assign_vertex(0,list(ds),[0]*len(positions))


def connected(r, key):
    adj=[set() for _ in range(r)]
    for (i,j),m in zip(((i,j) for i in range(r) for j in range(i,r)), key):
        if i!=j and m:
            adj[i].add(j); adj[j].add(i)
    found={0}; todo=[0]
    while todo:
        for j in adj[todo.pop()]-found:
            found.add(j); todo.append(j)
    return len(found)==r


def degree_preserving_permutations(ds):
    groups=[]
    for d in sorted(set(ds)):
        groups.append(tuple(i for i,x in enumerate(ds) if x==d))
    for maps in product(*(tuple(permutations(g)) for g in groups)):
        p=list(range(len(ds)))
        for before,after in zip(groups,maps):
            for i,j in zip(before,after): p[i]=j
        yield tuple(p)


def graph_orbits(ds):
    """Yield one representative and labelled-orbit size, independently checked
    against the total count of connected labelled degree-constrained graphs."""
    ds = degree_specification(ds)
    r=len(ds)
    positions=tuple((i,j) for i in range(r) for j in range(i,r))
    position_index={p:k for k,p in enumerate(positions)}
    permutation_maps=[]
    for p in degree_preserving_permutations(ds):
        permutation_maps.append(tuple(position_index[tuple(sorted((p[i],p[j])))]
                                      for i,j in positions))
    seen=set(); labelled=0; orbit_sum=0
    for key in graph_keys(ds):
        if not connected(r,key): continue
        labelled+=1
        if labelled>MAX_LABELLED: raise RuntimeError('labelled graph cutoff')
        if key in seen: continue
        orbit=set()
        for pm in permutation_maps:
            image=[0]*len(key)
            for old,new in enumerate(pm): image[new]=key[old]
            orbit.add(tuple(image))
        if seen.intersection(orbit): raise RuntimeError('overlapping orbits')
        seen.update(orbit)
        orbit_sum+=len(orbit)
        yield key,len(orbit)
    if labelled!=orbit_sum: raise RuntimeError('orbit count mismatch')


def component_counts(r, edges):
    out=[]
    for mask in range(1<<len(edges)):
        par=list(range(r))
        def find(i):
            while i!=par[i]: i=par[i]
            return i
        for k,(i,j) in enumerate(edges):
            if mask>>k&1: par[find(i)]=find(j)
        out.append(len({find(i) for i in range(r)}))
    return out


def graph_laurent(ds,key):
    """Sum all cell indices and all covariance colors for one Wick graph.

    A row-colored edge supplies n delta(row); a column-colored edge supplies
    n delta(col); a constant edge supplies -1. Every edge divides by 2*n^2.
    For a color choice with A nonconstant edges, row and column equality
    component counts R,C give the monomial (-1)^(E-A)*n^(R+C+A-2E)/2^E.
    All loops have covariance (2*n-1)/(2*n^2), so they can be multiplied out
    separately. Parallel-edge colors are grouped with exact multinomial factors.
    """
    ds = degree_specification(ds)
    r=len(ds); E=sum(ds)//2
    require(isinstance(key, tuple) and len(key) == r*(r+1)//2, "invalid graph key")
    for m in key: integer(m, 0, 9, "edge multiplicity")
    incident = [0]*r
    for (i,j),m in zip(((i,j) for i in range(r) for j in range(i,r)),key):
        incident[i] += m; incident[j] += m
    require(tuple(incident) == ds, "graph degrees do not match")
    positions=tuple((i,j) for i in range(r) for j in range(i,r))
    loops=sum(m for (i,j),m in zip(positions,key) if i==j)
    edges=[(i,j) for (i,j),m in zip(positions,key) if i!=j and m]
    ms=[m for (i,j),m in zip(positions,key) if i!=j and m]
    components=component_counts(r,edges)
    options=[]
    for bit,m in enumerate(ms):
        terms=[]
        for a in range(m+1):
            for b in range(m-a+1):
                c=m-a-b
                terms.append(((1<<bit) if a else 0,
                              (1<<bit) if b else 0,a+b,
                              comb(m,a)*comb(m-a,b)*(-1)**c))
        options.append(terms)
    out=defaultdict(int)
    for selection in product(*options):
        row=col=nonconstant=0; coefficient=1
        for a,b,k,w in selection:
            row|=a; col|=b; nonconstant+=k; coefficient*=w
        power=components[row]+components[col]+nonconstant-2*E
        for k in range(loops+1):
            out[power+k]+=coefficient*comb(loops,k)*2**k*(-1)**(loops-k)
    # Half-edge pairings for a fixed graph: prod d_i! / prod_e m_e!
    # and one extra factor 2^loop_count in the denominator.
    multiplicity=F(1,2**loops)
    for d in ds: multiplicity*=factorial(d)
    for m in key: multiplicity/=factorial(m)
    if multiplicity.denominator!=1: raise RuntimeError('nonintegral Wick count')
    return {k:F(v)*multiplicity/2**E for k,v in out.items() if v}


def cumulant(ds):
    ds = degree_specification(ds)
    r=len(ds); total=sum(ds)
    if not ds or min(ds)<3 or r>MAX_VERTICES or total%2 or total>2*MAX_EDGES:
        raise ValueError('unsupported degree specification')
    cost=(total-2*r)//2
    if cost>3: raise ValueError('cost cutoff')
    out=defaultdict(F); orbits=labelled=0
    for key,orbit_size in graph_orbits(ds):
        orbits+=1; labelled+=orbit_size
        for power,value in graph_laurent(ds,key).items():
            out[power]+=orbit_size*value
    out={p:v for p,v in sorted(out.items(),reverse=True) if v}
    if out and max(out)>1-cost: raise RuntimeError('connected rank bound failure')
    return out,{'orbits':orbits,'labelled_graphs':labelled}


def geometric_coefficients(max_degree=8):
    """Cumulants of Geom(1/2) from the exact mgf recurrence.

    For G(t)=1/(2-exp(t)), raw moment M_j=sum_{k=0}^{j-1} C(j,k) M_k,
    M_0=1. Then K_j=M_j-sum_{k=1}^{j-1} C(j-1,k-1) K_k M_{j-k}.
    Return real coefficients b_j=K_j/j!, so h(z)=sum b_j*i^j*z^j.
    The mean and Gaussian terms have already been removed.
    """
    integer(max_degree, 3, 8, "maximum geometric degree")
    moments=[1]; cumulants=[0]
    for j in range(1,max_degree+1):
        moments.append(sum(comb(j,k)*moments[k] for k in range(j)))
        cumulants.append(moments[j]-sum(comb(j-1,k-1)*cumulants[k]*moments[j-k]
                                       for k in range(1,j)))
    return {j:F(cumulants[j],factorial(j)) for j in range(3,max_degree+1)}


def log_weight(ds, coeff):
    """Multiset expansion of log E exp(sum h_d S_d).

    The ordered cumulant expansion has 1/r!. A degree multiset occurs
    r!/prod_d multiplicity(d)! times, leaving exactly the divisor below.
    """
    ds = degree_specification(ds)
    w=F((-1)**(sum(ds)//2))  # i**sum(ds), always real for even total degree.
    for d in ds:w*=coeff[d]
    for multiplicity in Counter(ds).values():w/=factorial(multiplicity)
    return w


def fmt(poly):
    return ' + '.join(f'({v}) n^{p}' for p,v in poly.items()) or '0'


def receipt():
    coeff=geometric_coefficients()
    rows=[]; log=defaultdict(F)
    specs=tuple(ds for cost in range(1,4) for ds in all_specs(cost))
    require(specs == expected_specifications(), 'degree partition enumeration mismatch')
    for ds in specs:
        cost=sum(d-2 for d in ds)//2
        poly,stats=cumulant(ds); w=log_weight(ds,coeff)
        for p,v in poly.items(): log[p]+=w*v
        rows.append({'degrees':list(ds),'cost':cost,
                     'cumulant':{str(p):str(v) for p,v in poly.items()},
                     'weight':str(w),'statistics':stats})
    selected={p:v for p,v in sorted(log.items(),reverse=True) if p>=-2 and v}
    require(selected == {0:F(1,4),-1:F(-3,2),-2:F(223,32)}, 'logarithmic coefficient mismatch')
    lower=sum(log_weight(tuple(row['degrees']),coeff)*F(row['cumulant'].get('-2','0'))
              for row in rows if row['cost']<3)
    higher=sum(log_weight(tuple(row['degrees']),coeff)*F(row['cumulant'].get('-2','0'))
               for row in rows if row['cost']==3)
    return {'status':'PASS','coefficients':{str(j):str(b) for j,b in coeff.items()},
            'rows':rows,'log_through_n_minus_2':{str(p):str(v) for p,v in selected.items()},
            'n_minus_2_by_cost':{'cost_1_and_2':str(lower),'cost_3':str(higher)},
            'scope':'Exact finite Laurent identities; no analytic remainder certificate.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',help='new external output file; default stdout')
    args=parser.parse_args()
    if args.output is not None: new_file_path(args.output)
    emit(receipt(),args.output)


if __name__=='__main__':
    try: main()
    except (ValueError,RuntimeError,OSError,ArithmeticError) as exc: raise SystemExit(str(exc))
