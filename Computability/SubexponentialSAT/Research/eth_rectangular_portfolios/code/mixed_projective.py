"""Authored exact specialization of the inherited projective extraction theorem.

No incoming program is imported or executed.  The new implementation supports
different root orders 3 and 5 in one fixed rank-four quotient, rather than the
old {1,2}-target specialization.  The coefficient identity is inherited, not
a new permanent formula.  All algorithms use the same creation representatives.
"""
from dataclasses import dataclass
from math import comb, factorial, prod


def require(ok, message):
    if not ok:
        raise ValueError(message)


@dataclass(frozen=True)
class Ring:
    p: int
    ell: int = 1

    def __post_init__(self):
        require(type(self.p) is int and self.p > 0, 'positive precision')
        require(type(self.ell) is int and self.ell > 0, 'positive nilpotent length')

    @property
    def mask(self): return (1 << self.p)-1
    @property
    def zero(self): return (0,)*(4*self.ell)
    @property
    def one(self): return (1,)+(0,)*(4*self.ell-1)

    def canon(self, a):
        if isinstance(a, int): a=(a,)+(0,)*(4*self.ell-1)
        require(len(a)==4*self.ell, 'wrong coordinate count')
        return tuple(x & self.mask for x in a)

    def add(self, a, b):
        return tuple((x+y)&self.mask for x,y in zip(a,b))

    def scale(self, a, c):
        return tuple((x*c)&self.mask for x in a)

    def mul(self, a, b):
        # Z[U,V]/(U^4+U+1,V^ell); free integral coordinates, no field division.
        out=[]
        for v in range(self.ell):
            c=[0]*7
            for w in range(v+1):
                for i in range(4):
                    x=a[4*w+i]
                    if x:
                        for j in range(4): c[i+j]+=x*b[4*(v-w)+j]
            for k in range(6,3,-1):
                c[k-4]-=c[k]
                c[k-3]-=c[k]
            out.extend(x&self.mask for x in c[:4])
        return tuple(out)

    def power(self, a, n):
        require(n>=0, 'nonnegative power')
        out=self.one
        while n:
            if n&1: out=self.mul(out,a)
            a=self.mul(a,a); n>>=1
        return out


def root15_bitwise(ring):
    """Slow independent-precision oracle retained for root-lift regression tests.

    For f=x^4+x+1, residue primitivity is checked rather than assumed.
    At one extra bit the inverse of 15*x^14 has residue x, so the Newton
    correction x <- x-x*(x^15-1) is sufficient for that one-bit lift.
    """
    r=Ring(1,ring.ell)
    x=r.canon((0,1,0,0)+(0,)*(4*(ring.ell-1)))
    require(r.power(x,15)==r.one and r.power(x,3)!=r.one and
            r.power(x,5)!=r.one, 'residue primitive check')
    for p in range(2,ring.p+1):
        r=Ring(p,ring.ell)
        error=r.add(r.power(x,15),r.scale(r.one,-1))
        x=r.add(x,r.scale(r.mul(x,error),-1))
        require(r.power(x,15)==r.one, 'root lift failed')
    return x


def root15(ring):
    """Classical precision-doubling Newton lift; not a new algebraic identity.

    If x^15=1+e and e is zero modulo 2^k, then
      [x*(1-e/15)]^15 = (1+e)*(1-e+O(e^2)) = 1+O(e^2).
    Only the odd scalar 15 is inverted.  The binomial argument works in the
    finite free quotient and with nilpotents.  Root preparation is charged
    separately whenever no reusable root has already been supplied.
    """
    r=Ring(1,ring.ell)
    x=r.canon((0,1,0,0)+(0,)*(4*(ring.ell-1)))
    require(r.power(x,15)==r.one and r.power(x,3)!=r.one and
            r.power(x,5)!=r.one, 'residue primitive check')
    k=1
    while k<ring.p:
        target=min(2*k,ring.p);r=Ring(target,ring.ell)
        old=x; error=r.add(r.power(x,15),r.scale(r.one,-1))
        correction=r.scale(r.mul(x,error),pow(15,-1,1<<target))
        x=r.add(x,r.scale(correction,-1))
        require(r.power(x,15)==r.one, 'doubling root lift failed')
        require(Ring(k,ring.ell).canon(x)==old, 'root lift changed old precision')
        k=target
    return x


def checked_powers(ring, root):
    root=ring.canon(root)
    powers=[ring.one]
    for _ in range(15): powers.append(ring.mul(powers[-1],root))
    require(powers[15]==ring.one, 'root order does not divide 15')
    for q in (3,5):
        for m in range(1,q):
            total=ring.zero
            for j in range(q): total=ring.add(total,powers[(15*j*m//q)%15])
            require(total==ring.zero, 'root orthogonality failed')
    return powers[:15]


def prepare(rows, beta, ring):
    beta=tuple(beta)
    require(all(type(b) is int and b>=0 for b in beta), 'nonnegative integer targets')
    require(sum(beta)==len(rows), 'homogeneous degree mismatch')
    require(all(len(row)==len(beta) for row in rows), 'wrong row width')
    keep=[j for j,b in enumerate(beta) if b]
    return tuple(tuple(ring.canon(row[j]) for j in keep) for row in rows), tuple(beta[j] for j in keep)


def gray(radices):
    point=[0]*len(radices); step=[1]*len(radices)
    yield point,None,0
    while True:
        for j,n in enumerate(radices):
            if 0<=point[j]+step[j]<n:
                point[j]+=step[j]
                yield point,j,step[j]
                break
            step[j]=-step[j]
        else: return


def projective(rows, beta, ring, root, mixed=True, stats=None):
    rows,beta=prepare(rows,beta,ring)
    if not rows: return ring.one
    if len(beta)==1:
        out=ring.one
        for row in rows: out=ring.mul(out,row[0])
        if stats is not None: stats.update(evaluations=1,guard_bits=0,orders=[])
        return out
    require(max(beta)<=4, 'orders 3 and 5 support target exponents at most four')
    k=min(range(len(beta)),key=lambda j: (beta[j],j))
    free=[j for j in range(len(beta)) if j!=k]
    common=3 if max(beta)<=2 else 5
    qs=[(3 if beta[j]<=2 else 5) if mixed else common for j in free]
    powers=checked_powers(ring,root)
    increments=[]
    for j,q in zip(free,qs):
        increments.append([[ring.mul(row[j],ring.add(powers[15*(g+1)//q],
                                ring.scale(powers[15*g//q],-1)))
                            for row in rows] for g in range(q-1)])
    sums=[]
    for row in rows:
        a=row[k]
        for j in free: a=ring.add(a,row[j])
        sums.append(a)
    total=ring.zero; phase=0; count=0
    for point,changed,direction in gray(qs):
        if changed is not None:
            previous=point[changed]-direction
            inc=increments[changed][min(previous,point[changed])]
            for r,a in enumerate(inc): sums[r]=ring.add(sums[r],ring.scale(a,direction))
            phase=(phase-direction*beta[free[changed]]*(15//qs[changed]))%15
        value=ring.one
        for a in sums: value=ring.mul(value,a)
        total=ring.add(total,ring.mul(value,powers[phase])); count+=1
    out=ring.scale(total,pow(prod(qs),-1,1<<ring.p))
    if stats is not None: stats.update(evaluations=count,guard_bits=0,orders=qs)
    return out


def direct(rows,beta,ring):
    """Small-case independent coefficient DP, not a production-space fallback."""
    rows,beta=prepare(rows,beta,ring)
    values={(0,)*len(beta):ring.one}
    for row in rows:
        out={}
        for a,c in values.items():
            for j,b in enumerate(beta):
                if a[j]<b:
                    t=list(a);t[j]+=1;t=tuple(t)
                    out[t]=ring.add(out.get(t,ring.zero),ring.mul(c,row[j]))
        values=out
    return values.get(beta,ring.zero)


def centered(rows,beta,ring,stats=None):
    """Strong inherited anisotropic antipodal Gray baseline, not step-two-only.

    Every even target uses step 1 and every odd target step 2, minimizing
    integral-centered guard valuation.  Same creation precision/canonicalization.
    """
    rows,beta=prepare(rows,beta,ring)
    if not rows: return ring.one
    B=prod(factorial(b) for b in beta); v=(B&-B).bit_length()-1
    O=sum(b for b in beta if b&1); guard=v+O-1
    require(guard>=0, 'negative paired denominator valuation')
    work=Ring(ring.p+guard,ring.ell)
    boxes=[];prefix=[]
    for j,b in enumerate(beta):
        boxes.append(prefix+[(0,(b-1)//2)]+[(0,a) for a in beta[j+1:]])
        if b&1: break
        prefix=prefix+[(b//2,b//2)]
    bins=[[comb(b,g) for g in range(b+1)] for b in beta]
    total=work.zero; count=0
    for bounds in boxes:
        sums=None; weight=0; sign=0
        for point,j,direction in gray([hi-lo+1 for lo,hi in bounds]):
            gamma=[t+lo for t,(lo,hi) in zip(point,bounds)]
            if j is None:
                x=[(2*g-b) if b&1 else g-b//2 for g,b in zip(gamma,beta)]
                sums=[]
                for row in rows:
                    s=work.zero
                    for a,c in zip(row,x): s=work.add(s,work.scale(a,c))
                    sums.append(s)
                weight=prod(bins[h][g] for h,g in enumerate(gamma))
                sign=-1 if (len(rows)-sum(gamma))&1 else 1
            else:
                old=gamma[j]-direction
                weight=weight*bins[j][gamma[j]]//bins[j][old]
                sign=-sign; step=direction*(2 if beta[j]&1 else 1)
                for r,row in enumerate(rows): sums[r]=work.add(sums[r],work.scale(row[j],step))
            value=work.one
            for s in sums: value=work.mul(value,s)
            total=work.add(total,work.scale(value,sign*weight));count+=1
    mask=(1<<guard)-1
    require(all(not (x&mask) for x in total), 'paired numerator divisibility')
    out=tuple(((x>>guard)*pow(B>>v,-1,1<<ring.p))&ring.mask for x in total)
    if stats is not None: stats.update(evaluations=count,guard_bits=guard)
    return out


def adaptive(rows,beta,ring,root,stats=None):
    _,positive=prepare(rows,beta,ring)
    if not positive: return ring.one
    G=prod(b+1 for b in positive)
    k=min(range(len(positive)),key=positive.__getitem__)
    eligible=max(positive)<=4
    points=prod(3 if b<=2 else 5 for j,b in enumerate(positive) if j!=k) if eligible else G
    if eligible and points < G//2:
        out=projective(rows,beta,ring,root,True,stats)
        if stats is not None: stats['method']='mixed_projective'
        return out
    out=centered(rows,beta,ring,stats)
    if stats is not None: stats['method']='anisotropic_centered'
    return out


def affine(rows,beta,ring,root,method='adaptive',stats=None):
    """Packet-entry adapter: each row starts with its constant coefficient.

    Homogenize with target R-|beta| on the constant coordinate.  An excessive
    requested degree is zero.  The caller must retain immutable creation p.
    """
    beta=tuple(beta)
    require(all(type(b) is int and b>=0 for b in beta), 'nonnegative integer targets')
    require(all(len(row)==len(beta)+1 for row in rows), 'wrong affine row width')
    constant_degree=len(rows)-sum(beta)
    if constant_degree<0:
        if stats is not None: stats.update(method='zero_degree',evaluations=0,guard_bits=0)
        return ring.zero
    homogeneous=(constant_degree,)+beta
    if method=='adaptive': return adaptive(rows,homogeneous,ring,root,stats)
    if method=='mixed': return projective(rows,homogeneous,ring,root,True,stats)
    if method=='common': return projective(rows,homogeneous,ring,root,False,stats)
    if method=='centered': return centered(rows,homogeneous,ring,stats)
    raise ValueError('unknown affine method')
