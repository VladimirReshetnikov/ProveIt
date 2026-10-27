"""Independent exact packet-coefficient kernels; Python stdlib only.

No upstream executable code was imported. Arithmetic is in a finite free
integral quotient reduced modulo a power of two. The centered half-grid is
classical polarization/Glynn algebra, not a claim of a new permanent formula.
"""
from dataclasses import dataclass
from itertools import product
from math import comb, factorial, prod


@dataclass(frozen=True)
class Ring:
    precision: int
    # f(U)=U^e + f[0]+...+f[e-1] U^(e-1); None denotes scalars.
    f: tuple | None = None
    ell: int = 1

    def __post_init__(self):
        if self.precision < 1 or self.ell < 1 or self.f == ():
            raise ValueError('positive precision, ell and monic degree required')

    @property
    def mask(self): return (1 << self.precision) - 1
    @property
    def e(self): return len(self.f) if self.f else 1
    @property
    def dimension(self): return self.e * self.ell
    @property
    def scalar(self): return self.f is None and self.ell == 1
    @property
    def zero(self): return 0 if self.scalar else (0,) * self.dimension
    @property
    def one(self): return 1 if self.scalar else (1,) + (0,) * (self.dimension - 1)

    def canonical(self, x):
        if self.scalar:
            return int(x) & self.mask
        if isinstance(x, int):
            x = (x,) + (0,) * (self.dimension - 1)
        if len(x) != self.dimension: raise ValueError('wrong coordinate dimension')
        return tuple(int(a) & self.mask for a in x)

    def add(self, x, y):
        mask = self.mask
        if self.scalar: return (x+y) & mask
        return tuple((a+b)&mask for a,b in zip(x,y))

    def scale(self, x, n):
        mask = self.mask
        if self.scalar: return (x*n)&mask
        return tuple((a*n)&mask for a in x)

    def mul(self, x, y):
        mask = self.mask
        if self.scalar: return (x*y)&mask
        e, ell = self.e, self.ell
        out = [0] * (e*ell)
        for v in range(ell):
            q = [0] * (2*e-1)
            for a in range(v+1):
                for i in range(e):
                    xi=x[a*e+i]
                    for j in range(e): q[i+j] += xi*y[(v-a)*e+j]
            if self.f:
                for d in range(2*e-2,e-1,-1):
                    for j in range(e): q[d-e+j] -= q[d]*self.f[j]
            out[v*e:(v+1)*e] = [a&mask for a in q[:e]]
        return tuple(out)

    def divide_and_reduce(self, numerator, shift, odd, target_precision):
        mask=(1<<target_precision)-1
        inv=pow(odd, -1, 1<<target_precision)
        def one(a):
            if a & ((1<<shift)-1):
                raise ArithmeticError('loss of exact divisibility: precision or identity failure')
            return ((a>>shift)*inv)&mask
        if self.scalar: return one(numerator)
        return tuple(one(a) for a in numerator)


def _prepare(rows, beta, ring):
    beta=tuple(beta)
    if any(not isinstance(b,int) or b<0 for b in beta): raise ValueError('invalid beta')
    R=len(rows)
    if sum(beta)!=R: raise ValueError('homogeneous total degree must equal number of rows')
    if any(len(row)!=len(beta) for row in rows): raise ValueError('wrong row width')
    # Canonical creation-time representatives are fixed BEFORE guard precision.
    keep=[j for j,b in enumerate(beta) if b]
    rows=tuple(tuple(ring.canonical(row[j]) for j in keep) for row in rows)
    beta=tuple(beta[j] for j in keep)
    B=prod(factorial(b) for b in beta)
    v=(B & -B).bit_length()-1
    return rows,beta,B,v


def _eval(rows, point, ring):
    out=ring.one
    for row in rows:
        value=ring.zero
        for a,g in zip(row,point): value=ring.add(value,ring.scale(a,g))
        out=ring.mul(out,value)
    return out


def forward_reference(rows, beta, ring, stats=None):
    """Full forward grid with independently recomputed row sums (fair identity baseline)."""
    rows,beta,B,v=_prepare(rows,beta,ring)
    R=len(rows)
    if not R: return ring.one
    work=Ring(ring.precision+v,ring.f,ring.ell)
    total=work.zero
    count=0
    for gamma in product(*(range(b+1) for b in beta)):
        weight=(-1 if (R-sum(gamma))&1 else 1)*prod(comb(b,g) for b,g in zip(beta,gamma))
        total=work.add(total,work.scale(_eval(rows,gamma,work),weight))
        count+=1
    if stats is not None: stats.update(evaluations=count,guard_bits=v,method='forward_reference')
    return work.divide_and_reduce(total,v,B>>v,ring.precision)


def gray_points(bounds):
    """Yield mutable mixed-radix reflected Gray point and changed index/direction.

    The consumer must not retain yielded lists. Every grid point appears once;
    every successor changes exactly one coordinate by +1 or -1.
    """
    point=[lo for lo,hi in bounds]
    direction=[1]*len(bounds)
    yield point,None,0
    while True:
        for j,(lo,hi) in enumerate(bounds):
            nxt=point[j]+direction[j]
            if lo<=nxt<=hi:
                point[j]=nxt
                yield point,j,direction[j]
                break
            direction[j] = -direction[j]
        else: return


def _grid_sum(rows,beta,bounds,work,centered):
    """One rectangular Gray grid, retaining only row sums and current point."""
    R=len(rows)
    bins=[tuple(comb(b,g) for g in range(b+1)) for b in beta]
    total=work.zero
    count=0
    for gamma,j,direction in gray_points(bounds):
        if j is None:
            point=[2*g-b if centered else g for g,b in zip(gamma,beta)]
            sums=[]
            for row in rows:
                a=work.zero
                for coeff,g in zip(row,point): a=work.add(a,work.scale(coeff,g))
                sums.append(a)
            weight=prod(bins[j][g] for j,g in enumerate(gamma))
            sign=-1 if (R-sum(gamma))&1 else 1
        else:
            old=gamma[j]-direction
            # Both factors are ordinary exact integers; this division is exact.
            weight=weight*bins[j][gamma[j]]//bins[j][old]
            sign=-sign
            step=direction*(2 if centered else 1)
            for r,row in enumerate(rows):
                sums[r]=work.add(sums[r],work.scale(row[j],step))
        value=work.one
        for row_sum in sums: value=work.mul(value,row_sum)
        total=work.add(total,work.scale(value,sign*weight))
        count+=1
    return total,count


def forward_gray(rows,beta,ring,stats=None):
    """Strong optimized baseline: same full FD grid with Gray row-sum updates."""
    rows,beta,B,v=_prepare(rows,beta,ring)
    R=len(rows)
    if not R: return ring.one
    work=Ring(ring.precision+v,ring.f,ring.ell)
    total,count=_grid_sum(rows,beta,[(0,b) for b in beta],work,False)
    if stats is not None: stats.update(evaluations=count,guard_bits=v,method='forward_gray')
    return work.divide_and_reduce(total,v,B>>v,ring.precision)


def antipodal_boxes(beta):
    """Disjoint rectangular representatives of gamma <-> beta-gamma pairs.

    Pick the first noncentral coordinate strictly below its midpoint. An odd
    coordinate stops the partition; an all-even central point is excluded.
    """
    prefix=[]
    for j,b in enumerate(beta):
        yield prefix+[(0,(b-1)//2)]+[(0,d) for d in beta[j+1:]]
        if b&1: return
        prefix=prefix+[(b//2,b//2)]


def centered_half_gray(rows,beta,ring,stats=None):
    """Paired centered finite differences, with exact power-of-two guard bits."""
    rows,beta,B,v=_prepare(rows,beta,ring)
    R=len(rows)
    if not R: return ring.one
    shift=R-1+v
    work=Ring(ring.precision+shift,ring.f,ring.ell)
    total=work.zero
    count=0
    for bounds in antipodal_boxes(beta):
        part,n=_grid_sum(rows,beta,bounds,work,True)
        total=work.add(total,part)
        count+=n
    if stats is not None: stats.update(evaluations=count,guard_bits=shift,method='centered_half_gray')
    return work.divide_and_reduce(total,shift,B>>v,ring.precision)


def direct_coefficient(rows,beta,ring):
    """Independent small-instance oracle; exponential table, NEVER production fallback."""
    beta=tuple(beta)
    if any(b<0 for b in beta): raise ValueError('negative exponent')
    if sum(beta)!=len(rows): raise ValueError('degree mismatch')
    coeff={(0,)*len(beta):ring.one}
    for row in rows:
        nxt={}
        for exp,value in coeff.items():
            for j,a in enumerate(row):
                if exp[j]>=beta[j]: continue
                ex=list(exp);ex[j]+=1;ex=tuple(ex)
                value2=ring.mul(value,ring.canonical(a))
                nxt[ex]=ring.add(nxt.get(ex,ring.zero),value2)
        coeff=nxt
    return coeff.get(beta,ring.zero)


def affine_coefficient(rows,beta,ring,method=centered_half_gray,stats=None):
    """rows[r][0] is constant; remaining columns are the requested variables."""
    if any(b<0 for b in beta): raise ValueError('negative exponent')
    if sum(beta)>len(rows): return ring.zero
    return method(rows,(len(rows)-sum(beta),)+tuple(beta),ring,stats)


def projective_odd_root(rows,beta,ring,root,order,stats=None):
    """Projective root filter for a verified odd-order root already in the ring.

    Applicable when order > every positive target exponent. Fix a coordinate
    having minimum exponent to 1. No factorial division or guard bits. This is
    selective, not universally faster: order**(k-1) can exceed the FD grid.
    """
    rows,beta,B,v=_prepare(rows,beta,ring)
    if not rows:return ring.one
    if order<3 or not order&1 or order<=max(beta):
        raise ValueError('odd order must exceed every target exponent')
    root=ring.canonical(root)
    powers=[ring.one]
    for _ in range(order): powers.append(ring.mul(powers[-1],root))
    if powers[-1]!=ring.one:raise ValueError('root has incorrect order')
    for d in range(1,order):
        s=ring.zero
        for a in range(order):s=ring.add(s,powers[(a*d)%order])
        if s!=ring.zero:raise ValueError('root filter is not orthogonal')
    k=min(range(len(beta)),key=beta.__getitem__)
    fixed=[row[k] for row in rows]
    active=[j for j in range(len(beta)) if j!=k]
    # Precompute every neighboring-root row-sum change. This is polynomial input
    # storage, not a table indexed by the exponential evaluation grid.
    increments=[]
    for j in active:
        by_step=[]
        for g in range(order-1):
            diff=ring.add(powers[g+1],ring.scale(powers[g],-1))
            by_step.append([ring.mul(row[j],diff) for row in rows])
        increments.append(by_step)
    sums=[]
    for r,row in enumerate(rows):
        a=fixed[r]
        for j in active:a=ring.add(a,row[j])
        sums.append(a)
    total=ring.zero;count=0;phase=0
    for gamma,j,direction in gray_points([(0,order-1)]*len(active)):
        if j is not None:
            old=gamma[j]-direction
            step=min(old,gamma[j])
            for r,increment in enumerate(increments[j][step]):
                sums[r]=ring.add(sums[r],increment if direction==1 else ring.scale(increment,-1))
            phase=(phase-beta[active[j]]*direction)%order
        value=ring.one
        for a in sums:value=ring.mul(value,a)
        total=ring.add(total,ring.mul(value,powers[phase]))
        count+=1
    denom=order**len(active)
    answer=ring.scale(total,pow(denom,-1,1<<ring.precision))
    if stats is not None:stats.update(evaluations=count,guard_bits=0,method='projective_odd_root',order=order)
    return answer


def lift_cube_root(residue_root,ring):
    """Bit-by-bit Hensel lift of a supplied root of x^2+x+1 modulo 2.

    The source's extension degree 4*lambda contains F4. Finding a residue root
    can be done by an O(2^e)-element deterministic search, polynomial in source
    size s because e=4*ceil(log2(s)); that search is not timed in benchmarks.
    """
    one=Ring(1,ring.f,ring.ell)
    x=one.canonical(residue_root)
    h=one.add(one.add(one.mul(x,x),x),one.one)
    if h!=one.zero:raise ValueError('not a residue cube root')
    for p in range(1,ring.precision):
        nxt=Ring(p+1,ring.f,ring.ell)
        h=nxt.add(nxt.add(nxt.mul(x,x),x),nxt.one)
        if nxt.scalar: correction=(h>>p)<<p
        else:correction=tuple((a>>p)<<p for a in h)
        x=nxt.add(x,correction)
    return x


def adaptive_homogeneous(rows,beta,ring,cube_root=None,stats=None):
    """Dispatch by proven evaluation counts; no universal wall-clock claim.

    A precomputed root is optional. No field extension or root search is hidden
    in the dispatch. Single-coordinate targets are handled by direct product.
    """
    rows,beta,B,v=_prepare(rows,beta,ring)
    if not rows:return ring.one
    if len(beta)==1:
        out=ring.one
        for row in rows:out=ring.mul(out,row[0])
        if stats is not None:stats.update(evaluations=1,guard_bits=0,method='single_coordinate')
        return out
    G=prod(b+1 for b in beta)
    if cube_root is not None and max(beta)<=2 and 3**(len(beta)-1)<G//2:
        return projective_odd_root(rows,beta,ring,cube_root,3,stats)
    return centered_half_gray(rows,beta,ring,stats)
