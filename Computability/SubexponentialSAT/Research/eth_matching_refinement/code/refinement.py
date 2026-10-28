"""Exact component routines, NOT a full SAT solver. Python standard library only."""
from fractions import Fraction as F
from math import isqrt

def ceildiv(a, b):
    return -(-a // b)

def ceil_log2(n):
    if n < 1:
        raise ValueError('positive integer required')
    return (n - 1).bit_length()

def color_matchings(edges):
    """Greedy coloring of a bipartite multigraph; endpoints have separate types."""
    groups = []
    for e in edges:
        for g in groups:
            if all(e[0] != f[0] and e[1] != f[1] for f in g):
                g.append(e)
                break
        else:
            groups.append([e])
    return groups

def packing_data(edges, labels, lam):
    if labels < 1 or lam < 1:
        raise ValueError('labels and lambda must be positive')
    groups = color_matchings(edges)
    if not groups:
        return [], 0, []
    tau = ceil_log2(8 * len(groups) * labels * labels)
    thresholds = [ceildiv((lam+1)*len(g), lam*labels*labels) + 2*lam*tau
                  for g in groups]
    return groups, tau, thresholds

def potential(groups, thresholds, labels, lam, assignment):
    """Exact conditional expectation; keys are ('L',vertex), ('R',vertex)."""
    t = F(lam+1, lam)
    total = F(0)
    for g, h in zip(groups, thresholds):
        for a in range(labels):
            for b in range(labels):
                v = t ** (-h)
                for left, right in g:
                    pl = F(assignment['L', left] == a) if ('L', left) in assignment else F(1, labels)
                    pr = F(assignment['R', right] == b) if ('R', right) in assignment else F(1, labels)
                    v *= 1 + pl*pr/lam
                total += v
    return total

def label_graph(edges, labels=2, lam=4):
    """Small exact reference derandomizer; polynomial, not engineered for speed."""
    groups, tau, hs = packing_data(edges, labels, lam)
    vertices = sorted({('L', e[0]) for e in edges} | {('R', e[1]) for e in edges})
    assignment = {}
    previous = potential(groups, hs, labels, lam, assignment)
    initial = previous
    trace = []
    for vertex in vertices:
        values = [potential(groups, hs, labels, lam, {**assignment, vertex:a})
                  for a in range(labels)]
        if sum(values, F(0))/labels != previous:
            raise ArithmeticError('conditional expectation identity failed')
        chosen = min(range(labels), key=lambda a: (values[a], a))
        assignment[vertex] = chosen
        previous = values[chosen]
        trace.append(previous)
    loads = [[0]*labels for _ in range(labels)]
    for left, right in edges:
        loads[assignment['L', left]][assignment['R', right]] += 1
    return dict(assignment=assignment, loads=loads, groups=groups, tau=tau,
                thresholds=hs, initial=initial, final=previous, trace=trace)

def log_interval_positive(x, terms):
    """Rigorous ln(x) interval for 1<=x<=2 via atanh; exact fractions."""
    if not isinstance(x, (int, F)):
        raise ValueError('integer or exact Fraction argument required')
    if not isinstance(terms, int) or terms < 1:
        raise ValueError('positive integer term count required')
    x=F(x)
    if not 1 <= x <= 2:
        raise ValueError('range')
    z=(x-1)/(x+1)
    lo=2*sum((z**(2*j+1)/F(2*j+1) for j in range(terms)), F(0))
    tail=2*z**(2*terms+1)/(F(2*terms+1)*(1-z*z))
    return lo,lo+tail

def exact_budget(lam, divisor=20):
    """floor(lambda/(divisor*log2(54))), using certified logarithm intervals.

    Equivalent to max a with 54**(divisor*a)<=2**lambda, but does not
    allocate lambda bits for gigantic illustrative lambda values.
    Equality is impossible for lambda>0, a>0 (prime factor 3).
    """
    if not isinstance(lam, int) or lam < 1 or not isinstance(divisor, int) or divisor < 1:
        raise ValueError('positive integer lambda and divisor required')
    terms=8
    while True:
        l2,h2=log_interval_positive(F(2),terms)
        # ln 54 = 6 ln 2 - ln(32/27)
        lx,hx=log_interval_positive(F(32,27),terms)
        l54,h54=6*l2-hx,6*h2-lx
        low=lam*l2/(divisor*h54)
        high=lam*h2/(divisor*l54)
        a,b=low.numerator//low.denominator,high.numerator//high.denominator
        if a==b:
            return a
        terms *= 2

def schedule(lam, root_constant=1):
    if lam < 2 or root_constant < 1:
        raise ValueError('lambda>=2 and integer root constant>=1 required')
    k=ceil_log2(lam); gap=6*k
    depth=0; p=1
    while p < root_constant*lam:
        depth+=1; p*=18
    budget=exact_budget(lam)
    U=budget-(depth+1)*gap-k*k
    us=[8*max(U,0)//(9**(d+1)) for d in range(depth+1)]
    aa=[]; acc=0
    for d,u in enumerate(us):
        acc+=u;aa.append(acc+(d+1)*gap)
    return dict(lam=lam, root_constant=root_constant, k=k, gap=gap,
                depth=depth,budget=budget,U=U,u=us,a=aa,
                basic_guard=U>0 and min(us)>=2)

def precision(M,a,u,p):
    """Inherited exact linear-taper schedule. Does not assert packing guards."""
    if not 1<=u<=min(a,M) or p<1:
        raise ValueError('invalid Hermite parameters')
    L=1<<a; mass=L*(2*u-2)+(1<<(a+1-u))
    h=M*(2*L-1)//mass+1
    rows=[]
    for i in range(u):
        b=a-i;r=u-i;D=1<<b;q=h*r
        loss=h*(6*D-(2*r+6)*(1<<(a-u))-r*(b+2))
        rows.append(dict(i=i,q=q,D=D,loss=loss,precision=p+loss+(q-1)*(b+1)))
    return dict(h=h,total_conditions=h*mass,degree=M*(2*L-1),rows=rows)

def mode_weight(b):
    if b<0: raise ValueError('nonnegative index')
    return 1+3*b-2*b.bit_count()

def weighted_count(precision, colors):
    """Exact abstract tuple count for infinite Cauchy modes, weight<precision."""
    if precision<1 or colors<0: raise ValueError('invalid inputs')
    dp=[0]*precision;dp[0]=1;b=0
    while mode_weight(b)<precision:
        w=mode_weight(b)
        for _ in range(colors):
            for p in range(w,precision):dp[p]+=dp[p-w]
        b+=1
    return sum(dp)
