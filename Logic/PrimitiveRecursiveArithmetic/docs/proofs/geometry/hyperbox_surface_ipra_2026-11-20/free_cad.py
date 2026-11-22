"""Reference exact unrestricted solver for rational boxes (SymPy 1.14+).

A full sign-invariant cylindrical decomposition is deliberately used. Beyond
small examples it can exhaust available time or memory. Every returned pair is
calculated using exact arithmetic. --raw forces the general method on rectangles
and box families covered by the closed theorems.
"""
import argparse
from functools import cmp_to_key, lru_cache
from itertools import combinations
import sympy as sp
from hyperbox import develop, rational_box


def enclose(expr, digits):
    if expr.is_Rational:
        return expr,expr
    if isinstance(expr,sp.CRootOf):
        expr.eval_rational(n=digits)  # refines its certified isolating interval
        interval = expr._get_interval()
        return sp.Rational(interval.a), sp.Rational(interval.b)
    supported = expr.is_Add or expr.is_Mul or (expr.is_Pow and expr.exp.is_Integer)
    if not supported:
        u = sp.Dummy('u')
        poly = sp.Poly(sp.minimal_polynomial(expr,u),u)
        if poly.degree() == 1:
            val = -poly.TC()/poly.LC()
            return val,val
        root = next(r for r in poly.real_roots(radicals=False) if poly.same_root(r,expr))
        return enclose(root,digits)
    parts = [enclose(x,digits) for x in expr.args]
    if expr.is_Add:
        return sum(x for x,_ in parts),sum(y for _,y in parts)
    if expr.is_Mul:
        lo=hi=sp.S.One
        for x,y in parts:
            corners = [v*w for v in (lo,hi) for w in (x,y)]
            lo,hi = min(corners),max(corners)
        return lo,hi
    if expr.is_Pow and expr.exp.is_Integer:
        lo,hi = parts[0]
        exp = int(expr.exp)
        if exp<0 and lo<=0<=hi:
            raise ZeroDivisionError
        ends = [lo**exp,hi**exp]
        if exp>0 and exp%2==0 and lo<=0<=hi:
            ends.append(0)
        return min(ends),max(ends)
    raise ValueError(f"Expected rational arithmetic in isolated real roots: {expr}")


@lru_cache(maxsize=12000)
def sign(v):
    v = sp.sympify(v)
    if v.is_Rational:
        return int(sp.sign(v))
    digits = 4
    zero_checked = False
    while True:
        try:
            a,b = enclose(v,digits)
            if a>0: return 1
            if b<0: return -1
            if a==b==0: return 0
        except ZeroDivisionError:
            pass
        if not zero_checked:
            u=sp.Dummy('u')
            if sp.Poly(sp.minimal_polynomial(v,u),u).TC()==0:
                return 0
            zero_checked=True
        digits *= 2


def ordered(a,b):
    return sign(a-b)


def factor_basis(polynomials, variables):
    out=set()
    for expr in set(polynomials):
        if not expr.free_symbols:
            continue
        for factor,_ in sp.factor_list(expr,*variables)[1]:
            if factor.free_symbols:
                out.add(factor)
    return tuple(sorted(out,key=sp.default_sort_key))


def principal_coefficients(f,g,z):
    """Principal subresultants by their Sylvester determinants, before specialization."""
    f,g=sp.Poly(f,z),sp.Poly(g,z)
    m,n=f.degree(),g.degree()
    for k in range(min(m,n)):
        size=m+n-2*k
        rows=[]
        for poly,number in ((f,n-k),(g,m-k)):
            for shift in reversed(range(number)):
                rows.append([poly.nth(j-shift) if j>=shift else sp.S.Zero
                             for j in range(m+n-k-1,k-1,-1)])
        yield sp.Matrix(size,size,[v for row in rows for v in row]).det()


def project(polynomials, variables):
    """Full degree-drop projection. No well-orientedness assumption."""
    z=variables[-1]
    down=set()
    trunc=[]
    for f in polynomials:
        coeff = sp.Poly(f,z).all_coeffs()
        down.update(coeff)
        versions=[]
        for i,c in enumerate(coeff[:-1]):
            if c==0: continue
            version=sp.Poly.from_list(coeff[i:],z).as_expr()
            versions.append(version)
            # Rank data for (f,f') fixes the number of distinct roots.
            down.update(principal_coefficients(version,sp.diff(version,z),z))
        trunc.append(versions)
    # Pairwise data keep coincident roots of different basis members aligned.
    for left,right in combinations(trunc,2):
        for f in left:
            for g in right:
                down.update(principal_coefficients(f,g,z))
    return factor_basis(down,variables[:-1])


def real_roots(polynomials,var,sub):
    roots=set()
    for f in polynomials:
        p=sp.Poly(f.subs(sub),var,extension=True)
        if p.degree()>0:
            roots.update(p.real_roots(radicals=False))
    order=sorted(roots,key=cmp_to_key(ordered))
    return [a for i,a in enumerate(order) if i==0 or ordered(a,order[i-1])]


def rational_between(left,right):
    if left.is_Rational and right.is_Rational:
        return (left+right)/2
    digits=4
    while True:
        _,lo=enclose(left,digits)
        hi,_=enclose(right,digits)
        if lo<hi: return (lo+hi)/2
        digits*=2


def stack_in_box(poly,z,sub,upper):
    roots=[r for r in real_roots(poly,z,sub) if sign(r)>=0 and sign(upper-r)>=0]
    # Every coordinate's two walls were in the input family, and project unchanged.
    for i,r in enumerate(roots):
        yield r
        if i+1<len(roots):
            yield rational_between(r,roots[i+1])


def legal(z,site,gates):
    earliest=sp.S.Zero
    for gate in gates:
        first,last=earliest,sp.S.One
        for x,y,(lo,hi) in zip(z,site,gate):
            delta=y-x
            direction=sign(delta)
            if direction==0:
                if sign(x-lo)<0 or sign(hi-x)<0: return False
            else:
                l,r=(lo-x)/delta,(hi-x)/delta
                if direction<0: l,r=r,l
                if sign(l-first)>0: first=l
                if sign(last-r)>0: last=r
                if sign(last-first)<0: return False
        earliest=first
    return True


def on_chart(sides,target,source,minimum,upper):
    n=len(sides)
    h=sp.Symbol('height')
    coords=list(sp.symbols(f'z0:{2*n-2}'))
    variables=[h]+coords
    m=n-1
    q=coords[:m].copy()
    p=coords[m:].copy()
    q.insert(target//2,sides[target//2]*(target%2))
    p.insert(source//2,sides[source//2]*(source%2))
    bound=[a for i,a in enumerate(sides) if i!=target//2]+[
           a for i,a in enumerate(sides) if i!=source//2]
    z=q[:target//2]+q[target//2+1:]
    worlds=[]
    inputs=[h-minimum,h-upper]
    for x,a in zip(coords,bound): inputs.extend((x,x-a))
    for frame,gates in develop(sides,target,{source},set()):
        s=[o+sig*p[i] for i,sig,o in frame]
        poly=sp.expand(sum((x-y)**2 for x,y in zip(s,z))-h)
        worlds.append((s,gates,poly))
        inputs.append(poly)
    levels=[factor_basis(inputs,variables)]
    for k in range(len(variables),1,-1):
        levels.append(project(levels[-1],variables[:k]))
    levels.reverse()

    def witness(sub,idx):
        if idx==len(coords):
            anchor=[x.subs(sub) for x in z]
            meets=False
            for site,gates,diff in worlds:
                cmp=sign(diff.subs(sub))
                if cmp>0: continue
                if legal(anchor,[x.subs(sub) for x in site],gates):
                    if cmp<0: return None
                    meets=True
            if meets:
                return tuple(x.subs(sub) for x in p),tuple(x.subs(sub) for x in q)
            return None
        x=coords[idx]
        for r in stack_in_box(levels[idx+1],x,sub,bound[idx]):
            sub[x]=r
            wp=witness(sub,idx+1)
            del sub[x]
            if wp is not None: return wp
        return None

    for value in reversed(real_roots(levels[0],h,{})):
        if sign(value-minimum)<=0 or sign(upper-value)<0: continue
        w=witness({h:value},0)
        if w is not None: return value,w
    return None


def diameter(sides, raw=False):
    sides=tuple(sp.Rational(x) for x in rational_box(sides))
    n=len(sides)
    ordered_sides=sorted(sides)
    ss=sum(x*x for x in sides)
    best=ss+2*ordered_sides[0]*ordered_sides[1]
    upper=ss+2*ordered_sides[-1]*ordered_sides[-2]
    pair=((sp.S.Zero,)*n,sides)
    if not raw and (n==2 or ordered_sides[1]==ordered_sides[-1]):
        return best,pair
    if not raw and ordered_sides[0]==ordered_sides[-2]:
        base=ordered_sides[0]
        height=ordered_sides[-1]/base
        if height >= n-1 or n >= 6:
            if n >= 6 and height <= 2:
                return best,pair
            delta=(height-sp.sqrt(height**2-1))/2
            low=tuple(0 if a==ordered_sides[-1] else base*(sp.Rational(1,2)-delta)
                      for a in sides)
            high=tuple(a-x for a,x in zip(sides,low))
            square=sp.expand(base**2*((height+1)**2+4*(n-2)*delta**2))
            if square <= best:
                return best,pair
            return square,(low,high)
    for i in range(n):
        for j in range(i,n):
            # Distinct axes can be reflected independently, and swapping
            # endpoints interchanges their axes. Same-axis uses opposite facets.
            result=on_chart(sides,2*i,2*j+int(i==j),best,upper)
            if result is not None: best,pair=result
    return best,pair


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('sides',help='comma-separated positive rationals')
    parser.add_argument('--raw',action='store_true')
    parser.add_argument('--compare',action='store_true',help='also compute fixed-vertex outcome and compare exactly')
    args=parser.parse_args()
    sq,pair=diameter(args.sides.split(','),args.raw)
    print('D squared =',sq)
    print('P =',pair[0])
    print('Q =',pair[1])

    if args.compare:
        from hyperbox import vertex_maximum
        fixed=vertex_maximum(args.sides.split(','))
        print('E squared =',fixed['squared'])
        print('Y =',tuple(map(sp.Rational,fixed['point'])))
        difference=sq-sp.Rational(fixed['squared'])
        if difference.has(sp.CRootOf):
            larger=(sign(difference)>0)
        else:
            larger=bool(difference>0)
        print('Strict improvement =', larger)
