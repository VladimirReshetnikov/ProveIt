"""Independent exact coefficient test for the low dyadic shell formula.
All arithmetic is integer arithmetic. F_s = Q_2(zeta_{2^s}), t=zeta-1.
The power basis in t has distinct valuations modulo v(2). Congruences
modulo a power of t become rows of integer linear congruences mod powers
of 2, tested by successive elimination of unit pivots and division by 2.
"""
from fractions import Fraction
from math import comb


def multiply(a, b, polynomial):
    n = len(polynomial)
    tmp = [0] * (2*n-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            tmp[i+j] += x*y
    for i in reversed(range(n, len(tmp))):
        c = tmp[i]
        if c:
            for j, fj in enumerate(polynomial):
                tmp[i-n+j] -= c*fj
    return tmp[:n]


def unit_power_minus_one(t_power, polynomial):
    # (1+t)^exponent - 1 at a primitive (2n)-th root.
    n = len(polynomial)
    exp = t_power % (2*n)
    sign = 1 if exp < n else -1
    exp %= n
    coeffs = [sign*comb(exp, j) if j <= exp else 0 for j in range(n)]
    coeffs[0] -= 1
    return coeffs


def congruences_solvable(mat, mod):
    """Does A*x = b (last column) admit a solution mod a power of 2?"""
    rows = [row[:] for row in mat]
    while rows and mod > 1:
        pivot = next(((i,j) for i,row in enumerate(rows)
                      for j,x in enumerate(row[:-1]) if x % 2), None)
        if pivot is None:
            if any(row[-1] % 2 for row in rows):
                return False
            rows = [[x//2 for x in row] for row in rows]
            mod //= 2
            continue
        i,j = pivot
        pivotrow = rows.pop(i)
        inv = pow(pivotrow[j], -1, mod)
        pivotrow = [(x*inv) % mod for x in pivotrow]
        for row in rows:
            scale = row[j]
            if scale:
                row[:] = [(x-scale*y) % mod for x,y in zip(row,pivotrow)]
            row.pop(j)
    return True


def check_levels(s, h, c):
    ns, nh = 1 << (s-1), 1 << (h-1)
    cyclo = [comb(ns,i) for i in range(ns)]
    cyclo[0] += 1
    one = [1]+[0]*(ns-1)
    uniformizer = [0,1]+[0]*(ns-2)
    # Norm of t to A=F_s^{<c>} has valuation 2/ns. Its first ns/2
    # powers are an integer basis of the totally ramified field A.
    normt = multiply(uniformizer,unit_power_minus_one(c, cyclo),cyclo)
    abasis = [one]
    for _ in range(ns//2-1):
        abasis.append(multiply(abasis[-1],normt,cyclo))
    blocks = []
    for a in range(1, 2*nh, 2):
        z = unit_power_minus_one((ns//nh)*a, cyclo)
        powers = [one]
        for _ in range(nh):
            powers.append(multiply(powers[-1],z,cyclo))
        products = [multiply(v, u, cyclo) for v in powers[:-1] for u in abasis]
        blocks.append((powers, products))
    def feasible(m, k):
        exponent = (k+ns-1)//ns
        mod = 1 << exponent
        rows = []
        for powers, products in blocks:
            for j in range(ns):
                # valuation of the coefficient times t^j must be >= k/ns.
                e_j = max(0, (k-j+ns-1)//ns)
                if e_j:
                    weight = 1 << (exponent-e_j)
                    rows.append([(v[j]*weight)%mod for v in products[:m*len(abasis)]]
                                + [(-powers[m][j]*weight)%mod])
        return congruences_solvable(rows,mod)
    for m in range(1,nh):
        even = m-m%2
        excess = Fraction(sum((1 << (i-1))*(even//(1 << (i-1)))
                              for i in range(1,h)),nh)
        if m % 2:
            excess += Fraction(1,nh)-Fraction(1,ns)
        optimum = (Fraction(m,nh)+excess)*ns
        assert optimum.denominator == 1
        k = int(optimum)
        assert feasible(m,k) and not feasible(m,k+1), (h,s,c,m,k)
    return nh-1


if __name__ == '__main__':
    total = 0
    for s in (3,4,5,6):
        for h in range(2,s):
            for c in ((1 << s)-1, (1 << (s-1))-1):
                total += check_levels(s,h,c)
    print(f'Exact linear congruences certified {total} degree/shell/involution optima.')
    print('All early shells at conductor levels 3 through 6; attainment and strict failure checked.')
