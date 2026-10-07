#!/usr/bin/env python3
"""Report203: deterministic standard-library exact finite checks.

Adapted from the separately written mathematical audit implementation. It is
not a new independent reimplementation. No coefficient-producer code is
imported or executed here. Explicit exceptions remain active under python -O.
Finite tests diagnose implementation mistakes; they do not prove asymptotics.
"""
import sys
sys.dont_write_bytecode = True
from fractions import Fraction as F
from math import comb, factorial, prod
from itertools import combinations
from collections import Counter
import json

COUNTS = Counter()

def check(ok, label):
    if not ok:
        raise RuntimeError('CHECK FAILED: ' + label)
    COUNTS[label.split(':')[0]] += 1

def same(a, b, label):
    check(a == b, label)

def conv(a, b, n):
    c = [F(0)] * (n+1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            if i+j <= n:
                c[i+j] += x*y
    return c

def exponential(a, n):
    if a[0] != 0:
        raise ValueError('Requires a zero constant term')
    e = [F(1)]
    for j in range(1, n+1):
        e.append(sum(F(k)*a[k]*e[j-k] for k in range(1, j+1))/j)
    return e

def cumulants(r, n):
    # Direct formal composition exp(t) exp(r(exp(t)-1))/(1+r).
    e = [F(1, factorial(j)) for j in range(n+1)]
    v = [F(0)] + [r*x for x in e[1:]]
    phi = conv(e, exponential(v, n), n)
    return [phi[j]*factorial(j)/(1+r) for j in range(n+1)]

def poly_add_scaled_shift(dst, src, factor, shift):
    for degree, c in src.items():
        dst[degree+shift] = dst.get(degree+shift, F(0)) + factor*c

def moment(degree, b):
    if degree % 2:
        return F(0)
    return F((-1)**(degree//2)*prod(range(1, degree, 2)), 1)/b**(degree//2)

def saddle_from_exponential(r, J):
    # Expand the non-Gaussian exponential by its differential equation in epsilon.
    kap = cumulants(r, 2*J+2)
    polynomials = [{0: F(1)}]
    for h in range(1, 2*J+1):
        p = {}
        for j in range(1, h+1):
            poly_add_scaled_shift(p, polynomials[h-j],
                                  F(j, h)*kap[j+2]/factorial(j+2), j+2)
        polynomials.append(p)
    saddle = [sum(c*moment(d, kap[2]) for d, c in polynomials[2*j].items())
              for j in range(J+1)]
    for h in range(1, 2*J+1, 2):
        same(sum(c*moment(d, kap[2]) for d, c in polynomials[h].items()),
             0, 'odd_gaussian_cancellation')
    return saddle

def saddle_from_multiindices(r, J):
    # Direct evaluation of the displayed finite recipe, independent of the engine above.
    kap = cumulants(r, 2*J+2)
    ans = [F(1)]
    for ell in range(1, J+1):
        total = F(0)
        def visit(j, weight, degree, coefficient):
            nonlocal total
            if j == 2*ell+3:
                if weight == 0:
                    total += coefficient*moment(degree, kap[2])
                return
            for count in range(weight//(j-2)+1):
                visit(j+1, weight-(j-2)*count, degree+j*count,
                      coefficient*kap[j]**count/F(factorial(count)*factorial(j)**count))
        visit(3, 2*ell, 0, F(1))
        ans.append(total)
    return ans

def stirling(J):
    B = [F(1)]
    for n in range(1, J+2):
        B.append(-sum(F(comb(n+1,k))*B[k] for k in range(n))/F(n+1))
    log = [F(0)]*(J+1)
    for h in range(1, J+1, 2):
        log[h] = B[h+1]/F(h*(h+1))
    return exponential(log, J)

def correction_coefficients(r, J):
    return conv(stirling(J), saddle_from_exponential(r, J), J)

def exact_sum(n, M):
    return sum(F(comb(n,k))*k**(n-k)*F(n)**(k-2)*M**(k-1)
               for k in range(1, n+1))

def exact_rooted_assembly(n, M):
    # Labelled rooted-block recurrence; v is fixed at nM for this whole calculation.
    v = n*M
    B = [F(1)]
    for h in range(1,n+1):
        B.append(sum(F(comb(h-1,j-1))*j*v*B[h-j] for j in range(1,h+1)))
    return B[n]/(M*n*n)

def restricted_growth(n):
    def rec(a, maxval):
        if len(a) == n:
            yield tuple(a)
            return
        for k in range(maxval+2):
            yield from rec(a+[k], max(k,maxval))
    yield from rec([0],0)

def original_model_polynomial(n):
    # Enumerate actual vertex-edge sets, then test acyclicity after block contraction.
    # No Cayley/Pruefer or weighted-tree identity is used by this counter.
    counts = [0]*n
    partition_count = 0
    candidate_count = 0
    for partition in restricted_growth(n):
        partition_count += 1
        k = 1+max(partition)
        this_partition = 0
        edges = [(partition[i],partition[j]) for i in range(n) for j in range(i)
                 if partition[i] != partition[j]]
        for selected in combinations(edges,k-1):
            candidate_count += 1
            parent = list(range(k))
            def root(i):
                while parent[i] != i:
                    i = parent[i]
                return i
            good = True
            for a,b in selected:
                a,b = root(a),root(b)
                if a == b:
                    good = False
                    break
                parent[a] = b
            if good:
                counts[k-1] += 1
                this_partition += 1
        sizes = Counter(partition)
        same(this_partition,F(n)**(k-2)*prod(sizes.values()),
             'individual_partition_weighted_Cayley')
    return counts, partition_count, candidate_count

def elementary_list(d, J):
    e = [1]+[0]*J
    for a in list(range(d))+[d]*d:
        for j in range(J,0,-1):
            e[j] += a*e[j-1]
    return e

def fdeficit(n,d):
    if d >= n:
        return F(0)
    return prod(F(n-i,n) for i in range(d))*F(n-d,n)**d

def exact_inverse(y,M):
    low,high = 0,1
    while exact_sum(high,M)<y:
        low,high = high,2*high
    while high-low>1:
        middle=(low+high)//2
        if exact_sum(middle,M)>=y:
            high=middle
        else:
            low=middle
    return high

def power(a, exponent, J):
    """Truncated ordinary power, using only rational arithmetic."""
    result = [F(1)] + [F(0)]*J
    for unused in range(exponent):
        result = conv(result, a, J)
    return result

def inverse_residual_expanded(ps, L, B, ds, J):
    """Explicit fixed-M inverse residual; ds[j] is d_j (ds[0] unused).

    u=1/t, h=sum p_k u^k. L and B are formal constants at the chosen t.
    This is an arbitrary finite-order recipe, not a convergence statement.
    """
    h = list(ps) + [F(0)]*(J+1-len(ps))
    result = [L*c for c in h[:J+1]]
    result[0] -= B
    for m in range(2, J+2):
        term = power(h, m, J)
        for k in range(J-m+2):
            result[k+m-1] += F((-1)**m, m*(m-1))*term[k]
    for m in range(1, J+1):
        term = power(h, m, J)
        for k in range(J-m+1):
            result[k+m] -= F(2*(-1)**(m+1),m)*term[k]
    for j in range(1,J+1):
        for m in range(J-j+1):
            term = power(h, m, J)
            factor = ds[j]*(-1)**m*comb(j+m-1,m)
            for k in range(J-j-m+1):
                result[k+j+m] += factor*term[k]
    return result

def inverse_coefficients(L, B, ds, J):
    """Solve successively through p_J; valid for any requested finite J."""
    L,B = F(L),F(B)
    ds = [F(d) for d in ds]
    if L == 0 or len(ds) <= J:
        raise ValueError('Need nonzero L and d_1 through d_J')
    ps = [B/L]
    for k in range(1,J+1):
        residual = inverse_residual_expanded(ps, L, B, ds, k)
        ps.append(-residual[k]/L)
    return ps

def inverse_residual_composed(ps, L, B, ds, J):
    """Second evaluation using formal log and geometric series composition.

    (t+h)log(q(t+h))-tlog(qt)
      = (L-1)h + log(1+uh)/u + h log(1+uh).
    """
    h = list(ps) + [F(0)]*(J+2-len(ps))
    v = [F(0)] + h[:J+1]
    logarithm = [F(0)]*(J+2)
    geometric = [F(0)]*(J+2)
    for m in range(J+2):
        term = power(v,m,J+1)
        for k in range(J+2):
            geometric[k] += (-1)**m*term[k]
            if m:
                logarithm[k] += F((-1)**(m+1),m)*term[k]
    hlog = conv(h,logarithm,J)
    result = [(L-1)*h[k]+logarithm[k+1]+hlog[k]-2*logarithm[k]
              for k in range(J+1)]
    result[0] -= B
    for j in range(1,J+1):
        term = power(geometric,j,J)
        for k in range(J-j+1):
            result[k+j] += ds[j]*term[k]
    return result

def run():
    oeis = [1,2,10,89,1156,19897,428002,11067457,334667368,11593751921,
            452892057454,19699549177585,944416040000044,49480473036710185,
            2812998429218735986,172475808692526176513,11345688093224067380176]
    for n,v in enumerate(oeis,1):
        same(exact_rooted_assembly(n,F(1)),v,'reference_A055779_terms')
    ms = [F(1,10),F(1,2),F(1),F(3,2),F(2),F(10),F(1000)]
    for n in range(1,41):
        for M in ms:
            a = exact_sum(n,M)
            same(a,exact_rooted_assembly(n,M),'assembly_vs_sum')
            check(exact_sum(n+1,M)>=(1+M)*a,'monotonicity')
            base = F(n)**(n-2)*M**(n-1)
            same(a/base,sum((F(n)/M)**d*fdeficit(n,d)/factorial(d) for d in range(n)),
                 'deficit_normalization')
    for M in [F(1),F(3,2),F(2),F(10)]:
        same(exact_inverse(F(1),M),1,'inverse_at_initial_value')
        for n in range(2,26):
            a=exact_sum(n,M)
            gap=min(a-exact_sum(n-1,M),exact_sum(n+1,M)-a)/3
            for delta,expected in [(-gap,n),(F(0),n),(gap,n+1)]:
                same(exact_inverse(a+delta,M),expected,'inverse_direct_integer_boundaries')
    enumeration = []
    for n in range(1,7):
        cs,pcs,ecs = original_model_polynomial(n)
        expected = [F(comb(n,k))*k**(n-k)*F(n)**(k-2) for k in range(1,n+1)]
        same(cs,expected,'original_vertex_edge_enumeration')
        enumeration.append({'n':n,'partitions':pcs,'candidate_edge_sets':ecs,'polynomial':cs})
    rvalues = [F(0),F(1,1000000),F(1,20),F(1,10),F(1,4),F(2,5),F(4,9)]
    samples = []
    for r in rvalues:
        s = saddle_from_exponential(r,6)
        same(s,saddle_from_multiindices(r,6),'saddle_engines_through_order_6')
        cs = conv(stirling(6),s,6)
        if r == 0:
            same(cs,[F(1)]+[F(0)]*6,'endpoint_stirling_cancellation')
        samples.append({'r':str(r),'c':[str(c) for c in cs]})
    same(stirling(3),[F(1),F(1,12),F(1,288),F(-139,51840)],'stirling_initial')
    inverse_samples = []
    inverse_order = 8
    # Algebraic values test the fixed-M formal rule. They are not parameter
    # samples establishing uniformity, or numerical claims about an inverse.
    for L,B in [(F(1),F(0)),(F(2),F(1)),(F(3),F(-2)),
                (F(7,2),F(5,3)),(F(11),F(17)),(F(100),F(201))]:
        ds = [F(0)]+[F((-1)**j*(j+1),j*j+1) for j in range(1,inverse_order+1)]
        ps = inverse_coefficients(L,B,ds,inverse_order)
        residual = inverse_residual_composed(ps,L,B,ds,inverse_order)
        for k, value in enumerate(residual):
            same(value,0,'inverse_composed_cancellation')
        for k in range(1,inverse_order+1):
            changed = ps[:]
            changed[k] += 1
            delta = inverse_residual_composed(changed,L,B,ds,k)[k]-residual[k]
            same(delta,L,'inverse_recursion_linear_coefficient')
        same(ps[0],B/L,'inverse_displayed_p0')
        same(ps[1],-(ps[0]**2/2-2*ps[0]+ds[1])/L,'inverse_displayed_p1')
        same(ps[2],-((ps[0]-2)*ps[1]-ps[0]**3/6+ps[0]**2-ds[1]*ps[0]+ds[2])/L,
             'inverse_displayed_p2')
        inverse_samples.append({'L':str(L),'B':str(B),
                                'p0_to_p8':[str(p) for p in ps]})
    for n in range(1,41):
        for d in range(81):
            f = fdeficit(n,d)
            A = F(3*d*d-d,2)
            check(0 <= 1-f <= A/n,'bonferroni_P1_first')
            check(0 <= f-1+A/n <= A*A/(2*n*n),'bonferroni_P1_second')
            es = elementary_list(d,6)
            for J in range(6):
                poly = sum(F((-1)**j*es[j],n**j) for j in range(J+1))
                bound = (A/n)**(J+1)*sum(F(1,factorial(j)) for j in range(J+1))
                if d<n:
                    bound = F(es[J+1],n**(J+1))
                check(abs(f-poly)<=bound,'all_order_Bonferroni')
    # Negative controls prove that tests discriminate common normalization/sign mistakes.
    check(exact_sum(3,F(2)) != 2*exact_sum(3,F(2)),'negative_missing_M')
    check(exact_rooted_assembly(3,F(1)) != 9*exact_sum(3,F(1)),'negative_missing_n_squared')
    kap = cumulants(F(1,4),4)
    correct = saddle_from_exponential(F(1,4),1)[1]
    wrong = kap[4]/(8*kap[2]**2)+5*kap[3]**2/(24*kap[2]**3)
    check(correct != wrong,'negative_saddle_sign')
    return {'status':'PASS','implementation_origin':'adapted prior independent audit',
            'checks_use_assert':False,'counts':dict(sorted(COUNTS.items())),
            'original_model_enumeration':enumeration,
            'coefficient_samples':samples,
            'fixed_M_inverse_formal_recursion':{'maximum_tested_order':inverse_order,
                                                'samples':inverse_samples},
            'scope':'Exact finite identities and symbolic recipe diagnostics; not proofs of uniform asymptotics.'}

if __name__ == '__main__':
    print(json.dumps(run(),indent=2,sort_keys=True))
