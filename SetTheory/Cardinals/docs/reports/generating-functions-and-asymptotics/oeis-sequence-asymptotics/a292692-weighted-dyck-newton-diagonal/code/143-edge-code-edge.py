#!/usr/bin/env python3
"""Report143 exact finite checks; no external packages, fitting, or file writes.

The ordinary-polynomial recurrence is regenerated here. Independent scalar
values/forward differences, signed and second-kind Stirling conversions,
and the elementary-symmetric product cross-check the normalizations.
Finite checks corroborate, and never replace, the article's uniform proof.
"""
import sys
if not sys.flags.isolated:
    sys.stderr.write('REJECTED: isolated Python (-I) is required before any imports\n')
    raise SystemExit(2)
sys.dont_write_bytecode = True


from fractions import Fraction as F
from math import comb, factorial
import json


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def multiply(a, b):
    c = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i+j] += x*y
    return c


def evaluate(p, x):
    value = 0
    for a in reversed(p):
        value = value*x+a
    return value


def falling(n, j):
    value = 1
    for i in range(j):
        value *= n-i
    return value


def constants(limit):
    V = [1]
    L = [F(1)]
    for a in range(1, limit+1):
        V.append((4*a-2)*V[-1]+sum(V[b]*V[a-1-b] for b in range(a)))
        L.append(L[-1]/a + sum(L[b]*L[a-1-b]*F(factorial(2*b)*factorial(2*(a-1-b)), factorial(2*a)) for b in range(a)))
        need(L[-1] == F(V[-1], factorial(2*a)), 'L and V recurrence identity')
    return V, L


def generate(limit):
    p, elementary, S, first = [[1]], [[1]], [[1]], [[1]]
    for n in range(1, limit+1):
        row = [0]*(n+1)
        for k, value in enumerate(p[-1]):
            row[k] += (2*n-2)*value
            row[k+1] += value
        for i in range(n):
            for k, value in enumerate(multiply(p[i], p[n-1-i])):
                row[k] += value
        p.append(row)
        elementary.append(multiply(elementary[-1], [2*n-1, 1]))
        prev = S[-1]
        S.append([(prev[k-1] if k else 0)+(k*prev[k] if k<len(prev) else 0) for k in range(n+1)])
        first.append(multiply(first[-1], [1-n, 1]))
    return p, elementary, S, first


def interpolate(values):
    # Newton interpolation on consecutive integers, converted to ordinary powers.
    work = [F(v) for v in values]
    result = [F(0)]*len(values)
    basis = [F(1)]
    for k in range(len(values)):
        for i, value in enumerate(basis):
            result[i] += work[0]*value/factorial(k)
        work = [b-a for a, b in zip(work, work[1:])]
        basis = multiply(basis, [-k, 1])
    return result


def run():
    limit, amax, order = 60, 80, 7
    p, elementary, S, first = generate(limit)
    V, L = constants(amax)
    c = lambda a, n: p[n][n-a] if 0<=a<=n else 0
    E = lambda a, n: elementary[n][n-a] if 0<=a<=n else 0
    P = [[sum(p[n][k]*S[k][m] for k in range(m, n+1)) for m in range(n+1)] for n in range(limit+1)]
    Q = [[sum(elementary[n][k]*S[k][m] for k in range(m, n+1)) for m in range(n+1)] for n in range(limit+1)]
    counts = dict(top_sandwich=0, p_sandwich=0, q_sandwich=0,
                  stirling_sandwich=0, elementary_sandwich=0,
                  coefficient_first_difference=0, coefficient_telescoping=0,
                  scalar_polynomial=0, scalar_newton=0, signed_stirling=0,
                  newton_extraction=0, smoothing_identity=0, W_convolution=0,
                  normalization_ratio=0, polynomial_values=0, h_monotonicity=0,
                  profile_monotonicity=0, exact_disjoint_split=0,
                  exact_ratio_product=0, connected_bounds=0)
    # Independent scalar recurrence at each integer k, then exact differences.
    scalar = [[1]*(limit+1)]
    for n in range(limit+1):
        if n:
            scalar.append([(k+2*n-2)*scalar[n-1][k]+sum(scalar[i][k]*scalar[n-1-i][k] for i in range(n)) for k in range(limit+1)])
        for k in range(limit+1):
            need(scalar[n][k] == evaluate(p[n], k), 'scalar/polynomial recurrence')
            counts['scalar_polynomial'] += 1
        differences = scalar[n][:n+1]
        for m in range(n+1):
            need(differences[0] == factorial(m)*P[n][m], 'scalar Newton normalization')
            differences = [b-a for a,b in zip(differences, differences[1:])]
            counts['scalar_newton'] += 1
        for k in range(n+1):
            need(p[n][k] == sum(P[n][m]*first[m][k] for m in range(k,n+1)), 'signed Stirling inverse')
            counts['signed_stirling'] += 1
    cumulative = [0]*(amax+1)
    for n in range(limit+1):
        for a in range(amax+1):
            if a==0:
                need(c(a,n)==1, 'monic coefficient')
            else:
                scaled = c(a,n)*factorial(2*a)
                need(V[a]*max(n-2*a,0)**(2*a) <= scaled <= V[a]*(n+a)**(2*a), 'all-index top sandwich')
            counts['top_sandwich'] += 1
        if n:
            for a in range(1, n+2):
                delta = 2*(n-1)*c(a-1,n-1)+sum(c(b,i)*c(a-1-b,n-1-i) for b in range(a) for i in range(n))
                need(c(a,n)-c(a,n-1)==delta, 'coefficient first difference')
                counts['coefficient_first_difference'] += 1
                cumulative[a] += delta
        for a in range(1,amax+1):
            need(c(a,n)==cumulative[a], 'telescoped coefficient identity')
            counts['coefficient_telescoping'] += 1
        for q in range(n//2+1):
            if q==0:
                need(P[n][n]==Q[n][n]==1, 'q=0 exact case')
            else:
                K = sum(L[a]/(2**(q-a)*factorial(q-a)) for a in range(q+1))
                C = F(3,2)**q/factorial(q)
                need(K*(n-2*q)**(2*q)<=P[n][n-q]<=K*(n+q)**(2*q), 'P sandwich')
                need(C*(n-2*q)**(2*q)<=Q[n][n-q]<=C*n**(2*q), 'Q sandwich')
            counts['p_sandwich'] += 1
            counts['q_sandwich'] += 1
            need(P[n][n-q]==sum(c(a,n)*S[n-a][n-q] for a in range(q+1)), 'P extraction')
            need(Q[n][n-q]==sum(E(a,n)*S[n-a][n-q] for a in range(q+1)), 'Q extraction')
            counts['newton_extraction'] += 2
        for j in range(n//2+1):
            if j==0:
                need(S[n][n]==1 and E(0,n)==1, 'zero index boundary')
            else:
                need(falling(n,2*j)<=S[n][n-j]*2**j*factorial(j)<=n**(2*j), 'Stirling sandwich')
                need((n-2*j)**(2*j)<=E(j,n)*factorial(j)<=n**(2*j), 'elementary sandwich')
            counts['stirling_sandwich'] += 1
            counts['elementary_sandwich'] += 1
        if n:
            gamma = F(comb(2*n,n),4**n)
            gamma_next = F(comb(2*n+2,n+1),4**(n+1))
            need(F(n,n+1)*(gamma/gamma_next)**2 == 1-F(1,(2*n+1)**2), 'central-binomial normalization ratio')
            counts['normalization_ratio'] += 1
    w = [F(1)]
    for n in range(1,amax+1):
        w.append(w[-1]*F((4*n-3)*(4*n-1),4*n))
        need(4*n*w[n]==sum(V[j]*w[n-j] for j in range(1,n+1)), 'formal W identity')
        counts['W_convolution'] += 1
    # Finite exact identities underlying the fixed-order endpoint algorithm.
    for n in range(1,amax+1):
        vn=F(V[n])/(4*n*w[n])
        need(0<vn<=1, 'positive connected normalization')
        counts['connected_bounds'] += 1
        midpoint=n//2
        left=vn+sum(F(n-l,n)*w[l]*w[n-l]/w[n]
                    *F(V[n-l])/(4*(n-l)*w[n-l])
                    for l in range(1,midpoint+1))
        right=1-sum(F(V[j])*w[n-j]/(4*n*w[n])
                    for j in range(1,n-midpoint))
        need(left==right, 'exact disjoint endpoint split')
        counts['exact_disjoint_split'] += 1
        product=F(1)
        h=F(1,n)
        for l in range(n+1):
            need(w[n-l]/w[n]==F(1,4**l)*h**l*product,
                 'exact shifted W ratio product')
            counts['exact_ratio_product'] += 1
            if l<n:
                product*=((1-l*h)/((1-(F(l)+F(1,4))*h)
                                       *(1-(F(l)+F(3,4))*h)))
    K = []
    for q in range(amax+1):
        value = sum(L[a]/(2**(q-a)*factorial(q-a)) for a in range(q+1))
        mean = sum(F(comb(q,a)*2**a,3**q)*factorial(a)*L[a] for a in range(q+1))
        need(factorial(q)*value==F(3,2)**q*mean, 'binomial smoothing identity')
        counts['smoothing_identity'] += 1
        K.append(value)
        if q:
            hn=factorial(q)*L[q]
            need(hn-factorial(q-1)*L[q-1] == F(factorial(q),factorial(2*q))*sum(V[b]*V[q-1-b] for b in range(q)), 'h increment identity')
            need(hn>factorial(q-1)*L[q-1], 'strict h monotonicity')
            counts['h_monotonicity'] += 1
            need(value*factorial(q)*F(2,3)**q > K[q-1]*factorial(q-1)*F(2,3)**(q-1), 'strict profile monotonicity')
            counts['profile_monotonicity'] += 1
    polynomials = []
    for a in range(order+1):
        coefficients = interpolate([c(a,n) for n in range(2*a+1)])
        need(coefficients[-1]==L[a], 'top leading coefficient')
        for n in range(limit+1):
            need(evaluate(coefficients,n)==c(a,n), 'top polynomial values')
            counts['polynomial_values'] += 1
        polynomials.append({'a':a,'degree':2*a,'coefficients':[str(v) for v in coefficients]})
    # Short exact samples preserve more than counters in the sealed fixture.
    rows = []
    for n in (0,1,2,4,8,16,30,60):
        rows.append({'n':n,'ordinary':[str(v) for v in p[n]],
                     'newton':[str(v) for v in P[n]],
                     'auxiliary_newton':[str(v) for v in Q[n]]})
    return {'maximum_n':limit,'maximum_a':amax,'polynomial_order':order,
            'counts':counts,'V_initial':[str(v) for v in V[:12]],
            'L_initial':[str(v) for v in L[:12]],'K_initial':[str(v) for v in K[:12]],
            'top_polynomials':polynomials,'rows':rows}


if __name__=='__main__':
    print(json.dumps(run(),sort_keys=True,indent=2))
