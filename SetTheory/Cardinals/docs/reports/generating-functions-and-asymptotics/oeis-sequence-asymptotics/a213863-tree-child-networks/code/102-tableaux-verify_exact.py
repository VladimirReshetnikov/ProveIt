#!/usr/bin/env python3
"""Independent exact algebra checks. No original derivation module is imported."""
from __future__ import annotations
import argparse
import ast
from datetime import datetime, timezone
from fractions import Fraction as F
import hashlib
import json
from math import factorial
from pathlib import Path
import platform
import sys
import time
import sympy as S

ROOT = Path(__file__).resolve().parent
INPUT_NAMES = (
    'derive_tree.py', 'endpoint_tree.py', 'verify_tree_formal.py',
    'formal_9.json', 'endpoint_9.json',
)
x, k, t, a = S.symbols('x k t a')
EPS = S.symbols('eps')
M = 9
STARTUP = 16
GATES = 0

class VerificationError(RuntimeError):
    """An exact verification condition was not satisfied."""

def require(condition, label):
    global GATES
    GATES += 1
    if condition is not True and condition != S.true:
        raise VerificationError(label)

def equal(left, right, label):
    require(S.cancel(S.expand(left-right)) == 0, label)

def expression(text):
    """Parse the small arithmetic input language without eval/sympify on strings."""
    require(isinstance(text, str) and len(text) <= 20000, 'expression string schema')
    symbols = {'x': x, 'k': k, 't': t, 'a': a}
    def visit(node):
        if isinstance(node, ast.Constant) and type(node.value) is int:
            require(abs(node.value) <= 10**30, 'integer expression bound')
            return S.Integer(node.value)
        if isinstance(node, ast.Name) and node.id in symbols:
            return symbols[node.id]
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.UAdd, ast.USub)):
            value = visit(node.operand)
            return value if isinstance(node.op, ast.UAdd) else -value
        if isinstance(node, ast.BinOp):
            left, right = visit(node.left), visit(node.right)
            if isinstance(node.op, ast.Add): return left + right
            if isinstance(node.op, ast.Sub): return left - right
            if isinstance(node.op, ast.Mult): return left * right
            if isinstance(node.op, ast.Div):
                require(right != 0, 'expression nonzero denominator')
                return left / right
            if isinstance(node.op, ast.Pow):
                require(right.is_Rational is True and abs(right) <= 32, 'bounded rational exponent')
                return left ** right
        raise VerificationError('unsupported expression syntax')
    try:
        return visit(ast.parse(text, mode='eval').body)
    except (SyntaxError, RecursionError) as error:
        raise VerificationError('malformed arithmetic expression') from error

def strict_json(path):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            require(key not in result, 'duplicate JSON key: ' + key)
            result[key] = value
        return result
    def reject_constant(value):
        raise VerificationError('nonfinite JSON constant: ' + value)
    return json.loads(path.read_text(encoding='utf-8'), object_pairs_hook=unique, parse_constant=reject_constant)

def provenance():
    manifest = strict_json(ROOT / 'input_manifest.json')
    require(set(manifest) == {'schema', 'algorithm', 'files'}, 'manifest schema')
    require(type(manifest['schema']) is int and manifest['schema'] == 1 and manifest['algorithm'] == 'sha256', 'manifest version')
    require(set(manifest['files']) == set(INPUT_NAMES), 'exact manifest file set')
    digests = {}
    for name in INPUT_NAMES:
        path = ROOT / 'inputs' / name
        require(path.is_file() and not path.is_symlink(), 'regular local input: ' + name)
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        require(digest == manifest['files'][name], 'input SHA-256 mismatch: ' + name)
        digests[name] = digest
    return digests

def load_coefficients():
    data = strict_json(ROOT / 'inputs' / 'formal_9.json')
    require(set(data) == {'f', 'sigma'}, 'formal JSON schema')
    require(isinstance(data['f'], list) and len(data['f']) == 8, 'profile count')
    require(isinstance(data['sigma'], list) and len(data['sigma']) == M+1, 'sigma count')
    profiles = []
    for pair in data['f']:
        require(isinstance(pair, list) and len(pair) == 2, 'profile pair schema')
        profiles.append(tuple(expression(z) for z in pair))
    sigma = [expression(z) for z in data['sigma']]
    for pair in profiles:
        for z in pair:
            require(z.free_symbols <= {x,k}, 'profile variable set')
            require(S.Poly(z,x,k).domain == S.QQ or S.Poly(z,x,k).domain == S.ZZ,
                    'rational polynomial profile')
    for z in sigma:
        require(z.free_symbols <= {k}, 'sigma variable set')
        require(S.Poly(z,k).domain in (S.QQ,S.ZZ), 'rational polynomial sigma')
    out = strict_json(ROOT / 'inputs' / 'endpoint_9.json')
    require(set(out) == {'ell','E','log_correction','multiplicative','ratio'}, 'endpoint JSON schema')
    for name, size in [('ell',6),('log_correction',6),('multiplicative',7),('ratio',10)]:
        require(isinstance(out[name],list) and len(out[name]) == size, 'endpoint count: ' + name)
        out[name] = [expression(z) for z in out[name]]
    out['E'] = expression(out['E'])
    return profiles, sigma, out

def u(N,h): return F(3*N+h+2, 3*(N+h))
def v(N,h): return F(3*N+h+2, 3*N+h)
def lower(n,j): return F((3*n+j+1)*(3*n+j-1),9*(n+j)*(n+j-1))
def upper(n,j): return F(3*n+j+1,3*n+j-1)
def diagonal(n,j):
    if j == 0: return F(3*n+1,3*n)
    return F((3*n+j+1)*(6*n+2*j-3),3*(n+j)*(3*n+j-2))
def beta2(n,j): return F((3*n+j+1)*(3*n+j-1)*(3*n+j),9*(n+j)*(n+j-1)*(3*n+j-2))
def cdiag2(n,j): return F(3*n+j+1,3*(n+j))
def csub2(n,j): return F((3*n+j+1)*(3*n+j-1),3*(n+j)*(3*n+j-2))
def rising(a,j):
    out = 1
    for z in range(j): out *= a+z
    return out

def symmetrizer2(n,j):
    if j == 0: return F(1)
    return F(rising(3*n-1,j)*rising(3*n,j)*rising(3*n+2,j),
             9**j*rising(n,j)*rising(n+1,j)*rising(3*n+1,j))

def finite_checks():
    """Integers/Fractions only, including the exceptional and moving boundaries."""
    require(type(STARTUP) is int and STARTUP == 16, 'startup coverage configuration')
    last = 2*STARTUP+1
    rows = {1: [0,1]}
    for n in range(2,last+1):
        previous = rows[n-1]
        current = [0]*(n+1)
        for j in range(1,n+1):
            # Direct independent definition, not the adjacent-entry formula.
            current[j] = (2*n+j-2)*sum(previous[1:min(j,n-1)+1])
        rows[n] = current
    def b(n,m):
        if n < 1 or m < 1 or m > n: return 0
        return rows[n][m]
    def B(p,q): return b(p+1,q+1) if 0 <= q <= p else 0
    def d(N,h):
        if N < 0 or h < 0 or h > N or (N-h)%2: return F(0)
        p,q = (N+h)//2,(N-h)//2
        return F(B(p,q),3**p*factorial(p))
    require([1]+[sum(rows[n]) for n in range(1,8)] ==
            [1,1,7,106,2575,87595,3864040,210455470], 'small defining sequence values')
    b_count = rotated_count = matrix_count = 0
    for p in range(last):
        for q in range(p+1):
            if p == q == 0: continue  # Never evaluate the initial 0/0.
            value = (2*p+q+1)*B(p-1,q) + F(2*p+q+1,2*p+q)*B(p,q-1)
            require(value == B(p,q), f'B recurrence p={p},q={q}')
            b_count += 1
    for N in range(1,2*STARTUP+1):
        for h in range(N%2,N+1,2):
            require(d(N,h) == u(N,h)*d(N-1,h-1)+v(N,h)*d(N-1,h+1),
                    f'rotated recurrence N={N},h={h}')
            rotated_count += 1
    e = [F(1)]
    for n in range(1,STARTUP+1):
        new = []
        s2 = [symmetrizer2(n,j) for j in range(n+1)]
        for j in range(n+1):
            actual = sum((lower(n,j) if z==j-1 else diagonal(n,j) if z==j else upper(n,j) if z==j+1 else 0)*e[z] for z in range(n))
            require(actual == d(2*n,2*j), f'two-step trajectory n={n},j={j}')
            new.append(actual)
            require(s2[j] > 0 and cdiag2(n,j)>0, f'positive S/C n={n},j={j}')
            require(diagonal(n,j) == cdiag2(n,j)+(csub2(n,j) if j else 0),
                    f'C factor diagonal n={n},j={j}')
            require(diagonal(n,j) <= (1+F(1,3*n))*(1 if j==0 else 2),
                    f'corrected Jacobi domination diagonal n={n},j={j}')
            if j:
                require(s2[j]/s2[j-1] == lower(n,j)/upper(n,j-1), f'symmetrizer edge n={n},j={j}')
                require(beta2(n,j) == lower(n,j)*upper(n,j-1), f'Jacobi edge n={n},j={j}')
                require(beta2(n,j) == csub2(n,j)*cdiag2(n,j-1), f'C factor edge n={n},j={j}')
                require(beta2(n,j) > 0, f'positive Jacobi edge n={n},j={j}')
                require(beta2(n,j) <= (1+F(1,3*n))**2, f'corrected Jacobi domination edge n={n},j={j}')
            for z in range(n):
                # Enumerate permissible odd-time paths. Forbidden states never enter.
                direct = F(0)
                for mid in range(1,2*n,2):
                    w1 = u(2*n,2*j) if mid==2*j-1 else v(2*n,2*j) if mid==2*j+1 else 0
                    w2 = u(2*n-1,mid) if 2*z==mid-1 else v(2*n-1,mid) if 2*z==mid+1 else 0
                    direct += w1*w2
                claimed = lower(n,j) if z==j-1 else diagonal(n,j) if z==j else upper(n,j) if z==j+1 else 0
                require(direct == claimed, f'exact two-step operator n={n},row={j},col={z}')
                matrix_count += 1
            if j < n:
                r2 = (symmetrizer2(n-1,j) if n>1 else F(1))/s2[j]
                require(0 < r2 <= 1, f'exact R contraction n={n},j={j}')
                if n>1:
                    closed = F(9*(n-1)*(3*n-4)*(3*n-2)*(3*n-1)*(3*n+1)*(n+j-1)*(n+j),
                               n*(3*n+j-4)*(3*n+j-3)**2*(3*n+j-2)*(3*n+j-1)*(3*n+j+1))
                    require(r2 == closed, f'R closed form n={n},j={j}')
        require(F(sum(rows[n])) == F(B(n,n),3*n+1), f'a/B identity n={n}')
        require(F(sum(rows[n])) == F(3**n*factorial(n),3*n+1)*new[0], f'endpoint a/e identity n={n}')
        # The full terminal D acts on the zero-extended new coordinate only.
        terminal_truncated = F((4*n+1)*(4*n-1),6*n*(4*n-2))
        require(diagonal(n,n)-terminal_truncated == cdiag2(n,n), f'full terminal extension n={n}')
        e = new
    require(symmetrizer2(0,0) == 1 and d(0,0) == 1, 'initial conditions')
    require((b_count,rotated_count,matrix_count) == (560,288,1632), 'exact finite coverage counts')
    return {'startup_n_max':STARTUP,'original_b_row_max':last,
            'adjacent_B_entries':b_count,'rotated_entries':rotated_count,
            'two_step_matrix_entries':matrix_count,
            'method':'exact integers and fractions; no floating point or eigenvalue solver',
            'a_0_through_a_7':[1]+[sum(rows[n]) for n in range(1,8)]}

def symbolic_checks():
    n,j = S.symbols('n j',positive=True)
    U = lambda N,H: (3*N+H+2)/(3*(N+H))
    V = lambda N,H: (3*N+H+2)/(3*N+H)
    L = (3*n+j+1)*(3*n+j-1)/(9*(n+j)*(n+j-1))
    Up = (3*n+j+1)/(3*n+j-1)
    Db = (3*n+j+1)*(6*n+2*j-3)/(3*(n+j)*(3*n+j-2))
    B2 = (3*n+j+1)*(3*n+j-1)*(3*n+j)/(9*(n+j)*(n+j-1)*(3*n+j-2))
    equal(U(2*n,2*j)*U(2*n-1,2*j-1),L,'symbolic two-step lower')
    equal(V(2*n,2*j)*V(2*n-1,2*j+1),Up,'symbolic two-step upper')
    equal(U(2*n,2*j)*V(2*n-1,2*j-1)+V(2*n,2*j)*U(2*n-1,2*j+1),Db,'symbolic bulk diagonal')
    equal(V(2*n,0)*U(2*n-1,1),(3*n+1)/(3*n),'symbolic exceptional diagonal')
    c0 = (3*n+j+1)/(3*(n+j))
    c1 = (3*n+j+1)*(3*n+j-1)/(3*(n+j)*(3*n+j-2))
    equal(c0+c1,Db,'symbolic C diagonal')
    equal(c1*c0.subs(j,j-1),B2,'symbolic C off-diagonal square')
    equal(L*Up.subs(j,j-1),B2,'symbolic Jacobi off-diagonal square')
    edge = L/Up.subs(j,j-1)
    F1 = (3*n+j-1)/(3*(n+j-1))
    F2 = (3*n+j-2)*(3*n+j+1)/(3*(n+j)*(3*n+j))
    equal(edge,F1*F2,'factorized symmetrizer edge')
    z,b = 3*n+j,n+j
    equal(S.diff(F1,n),2*(j-1)/(3*(n+j-1)**2),'F1 derivative')
    equal(S.diff(F2,n),(2*j+1+6*b/z**2+2/z)/(3*b**2),'F2 derivative')
    equal(6*(n+j-1)*(n+j)-(2*n+2*j-1)*(3*n+j-2),4*j**2+4*j*n-j+n-2,'R Jensen numerator')
    equal(Db,2-(4*j-3)/(3*(n+j))+1/((n+j)*(3*n+j-2)),'bulk potential identity')
    # Airy-scale coefficient series are finite symbolic identities, not bounds.
    substitutions = {n: EPS**-3,j:x/EPS-S.Rational(1,2)}
    truncate = lambda f: S.series(f,EPS,0,4).removeO().expand()
    equal(truncate(Db.subs(substitutions)),2-S.Rational(4,3)*x*EPS**2+S.Rational(5,3)*EPS**3,'bulk diagonal Airy series')
    equal(truncate(S.sqrt(B2.subs(substitutions))),1-S.Rational(2,3)*x*EPS**2+S.Rational(7,6)*EPS**3,'lower beta Airy series')
    equal(truncate(S.sqrt(B2.subs(j,j+1).subs(substitutions))),1-S.Rational(2,3)*x*EPS**2+S.Rational(1,2)*EPS**3,'upper beta Airy series')
    equal(S.Rational(5,3)+S.Rational(7,6)+S.Rational(1,2),S.Rational(10,3),'eigenvalue cubic coefficient')
    equal(truncate(S.sqrt(B2.subs(j,1).subs(n,EPS**-3))),1+EPS**3/6,'boundary beta Airy series')
    # General polynomial action of T, checking the claimed triangular diagonal.
    c = S.Rational(2,3)
    for degree in range(19):
        monomial = x**degree
        image = S.diff(monomial,x,3)-4*(c*x+k)*S.diff(monomial,x)-2*c*monomial
        poly = S.Poly(image,x)
        require(poly.degree() <= degree,'T degree preserving')
        equal(poly.nth(degree),-2*c*(2*degree+1),'T nonzero triangular diagonal')
        require(poly.nth(degree) != 0,'T invertible finite diagonal')
    return {'identities':'symbolic two-step, C factor, edge monotonicity, R numerator, potential, Airy coefficient series',
            'airy_expansion_through_epsilon_power':3,'triangular_operator_monomial_degrees':[0,18],
            'scope':'finite symbolic certificates; analytic estimates and all-depth induction are not machine proved'}

# Truncated-series ring, independent of the supplied derivation scripts.
def trim(poly,order=M):
    return S.Add(*(coef*t**power[0] for power,coef in S.Poly(S.expand(poly),t).terms() if power[0]<=order))
def mul(left,right,order=M): return S.expand(trim(S.expand(left*right),order))
def power(value,exponent,order=M):
    result = S.Integer(1)
    for _ in range(exponent): result = mul(result,value,order)
    return result

def binomial_series(exponent,order=M,q=1):
    return S.Add(*(S.binomial(exponent,z)*(-q)**z*t**(3*z) for z in range(order//3+1)))
def rational_series(numerator,denominator,order=M):
    num = S.Poly(numerator,t); den = S.Poly(denominator,t)
    require(den.nth(0) != 0,'invertible series denominator')
    coefficients=[]
    for q in range(order+1):
        coefficients.append(S.expand((num.nth(q)-sum(den.nth(z)*coefficients[q-z] for z in range(1,q+1)))/den.nth(0)))
    return sum(c*t**q for q,c in enumerate(coefficients))
def derivative(pair):
    p,q = pair
    return S.expand(S.diff(p,x)+(S.Rational(2,3)*x+k)*q), S.expand(p+S.diff(q,x))
def compose_profile(poly,argument,order=M):
    result = S.Integer(0)
    # Horner composition avoids calling the source Taylor-shift implementation.
    P = S.Poly(poly,x)
    for coefficient in P.all_coeffs(): result = trim(mul(result,argument,order)+coefficient,order)
    return S.expand(result)
def shifted_pair(profiles,sign,order=M):
    """Compose P,Q at shifted x, then Taylor the Airy basis alone."""
    stretch = binomial_series(-S.Rational(1,3),order)
    argument = mul(x+sign*t,stretch,order)
    delta = S.expand(argument-x)
    # Airy(A,A') derivative basis at x, independently composed with profile polynomials.
    airy,airy_prime=(S.Integer(1),S.Integer(0)),(S.Integer(0),S.Integer(1))
    expansions=[[S.Integer(0),S.Integer(0)],[S.Integer(0),S.Integer(0)]]
    delta_power=S.Integer(1)
    for z in range(order+1):
        for comp in range(2):
            expansions[0][comp]+=mul(delta_power,airy[comp],order)/factorial(z)
            expansions[1][comp]+=mul(delta_power,airy_prime[comp],order)/factorial(z)
        airy,airy_prime=derivative(airy),derivative(airy_prime)
        delta_power=mul(delta_power,delta,order)
    result=[S.Integer(0),S.Integer(0)]
    for index,(p,q) in enumerate(profiles):
        limit=order-index
        factor=t**index*binomial_series(-S.Rational(index,3),limit)
        pp,qq=compose_profile(p,argument,limit),compose_profile(q,argument,limit)
        for comp in range(2):
            new=mul(pp,trim(expansions[0][comp],limit),limit)+mul(qq,trim(expansions[1][comp],limit),limit)
            result[comp]+=mul(factor,new,order)
    return tuple(S.expand(trim(z,order)) for z in result)

def formal_checks(profiles,sigma):
    equal(profiles[0][0],1,'leading profile P0')
    equal(profiles[0][1],0,'leading profile Q0')
    for index,(p,q) in enumerate(profiles):
        equal(q.subs(x,0),0,f'boundary profile {index}')
        if index: equal((p+S.diff(q,x)).subs(x,0),0,f'derivative gauge profile {index}')
    require(sigma[:4] == [S.Integer(2),S.Integer(0),k,S.Rational(4,3)],'initial scalar coefficients')
    for index,(p,q) in enumerate(profiles):
        for (rx,rk),coefficient in S.Poly(p,x,k).terms():
            if coefficient: require((index+rx+rk)%3 == 0,f'P grading profile {index}')
        for (rx,rk),coefficient in S.Poly(q,x,k).terms():
            if coefficient: require((index+rx+rk-1)%3 == 0,f'Q grading profile {index}')
    for index,value in enumerate(sigma):
        for (rk,),coefficient in S.Poly(value,k).terms():
            if coefficient: require((index+rk)%3 == 0,f'sigma grading {index}')
    U=rational_series(3+x*t*t+t**3,3+3*x*t*t-3*t**3)
    V=rational_series(3+x*t*t+t**3,3+x*t*t-t**3)
    minus,plus=shifted_pair(profiles,-1),shifted_pair(profiles,1)
    scalar=sum(z*t**q for q,z in enumerate(sigma))
    for comp in range(2):
        lhs=mul(scalar,sum(pair[comp]*t**q for q,pair in enumerate(profiles)))
        rhs=mul(U,minus[comp])+mul(V,plus[comp])
        poly=S.Poly(S.expand(rhs-lhs),t)
        for z in range(M+1): equal(poly.nth(z),0,f'formal pair recurrence component={comp},power={z}')
    return {'profile_indices':[0,7],'scalar_indices':[0,9],
            'checked_recurrence_powers':[0,9],'pair_coefficient_equalities':20,'modulo_three_grading':True,
            'method':'independent truncated composition of profile polynomials and Airy basis; no source module imports'}

def log_series(poly,order=M):
    require(S.expand(poly).coeff(t,0) == 1,'unit constant for logarithmic series')
    quotient=rational_series(S.diff(poly,t),poly,order-1)
    return S.expand(S.integrate(quotient,t))
def exp_series(poly,order=M):
    p=S.Poly(poly,t)
    require(p.nth(0) == 0,'zero constant for exponential series')
    result=[S.Integer(1)]
    for index in range(1,order+1):
        result.append(S.expand(sum(z*p.nth(z)*result[index-z] for z in range(1,index+1))/index))
    return sum(z*t**index for index,z in enumerate(result))
def exact_simple(left,right,label): require(S.simplify(S.expand(left-right)) == 0,label)

def endpoint_checks(profiles,sigma,data):
    J=6
    endpoint=S.Integer(0)
    for index,pair0 in enumerate(profiles):
        pair=pair0
        for degree in range(J+2-index):
            endpoint+=pair[1].subs(x,0)*t**(index+degree-1)/factorial(degree)
            pair=derivative(pair)
    endpoint=S.expand(trim(endpoint,J))
    equal(endpoint,data['E'],'canonical endpoint Taylor series')
    scalar=sum(z*t**q for q,z in enumerate(sigma))
    log_scalar=log_series(scalar/2)
    carrier=3*k/(2*t)*(1-binomial_series(S.Rational(1,3),M+1))-S.Rational(2,3)*log_series(1-t**3)
    for index,ell in enumerate(data['ell'],1):
        carrier+=ell*t**index*(1-binomial_series(-S.Rational(index,3),M-index))
    carrier=S.expand(trim(carrier))
    for z in range(M+1): equal(carrier.coeff(t,z),log_scalar.coeff(t,z),f'scalar carrier difference power={z}')
    # Check all endpoint normalization, logarithm, and exponential conversion data.
    log_normalized=log_series(endpoint,J)-log_series(1+S.Rational(2,3)*t**3,J)
    for index,ell in enumerate(data['ell'],1): log_normalized+=ell*t**index
    k_to_alpha=S.Rational(2,3)**S.Rational(2,3)*a
    for index,want in enumerate(data['log_correction'],1):
        actual=log_normalized.coeff(t,index).subs(k,k_to_alpha)*2**(-S.Rational(index,3))
        exact_simple(actual,want,f'endpoint logarithmic correction {index}')
    exponent=sum(z*t**index for index,z in enumerate(data['log_correction'],1))
    multiplicative=exp_series(exponent,J)
    for index,want in enumerate(data['multiplicative']):
        exact_simple(multiplicative.coeff(t,index),want,f'multiplicative correction {index}')
    # First ratio route: direct two-step scalar and endpoint conversion.
    scalar_previous=trim(sum(z*t**index*binomial_series(-S.Rational(index,3),M-index) for index,z in enumerate(sigma)))
    endpoint_previous=trim(sum(endpoint.coeff(t,index)*t**index*binomial_series(-S.Rational(index,3),M-index,q=2) for index in range(J+1)))
    raw_ratio=mul(scalar/2,scalar_previous/2)
    for factor in [binomial_series(S.Rational(1,3),q=2),endpoint,
                   rational_series(1,endpoint_previous),rational_series(3-4*t**3,3+2*t**3)]:
        raw_ratio=mul(raw_ratio,factor)
    for index,want in enumerate(data['ratio']):
        actual=raw_ratio.coeff(t,index).subs(k,k_to_alpha)*2**(-S.Rational(index,3))
        exact_simple(actual,want,f'direct endpoint ratio coefficient {index}')
    # Second ratio route: the canonical asymptotic logarithm at n and n-1.
    log_ratio=3**S.Rational(1,3)*a/t*(1-binomial_series(S.Rational(1,3),M+1))+S.Rational(2,3)*log_series(1-t**3)
    for index,ell in enumerate(data['log_correction'],1):
        log_ratio+=ell*t**index*(1-binomial_series(-S.Rational(index,3),M-index))
    ratio=exp_series(trim(log_ratio))
    for index,want in enumerate(data['ratio']):
        exact_simple(ratio.coeff(t,index),want,f'logarithmic endpoint ratio coefficient {index}')
    return {'canonical_endpoint_through_t_power':6,'carrier_difference_through_t_power':9,
            'log_and_multiplicative_corrections_through_n_power':'n^(-2)',
            'ratio_through_n_power':'n^(-3)','independent_ratio_routes':2,
            'exact_normalization_factor':'(3n-2)/(3n+1)',
            'scope':'finite formal algebra only; no amplitude numerical enclosure'}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--section',choices=['all','finite','symbolic','formal','endpoint'],default='all')
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    start=time.monotonic()
    result={'schema':1,'status':'FAIL','python':platform.python_version(),'sympy':S.__version__,
            'optimization':sys.flags.optimize,'section':args.section,
            'started_utc':datetime.now(timezone.utc).isoformat(),
            'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    try:
        result['input_sha256']=provenance()
        profiles,sigma,endpoint=load_coefficients()
        sections={}
        for name,operation in [('finite',finite_checks),('symbolic',symbolic_checks),
                               ('formal',lambda:formal_checks(profiles,sigma)),
                               ('endpoint',lambda:endpoint_checks(profiles,sigma,endpoint))]:
            if args.section in ('all',name):
                sections[name]=operation()
                print('PASS '+name,flush=True)
        result['checks']=sections
        result['status']='PASS'
    except Exception as error:
        result['error_type']=type(error).__name__
        result['error']=str(error)
        print('FAIL '+type(error).__name__+': '+str(error),file=sys.stderr,flush=True)
    result['explicit_gates']=GATES
    result['elapsed_seconds']=round(time.monotonic()-start,6)
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({key:result[key] for key in ['status','section','optimization','explicit_gates','elapsed_seconds']}),flush=True)
    return 0 if result['status']=='PASS' else 1

if __name__=='__main__':
    sys.exit(main())
