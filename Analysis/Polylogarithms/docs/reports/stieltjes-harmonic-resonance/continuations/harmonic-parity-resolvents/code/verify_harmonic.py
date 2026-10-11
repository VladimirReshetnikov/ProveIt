#!/usr/bin/env python3
"""Exact algebra checks and independent high-precision diagnostics.

The analytic proof is in harmonic_module.tex. Floating-point residuals
are diagnostics, not interval certificates. Continuation uses direct
finite Hurwitz tails plus Euler--Maclaurin terms independently of the
nonpositive-index elimination under test.

The depth-three Euler--Maclaurin evaluator adapts the independent-order
package's code/verify_harmonic_transport.py at the pinned repository
snapshot recorded in harmonic_provenance.json. Its evaluation method is
independent of the new finite deletion and gap-polynomial algorithms.
"""
from __future__ import annotations
import argparse
import itertools
import json
import random
from pathlib import Path
import mpmath as mp
import sympy as sp

from reduce_harmonic import (A, B, clean, complete_harmonic,
    eliminate_one, finite_harmonic, is_nonpositive, reduce_by_gaps,
    reduce_word)


def exact_checks():
    rng = random.Random(10112026)
    s, t, v = sp.symbols('s t v')
    cases = [(0,s,0),(-1,s,-1),(s,0,t),(0,s,-1,t,0),
             (-1,0,s,0,-2),(s,0,0,t),(0,0,0),
             (-2,-1,0),(0,s,0,t,0,v,0),(-1,s,-2,t)]
    for _ in range(16):
        length = rng.randint(2,6)
        free_count = rng.randint(1,min(3,length-1))
        free_positions = set(rng.sample(range(length),free_count))
        letters = iter((s,t,v))
        cases.append(tuple(next(letters) if j in free_positions
                           else -rng.randint(0,2) for j in range(length)))
    cases = [tuple(map(sp.sympify,w)) for w in cases]
    finite_count = strategy_count = degree_count = 0
    b = sp.Rational(2,3)
    substitutions = {s:2,t:4,v:3}
    examples = []
    for word in cases:
        expected = reduce_word(word,'left')
        for strategy in ('right','middle'):
            got = reduce_word(word,strategy)
            assert clean({w:expected.get(w,0)-got.get(w,0)
                          for w in set(expected)|set(got)}) == {}
            strategy_count += 1
        got = reduce_by_gaps(word)
        assert clean({w:expected.get(w,0)-got.get(w,0)
                      for w in set(expected)|set(got)}) == {}
        strategy_count += 1
        free = tuple(x for x in word if not is_nonpositive(x))
        budget = sum(int(1-x) for x in word if is_nonpositive(x))
        for target, coefficient in expected.items():
            shift = sum(int(x-y) for x,y in zip(free,target))
            assert all(x-y >= 0 for x,y in zip(free,target))
            assert sp.Poly(coefficient,A,B).total_degree() <= budget-shift
            degree_count += 1
        numeric_word = tuple(x.subs(substitutions) for x in word)
        for n in (4,7):
            direct = finite_harmonic(numeric_word,b,n)
            reduced = sum(coefficient.subs({A:b+n,B:b})
                          *finite_harmonic(tuple(x.subs(substitutions)
                                                  for x in target),b,n)
                          for target,coefficient in expected.items())
            assert sp.cancel(direct-reduced) == 0
            finite_count += 1
        if len(examples)<10:
            examples.append({'word':[str(x) for x in word],
              'terms':[{'word':[str(x) for x in target],
                        'coefficient':str(sp.factor(coefficient))}
                       for target,coefficient in expected.items()]})
    # Exact check of the all-zero insertion identity.
    for r in range(7):
        summed = {}
        for p in range(r+1):
            for target,c in reduce_word((sp.Integer(0),)*p+(s,)
                           +(sp.Integer(0),)*(r-p)).items():
                summed[target] = summed.get(target,0)+c
        target = {(s,):sp.prod(A-B-1-j for j in range(r))/sp.factorial(r)}
        assert clean({w:summed.get(w,0)-target.get(w,0)
                      for w in set(summed)|set(target)}) == {}
    # A corrupted B_1(1) would lose the strict-gap subtraction.
    corrupted = {(s-1,t):1,(s,t-1):-1}
    correct = eliminate_one((s,sp.Integer(0),t),1)
    assert clean({w:correct.get(w,0)-corrupted.get(w,0)
                  for w in set(correct)|set(corrupted)}) == {(s,t):-1}
    # Compare complete-harmonic coefficients to independent series expansion.
    z = sp.Symbol('z')
    for j in range(6):
        poly = sp.series(sp.prod(1/(1-z/ell) for ell in range(1,j+1)),
                         z,0,6).removeO().expand()
        for n in range(6):
            assert complete_harmonic(j,n) == poly.coeff(z,n)
    return {'word_cases':len(cases),'strategy_and_gap_checks':strategy_count,
      'finite_nested_sum_checks':finite_count,'degree_bound_checks':degree_count,
      'zero_insertion_checks':7,'complete_harmonic_checks':36,
      'strict_gap_corruption_control':'passed','examples':examples}


def em_terms(s,order):
    result = {-1:mp.mpf(1)/(s-1),0:-mp.mpf('0.5')}
    for k in range(1,order+1):
        result[2*k-1] = mp.bernoulli(2*k)*mp.rf(s,2*k-1)/mp.factorial(2*k)
    return result


class Continuation:
    """EM continuation through depth three; no deletion rules are used."""
    def __init__(self,cutoff=28,order=14):
        self.cutoff,self.order = cutoff,order
        self.cache = {}

    def z(self,word,a):
        word = tuple(word)
        key = word,a
        if key in self.cache:
            return self.cache[key]
        if not word:
            answer = mp.mpf(1)
        elif len(word)==1:
            answer = mp.zeta(word[0],a)
        elif len(word)==2:
            s,t = word
            answer = mp.fsum(mp.zeta(s,a+n+1)/(a+n)**t
                            for n in range(self.cutoff))
            answer += mp.fsum(c*mp.zeta(s+t+j,a+self.cutoff)
                              for j,c in em_terms(s,self.order).items())
        elif len(word)==3:
            s,t,v = word
            answer = mp.mpf(0)
            prefix = mp.mpf(0)
            for n in range(self.cutoff):
                x = a+n
                answer += mp.zeta(s,x+1)*prefix/x**t
                prefix += x**(-v)
            outer = em_terms(s,self.order)
            inner = em_terms(v,self.order)
            inner[0] = mp.mpf('0.5')
            convolution = {}
            for j,c in outer.items():
                for k,d in inner.items():
                    convolution[j+k] = convolution.get(j+k,0)+c*d
            answer += mp.zeta(v,a)*mp.fsum(
                c*mp.zeta(s+t+j,a+self.cutoff) for j,c in outer.items())
            answer -= mp.fsum(c*mp.zeta(s+t+v+j,a+self.cutoff)
                              for j,c in convolution.items())
        else:
            raise ValueError('Only depths through three are implemented')
        self.cache[key] = answer
        return answer

    def h(self,word,a,b):
        word = tuple(word)
        if not word:
            return mp.mpf(1)
        return self.z(word,b)-mp.fsum(self.z(word[:j],a)
              *self.h(word[j:],a,b) for j in range(1,len(word)+1))


def sp_to_mp(expr,values):
    return sp.lambdify(tuple(values),expr,modules='mpmath')(*values.values())


def primitive(d,s,a,b):
    delta = a-b
    result = delta**(d+1)*mp.zeta(s,b)/(d+1)
    for j in range(d+1):
        numerator = delta**(d-j)*mp.zeta(s-j-1,a)
        if j==d:
            numerator -= mp.zeta(s-j-1,b)
        result += (mp.factorial(d)/mp.factorial(d-j)*numerator
                   /mp.fprod(s-ell for ell in range(1,j+2)))
    return result


def zeta_derivative(r,s,a):
    return mp.diff(lambda z:mp.zeta(z,a),s,r)


def stieltjes_moment(d,m,a,b):
    delta = a-b
    result = mp.mpf(0)
    for j in range(d+1):
        for r in range(m+2):
            exact = complete_harmonic(j,m+1-r)
            coefficient = mp.mpf(int(sp.numer(exact)))/int(sp.denom(exact))
            numerator = delta**(d-j)*zeta_derivative(r,-j,a)
            if j==d:
                numerator -= zeta_derivative(r,-j,b)
            result += (-1)**j*mp.binomial(d,j)*coefficient*numerator/mp.factorial(r)
    return (-1)**(m+1)*mp.factorial(m)*result


def polynomial_product(left,right):
    out = [mp.mpf(0)]*(len(left)+len(right)-1)
    for i,x in enumerate(left):
        for j,y in enumerate(right):
            out[i+j] += x*y
    return out


def zero_gap_coefficient(p,q,a,b,hvalues):
    upper,lower = [mp.mpf(1)],[mp.mpf(1)]
    for j in range(p):
        upper = polynomial_product(upper,[(a-1-j)/(j+1),-mp.mpf(1)/(j+1)])
    for j in range(q):
        lower = polynomial_product(lower,[(-b-j)/(j+1),mp.mpf(1)/(j+1)])
    return mp.fsum(c*hvalues[k]
                  for k,c in enumerate(polynomial_product(upper,lower)))


def numeric_checks(dps=60):
    mp.mp.dps = dps
    rows = []
    def record(name,residual,**metadata):
        rows.append({'name':name,'absolute_residual':mp.nstr(abs(residual),15),
                     **metadata})
        print(name,mp.nstr(abs(residual),5),flush=True)
    a,b = mp.mpf('2.3'),mp.mpf('.8')
    s,t = sp.symbols('s t')
    values = {A:a,B:b,s:mp.mpc('.71','.13'),t:mp.mpc('1.28','-.21')}
    cont = Continuation()
    cases = [(-2,s,t),(s,-1,t),(s,t,-2),(-1,s,-1),
             (0,s,0),(s,0,t)]
    for word in cases:
        word = tuple(map(sp.sympify,word))
        numerical = tuple(sp_to_mp(x,values) for x in word)
        direct = cont.h(numerical,a,b)
        reduced = mp.mpf(0)
        for target,coefficient in reduce_word(word).items():
            reduced += sp_to_mp(coefficient,values)*cont.h(
                tuple(sp_to_mp(x,values) for x in target),a,b)
        record('independent_EM_nonpositive_elimination',direct-reduced,
               word=[str(x) for x in word],cutoff=28,EM_order=14)
    # A free order derivative, independently differenced before deletion.
    word = (s,sp.Integer(-1),t)
    def direct_s(z):
        return Continuation().h((z,mp.mpf(-1),values[t]),a,b)
    def reduced_s(z):
        vals = dict(values); vals[s] = z
        engine = Continuation()
        return mp.fsum(sp_to_mp(coefficient,vals)*engine.h(
             tuple(sp_to_mp(x,vals) for x in target),a,b)
             for target,coefficient in reduce_word(word).items())
    record('independent_EM_free_order_derivative',
           mp.diff(direct_s,values[s])-mp.diff(reduced_s,values[s]))
    # Entire Lerch difference evaluated via a separate special-function call.
    ss = mp.mpc('.71','.21')
    u,v = mp.mpc('.03','.005'),mp.mpc('-.02','.001')
    tt = mp.log(1+v)-mp.log(1+u)
    lerch = mp.exp(b*tt)*mp.lerchphi(mp.exp(tt),ss,b)
    lerch -= mp.exp(a*tt)*mp.lerchphi(mp.exp(tt),ss,a)
    target = (1+u)**(a-1)*(1+v)**(-b)*lerch
    maxdegree = 18
    hvalues = [mp.zeta(ss-k,b)-mp.zeta(ss-k,a) for k in range(maxdegree+1)]
    for degree in (10,14,18):
        truncated = mp.fsum(zero_gap_coefficient(p,q,a,b,hvalues)*u**p*v**q
              for p in range(degree+1) for q in range(degree+1-p))
        record('zero_block_Lerch_generator',truncated-target,total_degree=degree)
    # Independent normalized Mellin integration in its honest convergence region.
    ss = mp.mpc('1.7','.2')
    tt = mp.mpc('-.23','.17')
    def kernel(y):
        if abs(y)<mp.mpf('1e-50'):
            return a-b
        return (mp.exp(-b*y)-mp.exp(-a*y))/(-mp.expm1(-y))
    integral = mp.quad(lambda x:x**(ss-1)*kernel(x-tt),[0,1,mp.inf])/mp.gamma(ss)
    lerch = mp.exp(b*tt)*mp.lerchphi(mp.exp(tt),ss,b)
    lerch -= mp.exp(a*tt)*mp.lerchphi(mp.exp(tt),ss,a)
    record('Lerch_Mellin_integral',integral-lerch)
    for d,ss in [(0,mp.mpc('.4','.2')),(1,mp.mpc('2.2','-.1')),
                 (3,mp.mpc('.8','.3'))]:
        direct = mp.quad(lambda x:(x-b)**d*(mp.zeta(ss,b)-mp.zeta(ss,x)),[b,a])
        record('normalized_polynomial_primitive',direct-primitive(d,ss,a,b),d=d)
    # Stieltjes quadrature is independent of derivatives at negative integers.
    for d,m in [(0,0),(1,0),(1,1),(2,1),(2,2)]:
        direct = mp.quad(lambda x:(x-b)**d*mp.stieltjes(m,x),[b,a])
        record('Stieltjes_polynomial_moment',direct-stieltjes_moment(d,m,a,b),d=d,m=m)
    return {'dps':dps,'checks':rows,
      'status':'floating-point diagnostics, not interval error bounds'}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--exact-only',action='store_true')
    parser.add_argument('--dps',type=int,default=60)
    parser.add_argument('--out',type=Path,default=Path(__file__).resolve().parents[1]/'results/latest/harmonic_verification.json')
    args = parser.parse_args()
    result = {'exact':exact_checks()}
    print('Exact checks passed',flush=True)
    if not args.exact_only:
        result['numeric'] = numeric_checks(args.dps)
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print('Wrote',args.out,flush=True)


if __name__=='__main__':
    main()
