"""Finite exact regression checks. These are not proofs of the paper's theorems."""
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import json
import platform
import random
import time
import sympy as sp
from omega_notation import (
    number, om, equivalent, compare, sign, leading, is_zero,
    separated_basis, coordinates, grid_form, evaluate_rational,
    rational_truncation, nonnegative_part, is_omnific,
    omnific_floor, truncate_at, coefficient_at,
)

results = []

def check(name, condition):
    if not condition:
        raise AssertionError(name)
    results.append(name)


def eq(name, a, b): check(name, equivalent(a, b))


def main():
    start = time.monotonic()
    w = om(1)
    W = om(w)
    Z = om(w*w)
    for i, (a, b) in enumerate([(number(2), number(-3)), (w, number(1)),
                                (w+1, 1/(w-1)), (1/w, w-2)]):
        eq('omega homomorphism %d' % i, om(a+b), om(a)*om(b))
        eq('omega inverse %d' % i, om(-a), 1/om(a))
        eq('omega rational multiple %d' % i, om(a/3)**3, om(a))
    eq('constant omega', om(0), 1)
    check('omega of positive infinitesimal is infinite', compare(om(1/w), 10**6) > 0)
    check('positive infinitesimal omega exponent order', compare(om(1/w), w) < 0)

    A = W/(1-1/w)
    eq('geometric identity', A*(1-1/w), W)
    eq('first tail identity', A-W, A/w)
    eq('two tails', A-W-W/w, A/(w*w))
    check('infinite support omnific', is_omnific(A))
    check('infinite support with negative infinitesimal not omnific', not is_omnific(A-1/w))
    check('nonintegral constant not omnific', not is_omnific(A+Q(1,2)))
    check('integral constant allowed', is_omnific(A-7))
    eq('floor below integral boundary', omnific_floor(A-1/w), A-1)
    eq('floor above integral boundary', omnific_floor(A+1/w), A)
    eq('negative half floor', omnific_floor(-A-Q(1,2)), -A-1)
    eq('noninteger rational minus tiny tail', omnific_floor(A+Q(2,3)-1/w), A)
    for n in range(8):
        check('coefficient geometric %d' % n, coefficient_at(A, w-n) == 1)
        cutoff = w-n
        expected = sum((W/(w**j) for j in range(n+1)), number(0))
        eq('truncation geometric %d' % n, truncate_at(A, cutoff), expected)
    check('absent coefficient', coefficient_at(A, w+1) == 0)
    eq('cut between lattice points', truncate_at(A, w-Q(3,2)), W+W/w)

    # Leading-term elimination with tails, dependence, and rational coordinates.
    g1, g2, g3 = w+1/(w-1), 1+1/w, 1/(w-1)
    exps = [g1, w, g2, g3, 2*g1-Q(2,3)*g2+Q(3,5)*g3]
    basis = separated_basis(exps)
    check('tail-sensitive basis dimension', len(basis) == 3)
    for i, e in enumerate(exps):
        cs = coordinates(e, basis)
        eq('basis reconstruction %d' % i,
           sum((c*b for c,b in zip(cs,basis)),number(0)), e)
    for i in range(2):
        check('basis is separated %d' % i,
              compare(leading(basis[i])[0],leading(basis[i+1])[0]) > 0)
    F = om(g1)/(1-om(-g2)) + om(g3)
    check('tail-sensitive grid omnific', is_omnific(F))
    rf, variables, gamma = grid_form(F)
    eq('grid round trip with nonmonomial exponent basis',
       evaluate_rational(rf,variables,gamma),F)

    # Explicit independent lexicographic polynomial-division expectations.
    X, Y, T = sp.symbols('X Y T')
    examples = [
        (X/(1-1/Y)+1/(Y-1), (X,Y), X/(1-1/Y), 0),
        ((X**2+Y)/(X-1), (X,Y), X+1, 1),
        (Y/(X-Y), (X,Y), 0, 0),
        (X*Y/(Y-1)+Y**2/(Y-1), (X,Y), X*Y/(Y-1)+Y+1, 1),
        (X/(1-1/Y)/(1-1/T)-sp.Rational(7,3)+1/T,
         (X,Y,T), X/(1-1/Y)/(1-1/T)-sp.Rational(7,3), -sp.Rational(7,3)),
        (X/(1-1/Y)-Y/(1-1/T), (X,Y,T), X/(1-1/Y)-Y/(1-1/T),0),
        (X-X+1/(Y-1), (X,Y),0,0),
    ]
    for i,(f,vs,expected,c) in enumerate(examples):
        tr, ct = rational_truncation(f,vs)
        check('rational truncation fixture %d' % i, sp.cancel(tr-expected)==0)
        check('rational coefficient fixture %d' % i, ct==c)
        gs = (w,number(1)) if len(vs)==2 else (w*w,w,number(1))
        v = evaluate_rational(f,vs,gs)
        t, cv = nonnegative_part(v)
        eq('full algorithm fixture %d' % i,t,evaluate_rational(expected,vs,gs))
        check('full coefficient fixture %d' % i,sp.Rational(cv.numerator,cv.denominator)==c)

    rng=random.Random(23092026)
    # Ordinary arithmetic identities and integer-part inequalities, rank one.
    for i in range(24):
        a,b,c,d=[rng.randint(-5,5) for _ in range(4)]
        f=(a*w*w+b*w+c)/(w+d)
        q=omnific_floor(f)
        check('random floor membership %d' % i,is_omnific(q))
        check('random floor lower %d' % i,compare(f,q)>=0)
        check('random floor upper %d' % i,compare(f,q+1)<0)
        eq('random division identity %d' % i,f*(w+d),a*w*w+b*w+c)

    # Rational-series finite rectangle certificate: cancellation is checked
    # exactly, rather than estimated from a numerical series sample.
    u,v=sp.symbols('u v')
    P=1+u+2*v; Qp=1-u-v
    S=(1+u+2*v)*(1+u*v); Tp=(1-u-v)*(1+u*v)
    check('rectangle numerator identity',sp.expand(P*Tp-S*Qp)==0)
    for i,j in product(range(4),repeat=2):
        check('lex grid injectivity %d %d' %(i,j),
              coefficient_at(Z/(1-1/W)/(1-1/w), w*w-i*w-j)==1)

    try:
        _=number(1)/(w-w)
        check('division by zero rejected',False)
    except ZeroDivisionError:
        check('division by zero rejected',True)
    try:
        number(0.1)
        check('floats rejected',False)
    except TypeError:
        check('floats rejected',True)

    out={
        'status':'PASS','assertions':len(results),
        'python':platform.python_version(),'sympy':sp.__version__,
        'elapsed_seconds':round(time.monotonic()-start,3),
        'seed':23092026,
        'scope':'Finite exact regression assertions; no Lean verification and no halting oracle.',
        'checks':results,
    }
    path=Path(__file__).resolve().parents[1]/'data'/'verification.json'
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:v for k,v in out.items() if k!='checks'},indent=2))

if __name__=='__main__': main()
