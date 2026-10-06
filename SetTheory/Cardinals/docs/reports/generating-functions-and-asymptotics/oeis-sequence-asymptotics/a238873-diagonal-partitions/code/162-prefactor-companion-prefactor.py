#!/usr/bin/env python3
"""Bounded exact diagnostics for Report162. No file writes or network I/O."""
import argparse
from fractions import Fraction as F
import itertools
import json
import math
import re
import sys

MAX_N = 400
MAX_SERIES = 100
MAX_ENUMERATION = 32
MAX_TARGET = 10 ** 200
AIRY_ZERO = '-2.338107410459767038489197252446735440638540145672387852'
AIRY_DERIVATIVE = '0.701210822720691362490691656031538702253471535993385538'


def bounded_integer(value, name, lower, upper):
    if type(value) is not int:
        raise TypeError(name + ' must be an integer, not a boolean or coerced value')
    if not lower <= value <= upper:
        raise ValueError(name + ' must be between ' + str(lower) + ' and ' + str(upper))
    return value


def canonical_integer(text, upper):
    if type(text) is not str or len(text) > 201 or re.fullmatch(r'0|[1-9][0-9]*', text, re.ASCII) is None:
        raise argparse.ArgumentTypeError('Use canonical nonnegative ASCII decimal notation')
    value = int(text)
    if value > upper:
        raise argparse.ArgumentTypeError('Value exceeds ' + str(upper))
    return value


def counts(max_n=MAX_N):
    """Positive in-place multiplicity DP; output includes the empty partition."""
    bounded_integer(max_n, 'max_n', 0, MAX_N)
    length = (math.isqrt(8 * max_n + 1) - 1) // 2
    dp = [[0] * (max_n + 1) for _ in range(length + 1)]
    dp[0][0] = 1
    for v in range(1, max_n + 1):
        for w in range(v, max_n + 1):
            for k in range(1, min(v, length) + 1):
                dp[k][w] += dp[k - 1][w - v]
    return [sum(row[n] for row in dp) for n in range(max_n + 1)]


def _convolve(left, right, n):
    out = [0] * (n + 1)
    for i, a in enumerate(left):
        if a:
            for j in range(n + 1 - i):
                if right[j]:
                    out[i + j] += a * right[j]
    return out


def q_series(max_n=80):
    """Independent reciprocal H_q formal-series calculation, exact integers."""
    bounded_integer(max_n, 'max_n', 0, MAX_SERIES)
    length = (math.isqrt(8 * max_n + 1) - 1) // 2
    hs = []
    for j in range(length + 1):
        denominator = [0] * (max_n + 1)
        denominator[0] = 1
        for r in range(1, j + 1):
            for n in range(r, max_n + 1):
                denominator[n] += denominator[n-r]
        shift = j*j
        hs.append(([0]*shift + [(-1)**j * a for a in denominator[:max_n+1-shift]])
                  if shift <= max_n else [0]*(max_n+1))
    cs = [[1] + [0] * max_n]
    for k in range(1, length + 1):
        ck = [0] * (max_n + 1)
        for j in range(1, k + 1):
            product = _convolve(hs[j], cs[k-j], max_n)
            ck = [a-b for a,b in zip(ck, product)]
        cs.append(ck)
    out = [0] * (max_n + 1)
    for k, ck in enumerate(cs):
        shift = k*(k-1)//2
        for n in range(max_n + 1 - shift):
            out[n+shift] += ck[n]
    return out


def _partitions(weight, minimum=1):
    if weight == 0:
        yield ()
    for first in range(minimum, weight + 1):
        for tail in _partitions(weight-first, first):
            yield (first,) + tail


def enumerate_checks(max_n=28):
    bounded_integer(max_n, 'max_n', 0, MAX_ENUMERATION)
    expected = counts(max_n)
    ordinary = admissible = injection_images = 0
    found = []
    for n in range(max_n + 1):
        good = []
        for part in _partitions(n):
            ordinary += 1
            indexed = all(value >= i for i,value in enumerate(part, 1))
            cumulative = all(sum(v <= j for v in part) <= j for j in range(n+1))
            if indexed != cumulative:
                raise RuntimeError('Indexed and cumulative constraints disagree')
            if indexed:
                admissible += 1
                good.append(part)
        images = set()
        for part in good:
            image = part[:-1] + (part[-1]+1,) if part else (1,)
            if not all(value >= i for i,value in enumerate(image, 1)) or sum(image) != n+1:
                raise RuntimeError('Invalid injection image')
            recovered = image[:-1] + (image[-1]-1,) if n else ()
            if recovered != part or image in images:
                raise RuntimeError('Injection is not reversible')
            images.add(image)
            injection_images += 1
        found.append(len(good))
    if found != expected:
        raise RuntimeError('Independent enumeration does not match counts')
    return {'through': max_n, 'ordinary_partitions': ordinary,
            'admissible_partitions': admissible, 'injection_images': injection_images,
            'indexed_cumulative_match': True, 'count_match': True}


def _poly_add(left, right):
    out = dict(left)
    for key, value in right.items():
        out[key] = out.get(key, F(0)) + value
    return {k:v for k,v in out.items() if v}


def _poly_scale(poly, coefficient, degree=0):
    return {(j+degree, kind): coefficient*v for (j,kind),v in poly.items() if coefficient*v}


def _airy_derivative(poly):
    out = {}
    for (j, kind),value in poly.items():
        if j:
            out = _poly_add(out, {(j-1,kind): j*value})
        # kind=0 is Ai and kind=1 is Ai'; Ai''=s Ai.
        key = (j,1) if kind == 0 else (j+1,0)
        out = _poly_add(out, {key:value})
    return out


def airy_algebra():
    """Fixed rational identity check, with no unbounded symbolic input."""
    derivatives = [{(0,0):F(1)}]
    for _ in range(5):
        derivatives.append(_airy_derivative(derivatives[-1]))
    q1 = [(2,1,F(1,2)), (0,2,F(-1,2))]
    q2 = [(5,0,F(-1,30)), (4,2,F(1,8)), (2,3,F(-1,4)),
          (1,2,F(1,4)), (0,4,F(1,8))]
    def integrate(terms):
        out = {}
        for u_degree,s_degree,coefficient in terms:
            out = _poly_add(out, _poly_scale(derivatives[u_degree],
                                            coefficient*(-1)**u_degree,s_degree))
        return out
    first = integrate(q1)
    second = integrate(q2)
    desired = {(1,0):F(2,15), (2,1):F(1,30)}
    if first or second != desired:
        raise RuntimeError('Airy polynomial identity failed')
    return {'Q1_integral_zero':True, 'Q2_integral':'(4*s*Ai(s)+s^2*AiPrime(s))/30',
            'arithmetic':'exact Fraction polynomial reduction with AiDoublePrime=s*Ai'}


def tilt_checks():
    """Fixed finite exact change-of-measure checks, including nonadmissible vectors."""
    checked = admissible = 0
    for m in range(7):
        for z in itertools.product(range(4), repeat=m):
            heights = [0]
            for j,value in enumerate(z,1):
                heights.append(heights[-1]+1-value)
            area, final = sum(heights[:-1]), heights[-1]
            weighted = sum(j*value for j,value in enumerate(z,1))
            if weighted != m*(m+1)//2-m*final+area:
                raise RuntimeError('Summation by parts failed')
            for q in (F(2,3),F(3,4)):
                lhs = F(2)**(m+sum(z))*q**weighted
                rhs = F(4)**m*q**(m*(m+1)//2)*q**area*(F(2)**(-final))*q**(-m*final)
                if lhs != rhs:
                    raise RuntimeError('Exact tilt failed')
                checked += 1
            admissible += all(h >= 0 for h in heights)
    return {'vector_lengths_through':6, 'entries_through':3, 'rational_tilt_comparisons':checked,
            'admissible_vectors':admissible, 'summation_by_parts':True, 'exact_tilt':True}


def verify():
    primary = counts(MAX_N)
    independent = q_series(80)
    if primary[:81] != independent:
        raise RuntimeError('Reciprocal H series does not match positive counts')
    if primary[:16] != [1,1,1,2,3,3,5,7,9,11,14,19,25,31,38,46]:
        raise RuntimeError('Convention check failed')
    if any(a>b for a,b in zip(primary,primary[1:])):
        raise RuntimeError('Nonmonotone counts')
    return {'scope':'Finite exact diagnostics, not an asymptotic proof or finite error certificate',
            'counts_through':MAX_N, 'empty_coefficient':primary[0],
            'reciprocal_H_match_through':80, 'enumeration':enumerate_checks(),
            'airy_algebra':airy_algebra(), 'tilt':tilt_checks(),
            'last_count_digits':len(str(primary[-1])), 'monotone_counts':True,
            'inverse_cross_coefficient':str(-F(1,8)*4-F(1,6)*2),
            'inverse_cross_coefficient_interpretation':'multiplies D^2/B * x^(-1/6)'}


def threshold(value, max_n=MAX_N):
    bounded_integer(value, 'value', 1, MAX_TARGET)
    bounded_integer(max_n, 'max_n', 0, MAX_N)
    values = counts(max_n)
    hit = next((i for i,a in enumerate(values) if a >= value), None)
    return {'value':str(value), 'max_n':max_n, 'status':'reached' if hit is not None else 'unreached',
            'threshold':hit, 'count_at_threshold':str(values[hit]) if hit is not None else None,
            'previous_count':str(values[hit-1]) if hit is not None and hit else None}


def illustrations():
    a, ap = float(AIRY_ZERO),float(AIRY_DERIVATIVE)
    b=math.log(2); C=math.pi**2/12+b*b; B=2*math.sqrt(C); D=-a*b*C**(-1/6)
    KF=2*math.sqrt(2)/ap; K=math.sqrt(2)*C**(5/12)/(math.sqrt(math.pi)*ap)
    alpha=a*a*(1/4-b/30)
    raw={'C':C,'B':B,'D':D,'K_F':KF,'K':K,'alpha':alpha,
         'inverse_x_two_thirds':2*D/B,'inverse_sqrt_x_log_x':11/(6*B),
         'inverse_sqrt_x':-2*math.log(K)/B}
    values=counts(MAX_N)
    residuals=[]
    for n in (25,50,100,200,400):
        remainder=math.log(values[n])-B*math.sqrt(n)+D*n**(1/6)+(11/12)*math.log(n)-math.log(K)
        residuals.append({'n':n,'log_normalized_residual':format(remainder,'.12g')})
    return {'scope':'Noncertified floating-point illustrations, no fitted constants or finite crossover',
            'airy_zero_decimal_input':AIRY_ZERO,'airy_derivative_decimal_input':AIRY_DERIVATIVE,
            'constants':{key:format(value,'.12g') for key,value in raw.items()},
            'finite_residuals':residuals,
            'precision_note':'Decimal Airy inputs are rounded reference evaluations; output is ordinary platform math, not interval arithmetic'}


def main(argv=None):
    parser=argparse.ArgumentParser(description=__doc__)
    sub=parser.add_subparsers(dest='command',required=True)
    counter=sub.add_parser('counts'); counter.add_argument('--max-n',default=MAX_N,type=lambda s:canonical_integer(s,MAX_N))
    series=sub.add_parser('series'); series.add_argument('--max-n',default=80,type=lambda s:canonical_integer(s,MAX_SERIES))
    sub.add_parser('verify'); sub.add_parser('illustrations')
    crossing=sub.add_parser('threshold')
    crossing.add_argument('--value',required=True,type=lambda s:canonical_integer(s,MAX_TARGET))
    crossing.add_argument('--max-n',default=MAX_N,type=lambda s:canonical_integer(s,MAX_N))
    args=parser.parse_args(argv)
    if args.command=='counts':
        result={'max_n':args.max_n,'counts':[str(v) for v in counts(args.max_n)],'arithmetic':'exact Python integers'}
    elif args.command=='series':
        result={'max_n':args.max_n,'counts':[str(v) for v in q_series(args.max_n)],'arithmetic':'exact reciprocal H formal q series'}
    elif args.command=='verify': result=verify()
    elif args.command=='illustrations': result=illustrations()
    else: result=threshold(args.value,args.max_n)
    print(json.dumps(result,indent=2,sort_keys=True,ensure_ascii=True))


if __name__=='__main__':
    try:
        main()
    except (TypeError,ValueError,RuntimeError) as error:
        print('Check failed: '+str(error),file=sys.stderr)
        sys.exit(1)
