#!/usr/bin/env python3
"""Exact restricted two-cover counts. Python 3.11+, standard library only."""
from fractions import Fraction
from math import comb
import argparse
import json

MAX_INDEX = 640
P = {
    'V': {1: Fraction(-1,2)},
    'U': {1: Fraction(1,2)},
    'L': {1: Fraction(1,2), 3: Fraction(-1,6), 4: Fraction(-1,4),
          5: Fraction(-1,8), 6: Fraction(-1,48)},
    'legacy': {1: Fraction(1,2), 3: Fraction(-1,6)},
}

def decimal(value):
    """Local base-10 rendering; never changes Python's process-wide digit limit."""
    if isinstance(value,Fraction):
        top=decimal(value.numerator)
        return top if value.denominator == 1 else top+'/'+decimal(value.denominator)
    if value == 0: return '0'
    sign='-' if value < 0 else ''
    value=abs(value); chunks=[]
    while value:
        value,rem=divmod(value,10**9)
        chunks.append(rem)
    return sign+str(chunks[-1])+''.join(f'{v:09d}' for v in reversed(chunks[:-1]))

def parse_threshold(value):
    if not value or len(value)>4000 or any(c not in '0123456789' for c in value):
        raise ValueError('threshold must have 1 through 4000 decimal digits')
    answer=0
    for start in range(0,len(value),9):
        part=value[start:start+9]
        answer=answer*10**len(part)+int(part)
    if answer < 1: raise ValueError('threshold must be positive')
    return answer

def bounded_index(n):
    if isinstance(n, bool) or not isinstance(n, int) or not 0 <= n <= MAX_INDEX:
        raise ValueError(f'index must be an integer from 0 to {MAX_INDEX}')
    return n

def bell_numbers(limit):
    if not isinstance(limit, int) or not 0 <= limit <= 2*MAX_INDEX:
        raise ValueError('Bell index outside supported range')
    # Bell triangle avoids factorial-sized binomial coefficients.
    row = [1]
    out = [1]
    for _ in range(limit):
        nxt = [row[-1]]
        for value in row:
            nxt.append(nxt[-1] + value)
        row = nxt
        out.append(row[0])
    return out

def h_values(limit):
    """Poisson moments of product_{j<n}(m^2-m-2j), divided by 2^n."""
    bounded_index(limit)
    bells = bell_numbers(2*limit)
    poly = [1]
    out = []
    for n in range(limit+1):
        value = sum(a*bells[k] for k,a in enumerate(poly))
        if value <= 0:
            raise ArithmeticError('positive Poisson count invariant failed')
        out.append(Fraction(value, 2**n))
        if n < limit:
            nxt = [0]*(len(poly)+2)
            for k,a in enumerate(poly):
                nxt[k] -= 2*n*a
                nxt[k+1] -= a
                nxt[k+2] += a
            poly = nxt
    return out

def exponential_coefficients(p, limit):
    bounded_index(limit)
    out = [Fraction(1)]
    for n in range(1,limit+1):
        out.append(sum((k*v*out[n-k] for k,v in p.items() if k <= n), Fraction())/n)
    return out

def transform(h, p):
    limit = bounded_index(len(h)-1)
    coeff = exponential_coefficients(p, limit)
    out=[]
    for n in range(limit+1):
        total = Fraction()
        falling = 1
        for j in range(n+1):
            total += falling*coeff[j]*h[n-j]
            falling *= n-j
        out.append(total)
    return out

def counts(limit):
    bounded_index(limit)
    h = h_values(limit)
    out = {'H': h}
    for name,p in P.items():
        seq=transform(h,p)
        if any(x.denominator != 1 for x in seq):
            raise ArithmeticError(f'nonintegral {name} count')
        out[name]=[x.numerator for x in seq]
    return out

def first_threshold(seq, threshold):
    """First value >= threshold in the supplied finite sequence; no monotonicity assumption."""
    if isinstance(threshold,bool) or not isinstance(threshold,int) or threshold < 1:
        raise ValueError('threshold must be a positive integer')
    for n,value in enumerate(seq):
        if value >= threshold:
            return {'index':n, 'value':decimal(value), 'previous':decimal(seq[n-1]) if n else None}
    return None

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--max-index', type=int, default=20)
    ap.add_argument('--model', choices=['all','H',*P], default='all')
    ap.add_argument('--threshold')
    args=ap.parse_args()
    try:
        data=counts(args.max_index)
        if args.threshold is not None:
            if args.model in ('all','H'):
                raise ValueError('threshold scans require V, U, L, or legacy')
            ans=first_threshold(data[args.model],parse_threshold(args.threshold))
            result={'model':args.model,'checked_through':args.max_index,'first_crossing':ans,
                    'status':'found' if ans is not None else 'not found in checked range'}
        else:
            result={k:[decimal(v) for v in values] for k,values in data.items()
                    if args.model in ('all',k)}
    except ValueError as exc:
        ap.error(str(exc))
    print(json.dumps(result,indent=2,sort_keys=True))

if __name__ == '__main__':
    main()
