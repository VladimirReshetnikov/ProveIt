"""Fresh exact rational interval checks and data-only coefficient comparison.

Intervals are rounded OUTWARD to dyadic rationals after arithmetic. Logarithms
use the positive atanh series with a geometric tail bound; square roots use
integer square root; exponentials use alternating Taylor bounds. No float or
Decimal value participates in an assertion. Only two JSON data files are read.
"""
from fractions import Fraction as F
from math import isqrt, factorial
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parent
SOURCE = Path('/workspace/shared/arity-table-asymptotics-20261004/evidence/exact.json')
BITS = 1024
SCALE = 1 << BITS

def floor(q):
    return q.numerator // q.denominator

def ceil(q):
    return -floor(-q)

class Interval:
    def __init__(self, lo, hi=None):
        lo, hi = F(lo), F(lo if hi is None else hi)
        assert lo <= hi
        self.lo = F(floor(lo*SCALE), SCALE)
        self.hi = F(ceil(hi*SCALE), SCALE)

    def __add__(self, other):
        return Interval(self.lo+other.lo, self.hi+other.hi)

    def __neg__(self):
        return Interval(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + (-other)

    def __mul__(self, other):
        values = [a*b for a in (self.lo,self.hi) for b in (other.lo,other.hi)]
        return Interval(min(values), max(values))

    def reciprocal(self):
        assert self.lo > 0 or self.hi < 0
        return Interval(1/self.hi,1/self.lo)

    def __truediv__(self, other):
        return self * other.reciprocal()

    def power(self, k):
        if k < 0:
            return self.reciprocal().power(-k)
        out = Interval(1)
        for _ in range(k):
            out = out*self
        return out

    def sqrt(self):
        assert self.lo >= 0
        lo = isqrt(floor(self.lo*SCALE*SCALE))
        hi = isqrt(floor(self.hi*SCALE*SCALE))+1
        return Interval(F(lo,SCALE),F(hi,SCALE))

def log_positive(x, count):
    assert x >= 1
    z = Interval((x-1)/(x+1))
    z2 = z*z
    power = z
    partial = Interval(0)
    for j in range(count):
        partial = partial + power*Interval(F(2,2*j+1))
        power = power*z2
    # Current power encloses z^(2count+1); denominators only increase.
    remainder = F(2,2*count+1)*power.hi/(1-z2.hi)
    return Interval(partial.lo,partial.hi+remainder)

def exp_negative(x, count=80):
    assert 0 <= x.lo <= x.hi < 1
    assert count % 2 == 0
    term = Interval(1)
    partial = Interval(1)
    for j in range(1,count+1):
        term = term*x*Interval(F(1,j))
        partial = partial + (term if j % 2 == 0 else -term)
    next_term = term*x*Interval(F(1,count+1))
    return Interval(partial.lo-next_term.hi, partial.hi)

def evaluate(terms, s, lam):
    result = Interval(0)
    for term in terms:
        value = Interval(F(term['coefficient']))
        value = value*s.power(term['s'])*lam.power(term['lambda_power'])
        result = result+value
    return result

def decimal_bounds(interval, places=12):
    # Display only: integer arithmetic still rounds outward.
    unit = 10**places
    def render(integer):
        prefix = '-' if integer < 0 else ''
        integer = abs(integer)
        return prefix+str(integer//unit)+'.'+str(integer%unit).zfill(places)
    return [render(floor(interval.lo*unit)),render(ceil(interval.hi*unit))]

def main():
    ours = json.loads((ROOT/'evidence'/'mathematics.json').read_text())
    source = json.loads(SOURCE.read_text())
    coefficient_checks = 0
    for name in ('P','L','D'):
        for k, terms in enumerate(source[name]):
            left = {(v['s'],-v['h']):F(v['coefficient']) for v in terms}
            assert all(v['t']==0 for v in terms)
            right = {(v['s'],v['lambda_power']):F(v['coefficient']) for v in ours[name][k]}
            assert left == right
            coefficient_checks += 1
    for item in source['initial_terms']:
        n = item['n']
        assert item['a_n'] == ours['initial_values'][n]
        assert int(item['C_n']) == int(ours['initial_values'][n])+1
    lam = log_positive(F(2),400)
    assert F(69,100) < lam.lo <= lam.hi < F(70,100)
    cases = []
    for n in (16,32,64):
        for extra in (0,1):
            value = int(ours['initial_values'][n])+extra
            logarithm_correction = log_positive(F(value,1 << (n*n)),80)
            s = (Interval(n*n)+logarithm_correction/lam).sqrt()
            assert s.lo > n
            t = Interval(F(1,1 << n))*exp_negative(lam*(s-Interval(n)))
            approx = s
            for m in range(1,7):
                approx = approx+evaluate(ours['D'][m],s,lam)*t.power(m)
                remainder = Interval(n)-approx
                assert remainder.hi < 0
                leading = Interval(-F(ours['c'][m+1],2*factorial(m+1)))*s.power(m)*t.power(m+1)/lam
                ratio = remainder/leading
                assert ratio.lo > 0
                cases.append(dict(n=n,sequence='C' if extra else 'a',M=m,
                                  remainder_interval=[str(remainder.lo),str(remainder.hi)],
                                  negative_remainder_certified=True,
                                  ratio_to_sharp_leading_interval=[str(ratio.lo),str(ratio.hi)],
                                  ratio_decimal_outward=decimal_bounds(ratio)))
    result = dict(dyadic_precision_bits=BITS,source_coefficient_families_compared=coefficient_checks,
                  source_sequence_values_compared=len(source['initial_terms']),
                  rigorous_signed_sequence_point_cases=len(cases),
                  lambda_interval=[str(lam.lo),str(lam.hi)],
                  no_floating_point_assertions=True,cases=cases)
    with (ROOT/'evidence'/'enclosures.json').open('x') as f:
        json.dump(result,f,indent=2,sort_keys=True)
        f.write('\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('cases','lambda_interval')},indent=2))
    for case in cases:
        print(case['sequence'],case['n'],case['M'],case['ratio_decimal_outward'])

if __name__ == '__main__':
    main()
