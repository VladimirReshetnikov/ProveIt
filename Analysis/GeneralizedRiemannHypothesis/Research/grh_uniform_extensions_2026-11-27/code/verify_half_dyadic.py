#!/usr/bin/env python3
"""Exact finite checks for the simultaneous dyadic-deletion theorem.

No third-party packages required. Angular sectors use fractions.Fraction.
Root powers use fixed-point integer intervals with outward rounding; all
assertions are exact. Decimal values are descriptive, not proof inputs.
"""
from fractions import Fraction
from decimal import Decimal, localcontext
from pathlib import Path
import json

BITS = 160
D = 1 << BITS
ROOT_STEPS = 110


def floor_q(x):
    return x.numerator // x.denominator


def ceil_q(x):
    return -((-x.numerator) // x.denominator)


def angular_sectors(indices):
    """Closed sectors theta/pi in [0,1] with Re(z**(2**j)) <= 0.

    Radius is irrelevant. Boundary inclusion facilitates exact endpoint
    checks; the theorem uses the corresponding strict inequalities.
    """
    intervals = [(Fraction(0), Fraction(1))]
    for j in indices:
        e = 1 << j
        new_intervals = []
        for lo, hi in intervals:
            for k in range(floor_q((lo*e-Fraction(3,2))/2)-1,
                           ceil_q((hi*e-Fraction(1,2))/2)+2):
                left = Fraction(4*k+1, 2*e)
                right = Fraction(4*k+3, 2*e)
                a, b = max(lo, left), min(hi, right)
                if a < b:
                    new_intervals.append((a, b))
        intervals = sorted(set(new_intervals))
    return intervals


def mul_interval(x, y):
    """Multiply nonnegative fixed-point intervals with denominator D."""
    a,b = x
    c,d = y
    assert 0 <= a <= b and 0 <= c <= d
    return (a*c // D, (b*d+D-1)//D)


def power_interval(x, e):
    result = (D,D)
    base = x
    while e:
        if e & 1:
            result = mul_interval(result, base)
        e >>= 1
        if e:
            base = mul_interval(base, base)
    return result


def bracket_root(L):
    """Certified bracket of the root r+r**L=1."""
    lo, hi = D//2, D
    decisions = 0
    for _ in range(ROOT_STEPS):
        mid = (lo+hi)//2
        p,q = power_interval((mid,mid),L)
        if mid+q < D:
            lo = mid
        elif mid+p > D:
            hi = mid
        else:
            raise AssertionError('Increase fixed-point precision')
        decisions += 1
    # Reconfirm endpoint sign with exact outward rounding.
    p,q = power_interval((lo,lo),L)
    assert lo+q < D
    p,q = power_interval((hi,hi),L)
    assert hi+p > D
    assert hi-lo <= D//(1 << (ROOT_STEPS+1)) + 1
    return lo,hi,decisions


def decimal_ratio(a,b,places=24):
    with localcontext() as ctx:
        ctx.prec = places+8
        return str(+(Decimal(a)/Decimal(b)))


def verify():
    angular=[]
    for n in range(2,20,2):
        L=1 << (n-1)
        indices=[0]+list(range(1,n,2))
        sectors=angular_sectors(indices)
        expected=Fraction(2,3)+Fraction(1,6*L)
        assert max(hi for lo,hi in sectors) == expected
        assert all(hi <= expected for lo,hi in sectors)
        assert any(lo < Fraction(2,3) < hi for lo,hi in sectors)
        angular.append(dict(n=n,L=L,retained_indices=indices,
                            number_of_sectors=len(sectors),
                            exact_upper_theta_over_pi=str(expected),
                            exact_total_sector_length=str(sum((hi-lo for lo,hi in sectors),Fraction(0)))))

    radii=[]
    for n in [2,4,6,8,10,12,16,20,30,40]:
        L=1 << (n-1)
        indices=[0]+list(range(1,n,2))
        lo,hi,decisions=bracket_root(L)
        assert D//2 < lo < hi < D
        # Certified strict inactivity at all retained interior exponents:
        # c^2 - |1+(r exp(2 pi i/3))^e|^2 = (r-t)(r+t-1), t=r^e.
        gaps=[]
        for j in indices[1:-1]:
            e=1 << j
            a,b=power_interval((lo,hi),e)
            lower_first=lo-b
            lower_second=lo+a-D
            assert lower_first > 0
            assert lower_second > 0
            gaps.append(dict(index=j,gap_lower_numerator=lower_first*lower_second,
                             gap_denominator=D*D))
        with localcontext() as ctx:
            ctx.prec=60
            r=Decimal(lo+hi)/Decimal(2*D)
            c=(1-r+r*r).sqrt()
            # Exact formula, descriptive decimal arithmetic only.
            pi=Decimal('3.14159265358979323846264338327950288419716939937510582097494459')
            coeff=2*c/(pi*Decimal(3).sqrt())*(1/r+1/(Decimal(L)*(1-r)))
            row=dict(n=n,L=L,retained_count=len(indices),full_count=n,
                     r_lo_numerator=lo,r_hi_numerator=hi,denominator=D,
                     exact_bisection_decisions=decisions,
                     radius_decimal=str(r),constant_decimal=str(c),
                     angular_coefficient_decimal=str(coeff),
                     certified_inactive_gaps=gaps)
            radii.append(row)
    return dict(status='PASS',arithmetic='exact rational sectors and integer interval powers',
                fixed_point_bits=BITS,root_bisections=ROOT_STEPS,
                angular_checks=angular,radius_checks=radii,
                scope='Finite checks support the all-n mathematical proof; no optimization is used.')


def main():
    result=verify()
    directory=Path(__file__).resolve().parents[1]/'data'
    directory.mkdir(exist_ok=True)
    (directory/'half_dyadic_checks.json').write_text(json.dumps(result,indent=2)+'\n')
    lines=['PASS: exact checks for simultaneous even-index deletion.',
           f'Angular barrier: {len(result["angular_checks"])} even lengths, n=2 through 18.',
           f'Certified radius and inactive-constraint checks: {len(result["radius_checks"])} lengths, n=2 through 40.',
           f'Power intervals: {BITS}-bit fixed point, outward rounding.',
           '', 'n  retained/full  c_n (illustration)  angular coefficient (illustration)']
    for r in result['radius_checks']:
        lines.append(f'{r["n"]:2} {r["retained_count"]:2}/{r["full_count"]:<2}  {r["constant_decimal"][:23]}  {r["angular_coefficient_decimal"][:23]}')
    lines.extend(['',result['scope']])
    report='\n'.join(lines)+'\n'
    (directory/'half_dyadic_verification.txt').write_text(report)
    print(report,end='')

if __name__ == '__main__':
    main()
