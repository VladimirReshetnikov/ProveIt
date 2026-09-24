#!/usr/bin/env python3
"""Exact checks of a wrong-index first/main Pell subsystem family.

The auxiliary rank block and the coding/packed-r equations are not
asserted. The companion proof gives an explicit mod-three obstruction
to extending this family to the full n=q^8 packing.
"""
import json
from pathlib import Path

from round37_1980_base_two_pell_regression import pell_power


def check_case(h):
    p,t,r = 6*h+1,3*h+2,3*h+1
    J = 2*r+1
    U = 1 << p
    numerator = (U+1)**(2*h)
    denominator = U**h*(1 << (2*h+1))
    Y,remainder = divmod(numerator,denominator)
    assert 0 < 5*remainder < denominator
    assert Y >= 1 << (4*h) and Y % (1 << (4*h)) == 0
    a = Y*(U+1)
    A,D = a+2,(a+2)**2-1
    E,P = U*Y,2*U*Y*Y+1
    d,c = pell_power(A,p)
    first_chi,k = pell_power(P,t)
    assert d*d-D*c*c == 1
    assert first_chi*first_chi-(P*P-1)*k*k == 1
    eta,zeta = c-Y*k,(Y+1)*k-c
    assert eta > 0 and zeta > 0 and eta+zeta == k
    # R0=F^3/Y^2 lies strictly between Y and Y+2/3.
    Rnum,Rden = numerator**3,denominator**3*Y*Y
    assert Y*Rden < Rnum and 3*Rnum < (3*Y+2)*Rden
    assert c*Rden > k*Rnum
    assert (c*Rden-k*Rnum)*(U+1) < 48*h*k*Rden
    assert U+1 > 144*h and a > 24*h
    tau,tau_rem = divmod(first_chi-1,2)
    h_index,h_rem = divmod(k-t,E)
    gamma,gamma_rem = divmod(d-U-a*c,4*a+3)
    assert min(tau,h_index,gamma) > 0
    assert tau_rem == h_rem == gamma_rem == 0
    assert tau*(tau+1) == (E*E+U)*(Y*k)**2
    # Pick a scaling power n<=r; the full relation n=q^8 is not imposed.
    n = 1 << (r.bit_length()-1)
    assert n <= r < 2*n and U % (n*n) == Y % (n*n) == 0
    w,s = U//(n*n),Y//(n*n)
    assert w > 0 and s > 0 and a > n**4 and E > r+1
    assert p == J-2 and r % 3 == 1
    # For every integer S,Tplus and n=2^(8j), packed r is 0 mod3.
    assert all(((1 << (8*j))**2-(1 << (8*j))) % 3 == 0 and
               ((1 << (8*j))**2-1) % 3 == 0 for j in range(1,5))
    return dict(h=h,p=p,t=t,r=r,claimed_index=J,n=n,
                U_bits=U.bit_length(),Y_bits=Y.bit_length(),c_bits=c.bit_length(),
                Y_two_adic_valuation=(Y & -Y).bit_length()-1,
                strict_positive_interval=True,
                positive_tau_index_and_exponent_quotients=True,
                scaled_first_and_main_norms=True,
                wrong_main_index=True,
                full_packing_excluded_modulo_three=True)


def verify():
    cases = [check_case(h) for h in (2,3,4,8,16,21,31)]
    return dict(status='PASS',cases=cases,
                scope='Wrong-index first/main Pell subsystem only. No auxiliary rank block, admissible code, second fixed index, or packed-r equation is asserted. The family is incompatible with full power-of-two n=q^8 packing modulo three.',
                proof='../1980/EXPLORATION_BASE_TWO_WRONG_INDEX_RATIONAL.md')


if __name__ == '__main__':
    result = verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status'],len(result['cases']),'exact wrong-index Pell subsystem cases',flush=True)
