#!/usr/bin/env python3
"""Certify the first change of sign in the Riemann Li second differences.

Run python3 certify_window.py [--csv window_bounds.csv] beside certify_zeta.py,
moment_constants.py and constants_verify.py. MPFI and MPFR are required.
"""
import argparse
import csv
import ctypes
from fractions import Fraction

from certify_zeta import I, bind, certify_heights, mpfr
from moment_constants import moment_constants


def to_mpfi(value):
    """Enclose a rational interval using MPFI's directed arithmetic."""
    def convert(q):
        return I(q.numerator)/I(q.denominator)
    return convert(value.lo).binary("union", convert(value.hi))


# Exact outward rounding for CSV endpoints. The binary64 conversion is
# directed in MPFR, then Fraction.from_float converts that exact double.
get_double = bind(mpfr, "mpfr_get_d", ctypes.c_double,
                  [ctypes.c_void_p,ctypes.c_int])


def decimal_endpoint(value, lower, places=12):
    endpoint = value.data.left if lower else value.data.right
    direction = 3 if lower else 2  # MPFR_RNDD or MPFR_RNDU
    binary_value = get_double(ctypes.byref(endpoint), direction)
    scaled = Fraction.from_float(binary_value)*10**places
    integer = scaled.__floor__() if lower else scaled.__ceil__()
    digits = str(abs(integer)).zfill(places+1)
    return ("-" if integer < 0 else "") + digits[:-places] + "." + digits[-places:]


def certify(csv_path=None):
    heights = certify_heights()
    weights = [I(2)/(I("0.25")+t*t) for t in heights]
    # Exact identity: x=1-cos(theta)=1/[2(1/4+t^2)]=w/4 for a pair.
    xs = [w/4 for w in weights]
    angles = [2*(I("0.5")/t).unary("atan") for t in heights]
    total, first, second = map(to_mpfi, moment_constants())
    residual0 = total - sum(weights,I(0))
    residual1 = first - sum((w*x for w,x in zip(weights,xs)),I(0))
    residual2 = second - sum((w*x*x for w,x in zip(weights,xs)),I(0))
    for residual in (residual0,residual1,residual2):
        assert I(0).strictly_below(residual)
    rows = []
    for n in range(119):
        finite = sum((w*(n*a).unary("cos")
                      for w,a in zip(weights,angles)),I(0))
        low = finite + residual0 - n*n*residual1
        # T_n''(1)/2=n^2(n^2-1)/6.
        high = low + n*n*(n*n-1)*residual2/6
        if n < 118:
            assert I("0.00014").strictly_below(low), n
        else:
            assert high.strictly_below("-0.00026"), n
        rows.append((n, decimal_endpoint(low,True), decimal_endpoint(high,False)))

    if csv_path is not None:
        with open(csv_path, "w", encoding="ascii", newline="") as f:
            writer = csv.writer(f)
            writer.writerow(("n","lower_bound","upper_bound"))
            writer.writerows(rows)
    print("Certified d_n > 0.00014 for every n=0,...,117.")
    print("Certified d_118 < -0.00026.")
    for n in (0,100,116,117,118):
        print(f"  {rows[n][1]} <= d_{n} <= {rows[n][2]}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--csv", metavar="PATH", help="write certified decimal bounds")
    certify(parser.parse_args().csv)
