#!/usr/bin/env python3
"""Rounded floating diagnostics from a small immutable OEIS count fixture.

These outputs are not interval certificates or finite-n remainder bounds.
Counts beyond n=5 are source data, not recomputed by the public dynamic program.
The only supported dimensions are 4,5,6,8,10,13; precision is fixed at 80 digits.
"""
import sys
sys.dont_write_bytecode=True
import argparse
import mpmath as mp
from common import emit, integer, new_file_path, require

COUNTS={
    4:10147,
    5:22069251,
    6:602351808741,
    8:1046591482728407939338275,
    10:66880713903767740581650957184096513655153,
    13:514016665650183402309555825250370336139392333285719205357202846243695510965,
}


def six_places(value):
    # Decimal-place rounding without conversion through binary machine float.
    magnitude=int(mp.floor(abs(value)*1000000+mp.mpf('0.5')))
    whole,decimal=divmod(magnitude,1000000)
    return ('-' if value<0 else '')+str(whole)+'.'+str(decimal).zfill(6)


def diagnostic(n):
    integer(n,4,13,'diagnostic dimension')
    require(n in COUNTS,'unsupported diagnostic dimension')
    with mp.workdps(80):
        x=mp.mpf(n)
        log_L=x*x*mp.log(4)-(x-mp.mpf('0.5'))*mp.log(4*mp.pi)-(x-1)*mp.log(x)+mp.mpf('0.25')
        ratio=mp.log(COUNTS[n])-log_L
        D1=x*ratio; D2=x*x*(ratio+mp.mpf('1.5')/x)
        return {'n':n,'exact_input_count':str(COUNTS[n]),
                'count_covered_by_public_DP_receipt':n<=5,
                'D1_6_decimal_places':six_places(D1),'D2_6_decimal_places':six_places(D2),
                'D1_25_significant_digits':mp.nstr(D1,25),'D2_25_significant_digits':mp.nstr(D2,25)}


def diagnostics():
    return {'status':'COMPUTED_APPROXIMATELY','decimal_working_precision':80,
            'rows':[diagnostic(n) for n in (4,5,6,8,10,13)],
            'source':'https://oeis.org/A110058/b110058.txt',
            'scope':'Floating-point diagnostics only; not interval-certified and not part of an exact mathematical receipt.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output')
    args=parser.parse_args()
    if args.output is not None:new_file_path(args.output)
    emit(diagnostics(),args.output)


if __name__=='__main__':
    try:main()
    except (ValueError,RuntimeError,OSError,ArithmeticError) as exc:raise SystemExit(str(exc))
