#!/usr/bin/env python3
"""Exact bounded enumeration of labelled square nonnegative integer tables.

Rows and columns each have margin n. Sorting residual capacities is only a
memoization symmetry: every labelled row option is counted with its full
multiplicity. A second unsorted recursion independently checks n <= 3.
"""
import argparse
from functools import lru_cache
import sys
sys.dont_write_bytecode=True
from common import emit, integer, new_file_path, require

EXPECTED=(1,1,3,55,10147,22069251)


def count_tables(n):
    integer(n,0,5,'table dimension')
    @lru_cache(None)
    def rows(rem):
        if not any(rem):return 1
        def options(i,total,rr):
            if i==n:
                if total==0:yield tuple(sorted(rr))
                return
            for x in range(min(total,rem[i])+1):
                yield from options(i+1,total-x,rr+(rem[i]-x,))
        return sum(rows(rr) for rr in options(0,n,()))
    return rows((n,)*n)


def count_tables_labelled(n):
    integer(n,0,3,'independent table dimension')
    @lru_cache(None)
    def recurse(remaining_rows,capacities):
        if remaining_rows==0:return int(all(c==0 for c in capacities))
        total=0
        # Generate each weak composition of n directly; do not sort capacities.
        def compositions(left,places,prefix=()):
            if places==0:
                if left==0:yield prefix
                return
            for x in range(left+1):
                yield from compositions(left-x,places-1,prefix+(x,))
        for row in compositions(n,n):
            if all(x<=c for x,c in zip(row,capacities)):
                total+=recurse(remaining_rows-1,tuple(c-x for c,x in zip(capacities,row)))
        return total
    return recurse(n,(n,)*n)


def receipt():
    values={}
    for n in range(6):
        value=count_tables(n)
        require(value==EXPECTED[n],'exact table prefix mismatch')
        values[str(n)]=value
    independently={str(n):count_tables_labelled(n) for n in range(4)}
    require(all(values[n]==v for n,v in independently.items()),'labelled enumeration mismatch')
    return {'status':'PASS','exact_counts':values,'independent_unsorted_counts':independently,
            'definition':'n by n labelled nonnegative integer tables, every row and column sum n; empty table counted once',
            'scope':'Exact counts only for the stated finite range; no fitted asymptotic coefficients.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--n',type=int,help='single dimension 0..5; default fixed receipt')
    parser.add_argument('--output')
    args=parser.parse_args()
    if args.output is not None:new_file_path(args.output)
    data=receipt() if args.n is None else {'n':integer(args.n,0,5,'table dimension'),'count':count_tables(args.n)}
    emit(data,args.output)


if __name__=='__main__':
    try:main()
    except (ValueError,RuntimeError,OSError,ArithmeticError) as exc:raise SystemExit(str(exc))
