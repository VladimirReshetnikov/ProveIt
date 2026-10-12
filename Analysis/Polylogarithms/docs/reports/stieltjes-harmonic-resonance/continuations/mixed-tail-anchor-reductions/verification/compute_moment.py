#!/usr/bin/env python3
"""Compute a regular centered mixed Hurwitz-tail moment exactly."""
import argparse
import sympy as sp
from research import mixed_moment,linearize
from reduce_values import reduce

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('orders',nargs='+',type=int,help='integer tail orders, each at least 2')
    parser.add_argument('--degree',required=True,type=int,help='nonnegative centered degree of regular parity')
    parser.add_argument('--reduce',action='store_true',help='reduce MZV weights 2 through 9 into the supplied spanning coordinates')
    parser.add_argument('--latex',action='store_true')
    args=parser.parse_args()
    try:
        value=linearize(mixed_moment(tuple(args.orders),args.degree))
        if args.reduce:value=reduce(value)
    except ValueError as error:parser.error(str(error))
    print(sp.latex(value) if args.latex else value)
    print('Normalization: the ordinary bracketed subtraction in article equation (3.4).')
if __name__=='__main__':main()
