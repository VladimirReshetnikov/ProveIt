#!/usr/bin/env python3
"""Bounded exact triangular-matrix counts and historical size conventions."""
from __future__ import annotations
import sys
sys.dont_write_bytecode = True
if not hasattr(sys, 'set_int_max_str_digits'):
    raise RuntimeError('Python 3.11 or newer is required')
sys.set_int_max_str_digits(640)
import argparse
from fractions import Fraction
import hashlib
import json
from math import comb
from common import ROOT, REPORT_NUMBER, emit, integer, new_file_path, require

MAX_N = 2000
MAX_CHECK_N = 40


def row(n, binary=False):
    integer(n, 0, MAX_N, 'total size')
    require(isinstance(binary, bool), 'binary flag must be bool')
    if n == 0:
        return [1]
    if binary:
        return [comb(m*(m-1)//2, n-m) if n-m <= m*(m-1)//2 else 0 for m in range(1,n+1)]
    return [comb(m*(m+1)//2+n-m-1, n-m) for m in range(1,n+1)]


def counts(n):
    integer(n, 0, MAX_N, 'total size')
    return sum(row(n)), sum(row(n, True))


def triangle(n, k):
    """The source index convention A098568(n,k)=T(n+1,k+1)."""
    integer(n, 0, MAX_N-1, 'triangle row')
    integer(k, 0, n, 'triangle column')
    return comb((k+1)*(k+2)//2+n-k-1, n-k)


def integer_record(value):
    require(isinstance(value,int) and not isinstance(value,bool) and 0 <= value <= (1 << 40000), 'nonnegative count must be an integer of at most 40001 bits')
    raw = value.to_bytes(max(1, (value.bit_length()+7)//8), 'big')
    result = {'bits':value.bit_length(), 'bytes':len(raw),
              'unsigned_big_endian_sha256':hashlib.sha256(raw).hexdigest()}
    if value.bit_length() <= 512:
        result['decimal'] = str(value)
    return result


def polynomial_rows(max_n, binary=False):
    """Independently multiply cell generating polynomials, with no binomials."""
    integer(max_n, 0, MAX_CHECK_N, 'polynomial size bound')
    require(isinstance(binary,bool), 'binary flag must be bool')
    result = {0:[1]}
    result.update({n:[] for n in range(1,max_n+1)})
    for m in range(1,max_n+1):
        qmax = max_n-m
        coefficients = [1]+[0]*qmax
        cells = m*(m-1)//2 if binary else m*(m+1)//2
        for unused in range(cells):
            if binary:
                for q in range(qmax,0,-1):
                    coefficients[q] += coefficients[q-1]
            else:
                for q in range(1,qmax+1):
                    coefficients[q] += coefficients[q-1]
        for n in range(m,max_n+1):
            result[n].append(coefficients[n-m])
    return result


def collision_moment_rows(max_n):
    """Cell-polynomial DP for counts and summed violation indicators."""
    integer(max_n,0,MAX_CHECK_N,'collision moment size bound')
    result={0:[(1,0,0)]}
    result.update({n:[] for n in range(1,max_n+1)})
    for m in range(1,max_n+1):
        qmax=max_n-m;M=m*(m+1)//2
        weights=[1]+[0]*qmax
        diagonal=[0]*(qmax+1);offdiagonal=[0]*(qmax+1)
        for cell in range(M):
            new_weights=[];new_diagonal=[];new_offdiagonal=[]
            cumulative_weight=cumulative_diagonal=cumulative_offdiagonal=0
            for q in range(qmax+1):
                cumulative_weight+=weights[q]
                cumulative_diagonal+=diagonal[q]
                cumulative_offdiagonal+=offdiagonal[q]
                new_weights.append(cumulative_weight)
                # A diagonal cell is bad at residual >=1, an off-diagonal
                # cell at residual >=2. Shifted coefficient sums count each.
                new_diagonal.append(cumulative_diagonal+(new_weights[q-1] if cell<m and q>=1 else 0))
                new_offdiagonal.append(cumulative_offdiagonal+(new_weights[q-2] if cell>=m and q>=2 else 0))
            weights,diagonal,offdiagonal=new_weights,new_diagonal,new_offdiagonal
        for n in range(m,max_n+1):
            q=n-m
            result[n].append((weights[q],diagonal[q],offdiagonal[q]))
    return result


def verify(max_n=MAX_CHECK_N):
    integer(max_n, 26, MAX_CHECK_N, 'verification size bound')
    fixture = json.loads((ROOT/'code/source_prefixes.json').read_text())
    for key, binary in (('A098569',False),('A121690',True)):
        record = fixture[key]
        actual = [sum(row(n,binary)) for n in range(1,len(record['terms'])+1)]
        require(actual == record['terms'], 'historical source size shift: '+key)
    require(counts(0)==(1,1), 'empty objects count once')
    polynomial = [polynomial_rows(max_n,b) for b in (False,True)]
    moment_rows=collision_moment_rows(max_n)
    require(moment_rows[0]==[(1,0,0)],'empty object has no violations')
    entries=products=transforms=collision_checks=moment_checks=0
    records=[]
    for n in range(max_n+1):
        ordinary,binary = row(n),row(n,True)
        require(ordinary==polynomial[0][n] and binary==polynomial[1][n], 'independent cell-polynomial count')
        records.append({'N':n,'b_N':integer_record(sum(ordinary)), 'c_N':integer_record(sum(binary))})
        if n==0:
            continue
        for m,(den,num) in enumerate(zip(ordinary,binary),1):
            entries+=1
            require(triangle(n-1,m-1)==den, 'A098568 dimension and size shift')
            require(0<=num<=den, 'binary inclusion count')
            q=n-m; M=m*(m+1)//2; L=M-m
            moment_count,diagonal_sum,offdiagonal_sum=moment_rows[n][m-1]
            require(moment_count==den,'collision-moment DP count agrees with total count')
            expected_diagonal=Fraction(m*q,M+q-1) if q>=1 else Fraction(0)
            expected_offdiagonal=Fraction(L*q*(q-1),(M+q-1)*(M+q-2)) if q>=2 else Fraction(0)
            require(Fraction(diagonal_sum,den)==expected_diagonal,'diagonal violation first moment')
            require(Fraction(offdiagonal_sum,den)==expected_offdiagonal,'off-diagonal violation first moment')
            moment_checks+=2
            # This finite product is exact rational arithmetic, including infeasibility.
            product=Fraction(1)
            for j in range(q):
                product*=Fraction(L-j,M+j)
            require(product==Fraction(num,den), 'conditional binary product identity')
            products+=1
            transformed=sum((comb(m*(m-1)//2,k-m) if k-m<=L else 0)*comb(n-1,k-1)
                            for k in range(m,n+1))
            require(transformed==den, 'fixed-dimension binomial transform')
            transforms+=1
            # Residual-cell tails from exact stars-and-bars counts.
            for k in (1,2):
                lhs=Fraction(comb(M+q-k-1,q-k),den) if q>=k else Fraction(0)
                falling=Fraction(1)
                for j in range(k):
                    if q-j<=0:
                        falling=Fraction(0);break
                    falling*=Fraction(q-j,M+q-1-j)
                require(lhs==falling, 'residual-cell tail identity')
                collision_checks+=1
    b=[sum(row(n)) for n in range(max_n+1)]
    c=[sum(row(n,True)) for n in range(max_n+1)]
    require(all(b[n+1]>b[n] for n in range(1,max_n)), 'finite ordinary monotonicity')
    require(all(c[n+1]>=c[n] for n in range(max_n)), 'finite binary monotonicity')
    require(all(b[n]==sum(comb(n-1,k-1)*c[k] for k in range(1,n+1)) for n in range(1,max_n+1)),
            'total binomial transform')
    large=[{'N':n,'b_N':integer_record(bn),'c_N':integer_record(cn)}
           for n in (100,200,500,1000,2000) for bn,cn in (counts(n),)]
    return {'status':'PASS','report_number':REPORT_NUMBER,'scope':'Exact bounded arithmetic checks, not an asymptotic proof',
            'size_range':[0,max_n], 'empty_convention':{'b_0':1,'c_0':1},
            'source_shifts':{'b_N':'A098569(N-1) for N>=1','c_N':'A121690(N-1) for N>=1',
                             'A098568(n,k)':'T(n+1,k+1)'},
            'source_prefix_lengths':{k:len(v['terms']) for k,v in fixture.items()},
            'cell_polynomial_rows_checked':2*(max_n+1), 'triangle_entries_checked':entries,
            'conditional_products_checked':products,'fixed_dimension_binomial_transforms_checked':transforms,
            'residual_cell_tail_checks':collision_checks,'collision_expectations_checked':moment_checks,
            'collision_moment_pairs_checked':entries,
            'collision_edge_conventions':{'diagonal_bad':'zero for q=0','offdiagonal_bad':'zero for q<2','empty_object':[0,0]},
            'total_binomial_transforms_checked':max_n,
            'small_counts':records,'large_count_byte_hashes':large,
            'hash_encoding':'minimal nonempty unsigned big-endian bytes; zero is one zero byte'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-n',type=int,default=MAX_CHECK_N)
    parser.add_argument('--output')
    args=parser.parse_args()
    integer(args.max_n,26,MAX_CHECK_N,'verification size bound')
    if args.output is not None:new_file_path(args.output)
    emit(verify(args.max_n),args.output)


if __name__=='__main__':
    try:main()
    except (ValueError,RuntimeError,OSError,ArithmeticError) as exc:raise SystemExit(str(exc))
