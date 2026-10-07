#!/usr/bin/env python3
"""Exact, standard-library-only checks for Report196 (OEIS A239964).

Default: capped sliding-window DP through 250, independent multiplicity-vector
enumeration through 45, and the positive subset-product identity through 55.
--full1000 recomputes and matches every one of the 1,001 pinned OEIS terms.
Every counting operation uses arbitrary-precision Python integers. No fits,
floating-point identities, downloaded programs, or third-party modules are used.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as Q
import hashlib
import json
from math import factorial, isqrt
from pathlib import Path
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).absolute().parent
sys.path.insert(0,str(ROOT))
import symbolic_checks
REFERENCE_SHA256 = 'e215b0baba64bf4afb2df72a642ed4c1e93ba16f87ea0f01ab50d58d87a2814b'


def need(condition, message):
    if not condition:
        raise ValueError(message)


def canonical(value):
    return (json.dumps(value, sort_keys=True, indent=2) + '\n').encode('utf-8')


def terms_bytes(values):
    return ''.join('%d %d\n' % pair for pair in enumerate(values)).encode('ascii')


def reference():
    data = (ROOT / 'data/b239964.txt').read_bytes()
    need(hashlib.sha256(data).hexdigest() == REFERENCE_SHA256, 'pinned b-file hash differs')
    rows = [tuple(map(int, line.split())) for line in data.decode('ascii').splitlines()]
    need(len(rows) == 1001 and all(len(row) == 2 and row[0] == n and row[1] >= 0
                                 for n, row in enumerate(rows)), 'b-file structure differs')
    need(rows[0] == (0, 0), 'empty partition must be excluded')
    return [row[1] for row in rows]


def partition_numbers(nmax):
    p = [1] + [0] * nmax
    for size in range(1, nmax + 1):
        for n in range(size, nmax + 1):
            p[n] += p[n - size]
    return p


def capped_rows(nmax, cap, occupied):
    """Coefficients of product_j (1 + u sum_{b=1}^cap q^(jb)).

    Before processing size j, row k counts partitions using sizes < j and
    exactly k occupied sizes. Descending k leaves row k-1 unmodified. In each
    residue class modulo j, run is the sum of the last cap entries of row k-1.
    Thus adding run permits precisely multiplicities 1,...,cap for size j.
    The minimum old-row degree k(k-1)/2 permits omission of initial zeros.
    """
    rows = [[0] * (nmax + 1) for _ in range(occupied + 1)]
    rows[0][0] = 1
    if cap == 0:
        return rows
    for size in range(1, nmax + 1):
        for k in range(min(occupied, size), 0, -1):
            base = k * (k - 1) // 2
            first = base + size
            if first > nmax:
                continue
            old, current = rows[k - 1], rows[k]
            # At most one contribution is possible once size > nmax/2.
            if 2 * size + base > nmax or cap == 1:
                for n in range(first, nmax + 1):
                    current[n] += old[n - size]
                continue
            outgoing = (cap + 1) * size
            for start in range(first, min(first + size, nmax + 1)):
                run = 0
                for n in range(start, nmax + 1, size):
                    run += old[n - size]
                    if n - outgoing >= base:
                        run -= old[n - outgoing]
                    current[n] += run
    return rows


def diagonal_counts(nmax):
    """Sum [u^m](cap m - cap m-1), reusing adjacent occupancy rows.

    With cap c, row c enters positively and row c+1 negatively. This shares
    one DP evaluation between adjacent diagonal terms. The exact minimum
    weight for D=M=m is m(m+1)/2 + m-1.
    """
    answer = [0] * (nmax + 1)
    maximum = (isqrt(8 * nmax + 17) - 3) // 2
    for cap in range(1, maximum + 1):
        upper = min(cap + 1, maximum)
        rows = capped_rows(nmax, cap, upper)
        for n in range(nmax + 1):
            answer[n] += rows[cap][n]
            if cap < maximum:
                answer[n] -= rows[cap + 1][n]
    need(all(value >= 0 for value in answer), 'negative diagonal coefficient')
    return answer


def direct_enumeration(nmax=45):
    """Enumerate every increasing-size multiplicity vector exactly once."""
    good, all_partitions = [0] * (nmax + 1), [0] * (nmax + 1)
    def visit(total, first, distinct, maximum):
        all_partitions[total] += 1
        if distinct and distinct == maximum:
            good[total] += 1
        for size in range(first, nmax - total + 1):
            for multiplicity in range(1, (nmax - total) // size + 1):
                visit(total + size * multiplicity, size + 1,
                      distinct + 1, max(maximum, multiplicity))
    visit(0, 1, 0, 0)
    return good, all_partitions


def positive_subset_identity(nmax=55):
    """Independent F = sum_S sign(S)(1-q^s) B_S, by literal factors.

    B_S = q^(|S|s) product_{j in S} 1/(1-q^j)
          product_{j not in S} (1+q^(s+j)/(1-q^j)).
    This uses positive B_S factors, not the capped DP or F/P expansion.
    """
    total = [0] * (nmax + 1)
    used = 0
    def subsets(prefix=(), subtotal=0, start=1):
        for j in range(start, nmax + 1):
            selected, summed = prefix + (j,), subtotal + j
            if len(selected) * summed > nmax:
                break
            yield selected, summed
            yield from subsets(selected, summed, j + 1)
    for selected, summed in subsets():
        used += 1
        shift = len(selected) * summed
        limit, members = nmax - shift, set(selected)
        polynomial = [1] + [0] * limit
        for j in range(1, limit + 1):
            old = polynomial[:]
            if j in members:
                for degree in range(j, limit + 1):
                    polynomial[degree] += polynomial[degree - j]
            else:
                for degree in range(summed + j, limit + 1):
                    polynomial[degree] += sum(old[degree - summed - b * j]
                        for b in range(1, (degree - summed) // j + 1))
        sign = 1 if len(selected) % 2 else -1
        for degree, value in enumerate(polynomial):
            total[shift + degree] += sign * value
            if shift + degree + summed <= nmax:
                total[shift + degree + summed] -= sign * value
    return total, used


def saddle_polynomials(maximum=13):
    """Check the exact circular-arc polynomial against its recurrence."""
    previous, current = [1], [1, -1]
    checked = [[1], [1, -1]]
    for m in range(1, maximum):
        following = [0] * (len(current) + 1)
        for j, value in enumerate(current):
            following[j] += 2 * value
            following[j + 1] -= value
        for j, value in enumerate(previous):
            following[j] -= value
        explicit = [(-1)**j * factorial(m + 1 + j) //
                    (factorial(m + 1 - j) * factorial(2 * j))
                    for j in range(m + 2)]
        need(following == explicit, 'saddle polynomial recurrence differs')
        previous, current = current, following
        checked.append(following)
    return checked


def low_order_algebra():
    """Exact rational power-series checks; s is represented by a polynomial."""
    # Degree-w and degree-w^2 coefficients of log[(1-e^-sw)/(sw)],
    # -sum_l (1-e^-sw)^l/[l(e^(lw)-1)], and the deleted-site logs.
    # Each list is indexed by the degree of s. Only l=1,2,3 contribute.
    pref1, pref2 = [0, Q(-1,2)], [0,0,Q(1,24)]
    q1 = [0,Q(1,2),Q(1,2)-Q(1,4)]
    q2 = [0,Q(-1,12),Q(-1,4)+Q(1,4),Q(-1,6)+Q(1,4)-Q(1,9)]
    def add(*vectors):
        out=[Q(0)]*max(map(len,vectors))
        for vector in vectors:
            for j, value in enumerate(vector): out[j] += value
        return out
    l1=add(pref1,q1); l2=add(pref2,q2,[0,0,-1])
    need(l1 == [0,0,Q(1,4)], 'first normalized log coefficient differs')
    need(l2 == [0,Q(-1,12),Q(-23,24),Q(-1,36)], 'second normalized log coefficient differs')
    t3=l2+[Q(1,32)]
    # Set z=tau/A. Divide the r=1,2,3 saddle polynomials by r=0.
    def ratio_coefficients(r, length):
        p=[Q((-1)**h*factorial(r+1+h), factorial(h)*factorial(r+1-h)*4**h)
           for h in range(r+2)]
        out=[]
        for j in range(length): out.append((p[j] if j<len(p) else Q(0))+(out[-1]/2 if out else 0))
        return out
    need(ratio_coefficients(1,3)==[1,-1,Q(1,4)], 'c1 probability coefficients differ')
    need(ratio_coefficients(2,2)==[1,Q(-5,2)], 'c2 probability coefficients differ')
    return {'log_w':list(map(str,l1)), 'log_w2':list(map(str,l2)),
            'T3':list(map(str,t3)), 'probability_coefficients_checked':True}


def verify(full1000=False):
    ref=reference()
    bound=1000 if full1000 else 250
    counts=diagonal_counts(bound)
    need(counts==ref[:bound+1], 'capped sliding DP disagrees with b-file')
    enumerated, enum_partitions=direct_enumeration()
    p=partition_numbers(1000)
    need(enumerated==ref[:46], 'direct multiplicity enumeration disagrees')
    need(enum_partitions==p[:46], 'enumeration does not count every partition')
    subset, used=positive_subset_identity()
    need(subset==ref[:56] and used==333, 'positive subset-product identity disagrees')
    need(all(a<=b for a,b in zip(counts,p)), 'diagonal counts exceed all partitions')
    result={'schema':'report196-verification-v1','status':'PASS',
            'arithmetic':'arbitrary-precision Python int and Fraction',
            'dependencies':'Python standard library only','full1000_recomputed':full1000,
            'pinned_bfile':{'url':'https://oeis.org/A239964/b239964.txt',
                'sha256':REFERENCE_SHA256,'terms':1001,'minimum_n':0,'maximum_n':1000},
            'capped_sliding_dp':{'maximum_n':bound,'terms_matched':bound+1,
                'computed_terms_sha256':hashlib.sha256(terms_bytes(counts)).hexdigest(),
                'last_term':str(counts[-1])},
            'independent_multiplicity_enumeration':{'maximum_n':45,'terms_matched':46,
                'ordinary_partition_counts_matched':True,'partitions_visited':sum(enum_partitions)},
            'independent_positive_subset_product':{'maximum_n':55,'terms_matched':56,'subsets':used},
            'saddle_polynomial_checks':{'maximum_m':13,'coefficients':saddle_polynomials()},
            'low_order_algebra':low_order_algebra(),'fourth_and_forward_jets':symbolic_checks.run(),
            'p1000':str(p[1000]),
            'scope':'Finite exact checks support reproducibility; they do not replace the analytic proof.'}
    return result,counts


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--full1000',action='store_true')
    parser.add_argument('--output',type=Path,help='new JSON result file; existing paths are refused')
    parser.add_argument('--terms-output',type=Path,help='new exact computed-term file')
    args=parser.parse_args()
    for path in (args.output,args.terms_output):
        if path is not None: need(not path.exists() and not path.is_symlink(), 'output already exists: '+str(path))
    result,counts=verify(args.full1000)
    payload=canonical(result)
    if args.output:
        with args.output.open('xb') as stream: stream.write(payload)
    if args.terms_output:
        with args.terms_output.open('xb') as stream: stream.write(terms_bytes(counts))
    sys.stdout.buffer.write(payload)


if __name__=='__main__':
    try: main()
    except (OSError,ValueError) as error:
        print('verification failed: '+str(error),file=sys.stderr)
        raise SystemExit(2)
