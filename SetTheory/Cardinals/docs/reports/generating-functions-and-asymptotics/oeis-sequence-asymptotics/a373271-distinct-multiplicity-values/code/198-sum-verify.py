#!/usr/bin/env python3
"""Exact offline checks for Report198 (OEIS A373273).

Default: recompute n=0,...,2500 by Q-polynomials, independently count partitions
avoiding each multiplicity through 450, and enumerate Ferrers gaps through 43.
Every count is an arbitrary-precision integer. Finite Fraction identities
check coefficient algebra, not analytic remainder estimates or novelty.
The statistic is the SUM of distinct positive multiplicity values.
"""
from __future__ import annotations
import argparse
import hashlib
from pathlib import Path
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).absolute().parent
sys.path.insert(0, str(ROOT))
import build as builder
import symbolic_checks

REFERENCE_SHA256 = '0b6ba19a1ea9490ef1ca8e15c3e86bd07519f332f6a07a9bc25a2858f213f54d'
MAXIMUM_N = 2500
POSITIVE_DP_MAXIMUM_N = 450
FERRERS_MAXIMUM_N = 43
DISPLAYED_OEIS = (1,3,5,11,18,29,48,74,107,161,237,324,471,648,876,1199,1632,2141,2881,3754,4910,6389,8301,10570,13603,17280,21915,27614,34842,43416,54415,67509,83782,103459,127685,156457,192155,234540,286112,347571,422245,510311,617216)
OEIS_RECORD_SHA256 = "37a7ec9af3a7c099c22b4254c066792f9ebaf2fb92975335fe8444798c448103"


def need(condition, message):
    if not condition:
        raise ValueError(message)


def terms_bytes(counts, partitions):
    need(len(counts) == len(partitions), 'count arrays have different lengths')
    return ''.join('%d %d %d\n' % (n,a,p) for n,(a,p) in
                   enumerate(zip(counts,partitions))).encode('ascii')


def reference():
    data = builder.read_regular(ROOT/'data/exact_A373273.txt')
    need(hashlib.sha256(data).hexdigest() == REFERENCE_SHA256,
         'pinned exact-data digest differs')
    rows = [tuple(map(int,line.split())) for line in data.decode('ascii').splitlines()]
    need(len(rows) == MAXIMUM_N+1 and all(len(row) == 3 and row[0] == n and
         row[1] >= 0 and row[2] > 0 for n,row in enumerate(rows)),
         'exact-data structure differs')
    counts, partitions = [row[1] for row in rows], [row[2] for row in rows]
    need(rows[0] == (0,0,1), 'empty partition normalization differs')
    need(data == terms_bytes(counts,partitions), 'exact data is not canonical')
    need(tuple(counts[1:44]) == DISPLAYED_OEIS, '43 displayed OEIS terms differ')
    record = builder.read_regular(ROOT/'data/A373273.seq')
    need(hashlib.sha256(record).hexdigest() == OEIS_RECORD_SHA256,
         'pinned OEIS record digest differs')
    combined = ''.join(line.split(' ',2)[2] for line in record.decode('utf-8').splitlines()
                       if line.startswith(('%S','%T','%U')))
    need(tuple(map(int,combined.split(','))) == DISPLAYED_OEIS,
         '43 pinned official OEIS record terms differ')
    return counts,partitions


def partition_product(nmax):
    """Multiply all geometric part-size factors, truncated after q^nmax."""
    p = [1]+[0]*nmax
    for size in range(1,nmax+1):
        for n in range(size,nmax+1):
            p[n] += p[n-size]
    return p


def partition_pentagonal(nmax):
    """Euler's recurrence, independent of the product dynamic program."""
    p = [1]
    for n in range(1,nmax+1):
        value,k = 0,1
        while k*(3*k-1)//2 <= n:
            sign = 1 if k%2 else -1
            for exponent in (k*(3*k-1)//2,k*(3*k+1)//2):
                if exponent <= n:
                    value += sign*p[n-exponent]
            k += 1
        p.append(value)
    return p


def q_polynomial_counts(nmax,partitions):
    """Form Q_m=product_j(1-q^(mj)+q^((m+1)j)); sum m*(1-Q_m), then P.

    The descending coefficient update reads only coefficients from the previous
    product: both shifts are strictly positive. The mth complement begins at
    degree m, so m<=nmax and j<=nmax/m exhaust all possible contributions.
    Intermediate Q_m and summed-complement coefficients may be signed.
    """
    need(len(partitions) == nmax+1, 'partition table has wrong length')
    complement = [0]*(nmax+1)
    for m in range(1,nmax+1):
        polynomial = [1]+[0]*nmax
        for size in range(1,nmax//m+1):
            first,second = m*size,(m+1)*size
            for degree in range(nmax,first-1,-1):
                polynomial[degree] -= polynomial[degree-first] - (
                    polynomial[degree-second] if degree >= second else 0)
        need(polynomial[0] == 1 and not any(polynomial[1:m]),
             'Q_m minimum-degree invariant differs')
        for degree in range(m,nmax+1):
            complement[degree] -= m*polynomial[degree]
    counts = [sum(partitions[n-k]*complement[k] for k in range(1,n+1))
              for n in range(nmax+1)]
    need(all(value >= 0 for value in counts), 'negative weighted multiplicity total')
    return counts


def forbidden_multiplicity_counts(nmax,partitions):
    """Positive combinatorial DP: multiply (1/(1-q^j)-q^(mj)) directly.

    For each m and part size j, first allow any number of copies, then remove
    the old-row contribution having exactly m copies. The resulting row counts
    partitions with each processed multiplicity different from m, so every
    coefficient stays nonnegative. This never constructs Q_m, a signed sum of
    complements, or a final convolution with the partition generating function.
    """
    need(len(partitions) == nmax+1, 'independent partition table has wrong length')
    counts = [0]*(nmax+1)
    for m in range(1,nmax+1):
        row = [1]+[0]*nmax
        for size in range(1,nmax+1):
            old = row[:]
            for degree in range(size,nmax+1):
                row[degree] += row[degree-size]
            for degree in range(m*size,nmax+1):
                row[degree] -= old[degree-m*size]
            need(all(value >= 0 for value in row),
                 'negative allowed-multiplicity DP coefficient')
        need(all(a <= b for a,b in zip(row,partitions)),
             'forbidden-multiplicity counts exceed partition counts')
        for n in range(nmax+1):
            counts[n] += m*(partitions[n]-row[n])
    return counts


def ferrers_gap_counts(nmax):
    """Enumerate descending partitions and sum different positive gaps.

    Under conjugation, positive adjacent gaps (including last part minus zero)
    become positive multiplicity values. This is an independent combinatorial
    representation, with no multiplicity Counter and no product identities.
    Every generated partition is also counted independently against p(n).
    """
    def descending(remaining,cap):
        if remaining == 0:
            yield ()
            return
        for part in range(min(remaining,cap),0,-1):
            for tail in descending(remaining-part,part):
                yield (part,)+tail
    counts,partitions = [],[]
    for n in range(nmax+1):
        total,visited = 0,0
        for partition in descending(n,n):
            gaps = {partition[i]-(partition[i+1] if i+1<len(partition) else 0)
                    for i in range(len(partition))}
            total += sum(gaps-{0})
            visited += 1
        counts.append(total)
        partitions.append(visited)
    return counts,partitions


def verify():
    expected,expected_p = reference()
    p = partition_product(MAXIMUM_N)
    pentagonal = partition_pentagonal(MAXIMUM_N)
    need(p == expected_p == pentagonal, 'partition recurrences disagree')
    counts = q_polynomial_counts(MAXIMUM_N,p)
    need(counts == expected, 'Q-polynomial recomputation disagrees with pinned data')
    positive = forbidden_multiplicity_counts(POSITIVE_DP_MAXIMUM_N,
                                             pentagonal[:POSITIVE_DP_MAXIMUM_N+1])
    need(positive == counts[:POSITIVE_DP_MAXIMUM_N+1],
         'independent forbidden-multiplicity DP disagrees')
    enumerated,enumerated_p = ferrers_gap_counts(FERRERS_MAXIMUM_N)
    need(enumerated == counts[:FERRERS_MAXIMUM_N+1], 'Ferrers-gap counts disagree')
    need(enumerated_p == p[:FERRERS_MAXIMUM_N+1], 'Ferrers enumeration omitted partitions')
    need(counts[0] == 0 and all(p[n] <= counts[n] <= n*p[n]
                               for n in range(1,MAXIMUM_N+1)),
         'elementary weighted multiplicity bounds fail')
    output = terms_bytes(counts,p)
    need(hashlib.sha256(output).hexdigest() == REFERENCE_SHA256,
         'recomputed exact data digest differs')
    algebra = symbolic_checks.run()
    need(algebra.get('status') == 'PASS', 'symbolic-check status differs')
    result = {
        'schema':'report198-verification-v1','report':198,'sequence':'A373273',
        'status':'PASS','all2501_recomputed':True,
        'arithmetic':'arbitrary-precision Python int and Fraction',
        'dependencies':'Python standard library only',
        'pinned_exact_data':{
            'file':'data/exact_A373273.txt','columns':['n','a_n','p_n'],
            'minimum_n':0,'maximum_n':MAXIMUM_N,'terms':MAXIMUM_N+1,
            'sha256':REFERENCE_SHA256,
            'provenance':'Locally computed exact reference; not an OEIS b-file'},
        'oeis_displayed_terms':{'url':'https://oeis.org/A373273',
                               'record_file':'data/A373273.seq',
                               'record_sha256':OEIS_RECORD_SHA256,
                               'live_verification_claim':False,
                               'first_n':1,'last_n':43,'terms_matched':43},
        'q_polynomial_recomputation':{
            'maximum_n':MAXIMUM_N,'terms_matched':MAXIMUM_N+1,
            'computed_terms_sha256':hashlib.sha256(output).hexdigest(),
            'last_a_n':str(counts[-1]),'last_p_n':str(p[-1])},
        'independent_partition_pentagonal_recurrence':{
            'maximum_n':MAXIMUM_N,'terms_matched':MAXIMUM_N+1},
        'independent_positive_forbidden_multiplicity_dp':{
            'maximum_n':POSITIVE_DP_MAXIMUM_N,'terms_matched':POSITIVE_DP_MAXIMUM_N+1,
            'all_intermediate_counts_nonnegative':True,
            'computed_terms_sha256':hashlib.sha256(terms_bytes(positive,
                pentagonal[:POSITIVE_DP_MAXIMUM_N+1])).hexdigest()},
        'independent_ferrers_gap_enumeration':{
            'maximum_n':FERRERS_MAXIMUM_N,'terms_matched':FERRERS_MAXIMUM_N+1,
            'ordinary_partition_counts_matched':True,
            'partitions_visited':sum(enumerated_p)},
        'exact_coefficient_algebra':algebra,
        'scope':'Finite exact checks support reproducibility; they do not replace the analytic proof.'}
    return result,output


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,help='new deterministic JSON receipt outside package')
    parser.add_argument('--terms-output',type=Path,help='new exact-data file outside package')
    args = parser.parse_args()
    paths = [builder.fresh_output(path,ROOT) for path in (args.output,args.terms_output)
             if path is not None]
    need(len(set(paths)) == len(paths), 'output destinations coincide')
    result,computed = verify()
    payload = builder.canonical(result)
    if args.output is not None:
        builder.write_new(args.output,payload)
    if args.terms_output is not None:
        builder.write_new(args.terms_output,computed)
    sys.stdout.buffer.write(payload)


if __name__ == '__main__':
    try:
        main()
    except (OSError,ValueError) as error:
        print('verification failed: '+str(error),file=sys.stderr)
        raise SystemExit(2)
