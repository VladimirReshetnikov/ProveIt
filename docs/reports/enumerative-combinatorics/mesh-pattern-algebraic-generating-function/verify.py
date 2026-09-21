#!/usr/bin/env python3
"""Exact and exhaustive checks for the proof of OEIS A289587.
Python 3.9+; standard library only. Run without Python's -O switch.
Finite checks support, but do not replace, the mathematical proof.
"""
from __future__ import annotations
import argparse
import csv
import json
import platform
from collections import Counter
from itertools import permutations, product
from math import comb
from pathlib import Path
from time import perf_counter
from typing import Dict, Iterator, List, Sequence, Tuple

Permutation = Tuple[int, ...]
OEIS_TERMS = [1,1,1,3,6,18,47,139,405,1225,3740,11602,36357,115049,366969,1178791,3809802]
MESH_174 = frozenset({(0,1),(0,2),(1,0),(1,2),(2,1)})
MESH_234 = frozenset({(0,1),(1,0),(1,2),(2,0),(2,1)})


def avoids_321(p: Permutation) -> bool:
    """middle is the largest middle of any previously encountered descent."""
    largest = middle = 0
    for value in p:
        if value < middle:
            return False
        if value < largest:
            middle = max(middle, value)
        largest = max(largest, value)
    return True


def mesh_occurrences(p: Permutation, shading: frozenset) -> List[Tuple[int,int]]:
    """Direct geometric definition, independent of the structural lemma.
    The returned position pairs are zero-based.
    """
    result = []
    for i, a in enumerate(p):
        for j in range(i+1, len(p)):
            b = p[j]
            if a >= b:
                continue
            for k, value in enumerate(p):
                if k == i or k == j:
                    continue
                cell = ((k>i)+(k>j), (value>a)+(value>b))
                if cell in shading:
                    break
            else:
                result.append((i,j))
    return result


def record_positions(p: Permutation) -> List[int]:
    result, largest = [], 0
    for i, value in enumerate(p):
        if value > largest:
            result.append(i)
            largest = value
    return result


def upper_bonds(p: Permutation) -> List[int]:
    return [i for i in record_positions(p)
            if i+1 < len(p) and p[i+1] == p[i]+1]


def components(p: Permutation) -> List[Permutation]:
    """Return the unique standardized direct-sum-indecomposable factors."""
    result, start, largest = [], 0, 0
    for end, value in enumerate(p, 1):
        largest = max(largest, value)
        if largest == end:
            result.append(tuple(v-start for v in p[start:end]))
            start = end
    return result


def inverse(p: Permutation) -> Permutation:
    result = [0]*len(p)
    for position, value in enumerate(p, 1):
        result[value-1] = position
    return tuple(result)


def av321(n: int) -> Iterator[Permutation]:
    """Insert the new maximum precisely before increasing suffixes."""
    if n == 0:
        yield ()
        return
    for p in av321(n-1):
        first_slot = 0
        for i in range(len(p)-1):
            if p[i] > p[i+1]:
                first_slot = i+1
        for i in range(first_slot,n):
            yield p[:i]+(n,)+p[i:]


def contract(p: Permutation) -> Tuple[Permutation,Tuple[int,...]]:
    """Contract maximal upper-bond runs and retain all other points."""
    bonds = set(upper_bonds(p))
    representatives, lengths = [], []
    i = 0
    while i < len(p):
        j = i
        while j in bonds:
            j += 1
        representatives.append(p[i])
        lengths.append(j-i+1)
        i = j+1
    rank = {v:i for i,v in enumerate(sorted(representatives),1)}
    return tuple(rank[v] for v in representatives), tuple(lengths)


def inflate(core: Permutation, lengths: Sequence[int]) -> Permutation:
    if len(core) != len(lengths) or any(length<1 for length in lengths):
        raise ValueError('One positive length is required for every core entry.')
    starts: Dict[int,int] = {}
    current = 1
    for value,length in sorted(zip(core,lengths)):
        starts[value] = current
        current += length
    return tuple(v for value,length in zip(core,lengths)
                 for v in range(starts[value],starts[value]+length))


def to_dyck(p: Permutation) -> Tuple[int,...]:
    positions = record_positions(p)
    values = [p[i] for i in positions]
    path: List[int] = []
    previous_value = 0
    for position,following,value in zip(positions,positions[1:]+[len(p)],values):
        path.extend([1]*(value-previous_value))
        path.extend([-1]*(following-position))
        previous_value = value
    return tuple(path)


def from_dyck(path: Tuple[int,...]) -> Permutation:
    if not path:
        return ()
    n = len(path)//2
    records: Dict[int,int] = {}
    i = up_total = down_total = 0
    while i < len(path):
        while i < len(path) and path[i] == 1:
            up_total += 1
            i += 1
        records[down_total] = up_total
        while i < len(path) and path[i] == -1:
            down_total += 1
            i += 1
    remaining = iter(sorted(set(range(1,n+1))-set(records.values())))
    return tuple(records[i] if i in records else next(remaining) for i in range(n))


def narayana(n: int,k: int) -> int:
    return comb(n,k)*comb(n,k-1)//n if n>=1 and 1<=k<=n else 0


def refined_core(n: int,k: int) -> int:
    return sum((-1)**d*comb(k-1,d)*narayana(n-d-1,k-d)
               for d in range(k)) if n>=2 and k>=1 else 0


def exact_div(numerator: int,denominator: int) -> int:
    quotient,remainder = divmod(numerator,denominator)
    if remainder:
        raise ArithmeticError('The theoretically exact division was inexact.')
    return quotient


def fast_coefficients(N: int) -> List[int]:
    """O(N) integer arithmetic operations; return a(0),...,a(N)."""
    if N < 0:
        raise ValueError('N must be nonnegative.')
    d,p = [1,-2,-5,-2,1],[3,10,11,4,1]
    t = [0]*(N+2)
    t[0] = 1
    for n in range(1,N+2):
        numerator = sum((3*k-2*n)*d[k]*t[n-k] for k in range(1,min(4,n)+1))
        t[n] = exact_div(numerator,2*n)
    a = [0]*(N+1)
    for n in range(N+1):
        numerator = (p[n+1] if n+1<len(p) else 0)-3*t[n+1]-5*t[n]
        numerator -= t[n-1] if n else 0
        a[n] = exact_div(numerator,8)
        if n>=1:
            a[n] -= 2*a[n-1]
        if n>=2:
            a[n] -= a[n-2]
    return a


def positive_coefficients(N: int) -> Tuple[List[int],List[int]]:
    """Independent O(N^2) recurrences using only nonnegative integers."""
    r,s,a = [0]*(N+1),[0]*(N+1),[0]*(N+1)
    s[0] = a[0] = 1
    for n in range(1,N+1):
        r[n] = int(n==2)+r[n-1]+(r[n-2] if n>=2 else 0)
        r[n] += sum(r[i]*r[n-i] for i in range(2,n-1))
        r[n] += sum(r[i]*r[n-1-i] for i in range(2,n-2))
        s[n] = sum(r[i]*s[n-i] for i in range(2,n+1))
        a[n] = s[n]+sum(s[i]*s[n-1-i] for i in range(n))
    return r,a


def refined_class_counts(N: int) -> List[Counter]:
    """Expand 1/(1-uR)+vxy/(1-uR)^2; keys (records,nontrivial,singletons)."""
    sequences = [Counter() for _ in range(N+1)]
    sequences[0][(0,0)] = 1
    for n in range(1,N+1):
        for length in range(2,n+1):
            for k in range(1,length):
                weight = refined_core(length,k)
                if weight:
                    for (records,count),multiplicity in sequences[n-length].items():
                        sequences[n][(records+k,count+1)] += weight*multiplicity
    result = [Counter() for _ in range(N+1)]
    for n in range(N+1):
        for (k,m),multiplicity in sequences[n].items():
            result[n][(k,m,0)] += multiplicity
        if n:
            for (k,m),multiplicity in sequences[n-1].items():
                result[n][(k+1,m,1)] += (m+1)*multiplicity
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-n',type=int,default=1000)
    parser.add_argument('--exhaustive',type=int,default=11)
    parser.add_argument('--outdir',type=Path,default=Path('data'))
    args = parser.parse_args()
    if not __debug__:
        parser.error('Do not use -O: this checker uses assertions.')
    if not 0 <= args.exhaustive <= args.max_n or args.exhaustive>14:
        parser.error('Require 0 <= exhaustive <= min(max-n,14).')
    args.outdir.mkdir(parents=True,exist_ok=True)
    start = perf_counter()
    a = fast_coefficients(args.max_n)
    r,other_a = positive_coefficients(args.max_n)
    assert a == other_a
    length = min(len(a),len(OEIS_TERMS))
    assert a[:length] == OEIS_TERMS[:length]
    print(f'Exact algorithms agree at indices 0..{args.max_n}.',flush=True)
    raw_limit = min(8,args.exhaustive)
    for n in range(raw_limit+1):
        raw = {p for p in permutations(range(1,n+1)) if avoids_321(p)}
        generated = list(av321(n))
        assert len(generated) == len(set(generated))
        assert set(generated) == raw
    print(f'Generator matches all n! permutations through n={raw_limit}.',flush=True)
    refined_expected = refined_class_counts(args.exhaustive)
    rows = []
    round_trips = 0
    for n in range(args.exhaustive+1):
        counts,records,cores,refined_actual = Counter(),Counter(),Counter(),Counter()
        for p in av321(n):
            assert avoids_321(p)
            mesh174 = mesh_occurrences(p,MESH_174)
            mesh234 = mesh_occurrences(p,MESH_234)
            inv = inverse(p)
            if n <= 8:
                inverse174 = mesh_occurrences(inv,MESH_174)
                assert sorted((p[i]-1,p[j]-1) for i,j in mesh234) == sorted(inverse174)
            assert avoids_321(inv)
            bs,cs = upper_bonds(p),components(p)
            singleton_count = sum(len(q)==1 for q in cs)
            structural = not bs and singleton_count<=1
            assert (not mesh174) == structural, (p,mesh174,bs,cs)
            counts['catalan'] += 1
            counts['avoid174'] += int(not mesh174)
            counts['avoid234'] += int(not mesh234)
            k = len(record_positions(p))
            records[k] += 1
            path = to_dyck(p)
            height = 0
            for step in path:
                height += step
                assert height>=0
            assert height==0 and len(path)==2*n
            assert from_dyck(path)==p
            assert sum(path[i:i+2]==(1,-1) for i in range(len(path)-1))==k
            if structural:
                refined_actual[(k,len(cs)-singleton_count,singleton_count)] += 1
            if n>=2 and len(cs)==1:
                counts['indecomposable'] += 1
                core,lengths = contract(p)
                assert len(core)>=2 and len(components(core))==1
                assert avoids_321(core) and not upper_bonds(core)
                assert inflate(core,lengths)==p
                core_records = set(record_positions(core))
                assert all(length==1 or i in core_records for i,length in enumerate(lengths))
                assert k==sum(lengths[i] for i in core_records)
                round_trips += 1
                if not bs:
                    cores[k] += 1
                    counts['reduced_core'] += 1
        assert counts['catalan']==comb(2*n,n)//(n+1)
        assert counts['avoid174']==counts['avoid234']==a[n]
        assert sum(cores.values())==r[n]
        if n:
            assert all(records[k]==narayana(n,k) for k in range(1,n+1))
        for k in range(1,n):
            assert cores[k]==refined_core(n,k)
        assert refined_actual==refined_expected[n], (n,refined_actual,refined_expected[n])
        row = dict(n=n,catalan=counts['catalan'],avoid174=counts['avoid174'],
                   avoid234=counts['avoid234'],indecomposable=counts['indecomposable'],
                   reduced_core=counts['reduced_core'])
        rows.append(row)
        print(row,flush=True)
    inflation_tests = 0
    for n in range(2,min(5,args.exhaustive)+1):
        for core in av321(n):
            if len(components(core))!=1 or upper_bonds(core):
                continue
            rec = record_positions(core)
            for chosen in product(range(1,4),repeat=len(rec)):
                lengths = [1]*n
                for i,length in zip(rec,chosen):
                    lengths[i] = length
                p = inflate(core,lengths)
                assert avoids_321(p) and len(components(p))==1
                assert contract(p)==(core,tuple(lengths))
                inflation_tests += 1
    with (args.outdir/'coefficients.csv').open('w',newline='') as stream:
        writer = csv.writer(stream)
        writer.writerow(['n','a_n','reduced_core_r_n'])
        writer.writerows((n,a[n],r[n]) for n in range(args.max_n+1))
    with (args.outdir/'b289587_extended.txt').open('w') as stream:
        stream.write('# Computed from the proved formula; not an official OEIS b-file.\n')
        stream.writelines(f'{n} {value}\n' for n,value in enumerate(a))
    with (args.outdir/'exhaustive_counts.csv').open('w',newline='') as stream:
        writer = csv.DictWriter(stream,fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    report = {'status':'PASS','python':platform.python_version(),
        'exact_last_index':args.max_n,'exact_terms_compared':args.max_n+1,
        'exhaustive_last_length':args.exhaustive,
        'exhaustive_permutations':sum(row['catalan'] for row in rows),
        'raw_factorial_last_length':raw_limit,
        'pointwise_inverse_last_length':min(8,args.exhaustive),
        'indecomposable_contraction_round_trips':round_trips,
        'independent_inflation_tests':inflation_tests,
        'checks':['two exact coefficient recurrences','published OEIS terms',
                  'independent n! generator cross-check','geometric mesh predicates',
                  'pointwise inverse-pattern equivalence','structural mesh lemma',
                  'Narayana record distribution','Dyck bijection round trips',
                  'contraction/inflation round trips','refined core formula',
                  'four-variable class generating function'],
        'elapsed_seconds':round(perf_counter()-start,3),
        'note':'Finite checks support but do not replace the mathematical proof.'}
    (args.outdir/'verification_report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2),flush=True)


if __name__ == '__main__':
    main()
