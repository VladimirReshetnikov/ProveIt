"""Reproduce exact tests and finite Cayley--Hamilton certificates.

Run from any directory: python code/verify.py
The default output directory is the parent of this code directory.
No external dependencies are required; --symbolic additionally uses SymPy.
"""
from __future__ import annotations

import argparse
import csv
import json
import platform
from collections import Counter
from itertools import product
from pathlib import Path
from time import perf_counter

from kbonacci_residues import (
    build_machine, coefficient_for_canonical, counter_step, dfa_sequence,
    hole_counts, is_canonical, multiply_factor, normalize, odd_counts,
    parity_machine, rational_series, support_counts, value, weights,
)


def check(condition: bool, message: str) -> None:
    """Do not rely on assert: these checks still execute under python -O."""
    if not condition:
        raise AssertionError(message)


def decode_canonical_pair(top: tuple[int, ...], bottom: tuple[int, ...],
                          k: int) -> list[tuple[int, int]]:
    """Independently parse the disjoint blocks in the fiber factorization.

    Return half-open intervals occupied by non-diagonal blocks. Check every
    symbol, including equal separator columns, rather than calling the counter.
    """
    n, pos, blocks = len(top), 0, []
    while pos < n:
        if top[pos] == bottom[pos]:
            pos += 1
            continue
        start = pos
        check(top[pos:pos+k] == (0,)*k, 'bad top opening')
        check(bottom[pos:pos+k] == (1,)*k, 'bad bottom opening')
        pos += k
        while True:
            check(pos < n, 'unterminated excursion')
            if top[pos] != bottom[pos]:
                check((top[pos], bottom[pos]) == (1, 0), 'bad closure')
                pos += 1
                blocks.append((start, pos))
                break
            check(top[pos+1:pos+k] == (0,)*(k-1), 'bad top continuation')
            check(bottom[pos+1:pos+k] == (1,)*(k-1), 'bad bottom continuation')
            pos += k
    return blocks


def parity_label(vector: tuple[int, ...], run: int, k: int) -> str:
    """Map every reachable generic mod-2 state to its uniform DFA quotient."""
    p, *b = vector
    if not any(vector):
        return 'X'
    if p == 1 and not any(b):
        return 'A0' if run == 0 else f'C{run}'
    if p == 1 and b == [1] + [0]*(k-1) and run == 1:
        return 'F'
    if p == 1 and run == 0:
        for j in range(1, k+1):
            if b == [1]*j + [0]*(k-j):
                return f'A{j}'
        for j in range(2, k+1):
            if b == [0]*(j-1) + [1]*(k-j+1):
                return f'B{j}'
    if p == 0:
        for j in range(1, k+1):
            if b == [0]*(j-1) + [1] + [0]*(k-j):
                if j == 1 and run in (0, 1):
                    return 'D'
                if j >= 2 and run == 0:
                    return f'E{j}'
    raise AssertionError(f'unclassified state {(vector, run, k)}')


def certificate(k: int, numerator: list[int], denominator: list[int],
                output: Path) -> dict:
    """Finite all-n certificate using the dimension of a known linear model."""
    machine = build_machine(k, modulus=3)
    dimension = len(machine.states)
    degree = len(denominator)-1
    check(len(numerator) <= degree, 'certificate assumes numerator degree < d')
    sequence = [r[1] for r in machine.distributions(dimension + degree - 1)]
    convolution = [sum(denominator[j]*sequence[n-j]
                       for j in range(min(n, degree)+1))
                   for n in range(len(sequence))]
    check(convolution[:degree] == numerator + [0]*(degree-len(numerator)),
          f'initial numerator mismatch k={k}')
    check(not any(convolution[degree:]), f'nonzero recurrence residual k={k}')
    data = machine.certificate_dict()
    data.update({
        'target_residue': 1, 'matrix_dimension': dimension,
        'numerator_ascending': numerator, 'denominator_ascending': denominator,
        'sequence_prefix': sequence,
        'initial_numerator_coefficients_checked': degree,
        'consecutive_zero_residuals_checked': dimension,
        'residuals': convolution[degree:],
        'proof': 'The residual sequence has a linear representation of dimension N. '
                 'N initial zero residuals imply all residuals vanish by Cayley-Hamilton.',
        'passed': True,
    })
    output.write_text(json.dumps(data, indent=2) + '\n')
    return {'k': k, 'matrix_dimension': dimension, 'denominator_degree': degree,
            'residuals_checked': dimension, 'passed': True}


def verify(output: Path, symbolic: bool = False) -> dict:
    start = perf_counter()
    for folder in ('data', 'certificates'):
        (output/folder).mkdir(parents=True, exist_ok=True)
    summary = {'python': platform.python_version(), 'integer_arithmetic': True,
               'tests': {}}
    tests = summary['tests']

    # Dense polynomial expansion is independent of the finite-state derivation.
    rows, comparisons, residue_entries, direct = [], 0, 0, {}
    for k in range(2, 9):
        n_max = 16
        machines = {m: build_machine(k, modulus=m).distributions(n_max)
                    for m in (2, 3, 4, 5)}
        support, holes = support_counts(k, n_max), hole_counts(k, n_max)
        coefficients = [1]
        ws = weights(k, n_max)
        for n in range(n_max+1):
            frequency = Counter(coefficients)
            direct[k, n] = frequency
            check(sum(coefficients) == 2**n, 'total coefficient mass')
            check(len(coefficients)-frequency[0] == support[n], 'support count')
            check(frequency[0] == holes[n], 'hole count')
            for m, machine_rows in machines.items():
                counts = [0]*m
                for c, multiplicity in frequency.items():
                    counts[c % m] += multiplicity
                expected = machine_rows[n].copy()
                expected[0] += holes[n]
                check(counts == expected, f'residue mismatch {(k,n,m)}')
                comparisons += 1
                for a, count in enumerate(counts):
                    rows.append([k,n,m,a,count,len(coefficients)-1,support[n],holes[n]])
                    residue_entries += 1
            if n < n_max:
                coefficients = multiply_factor(coefficients, ws[n])
    with (output/'data/coefficient_counts.csv').open('w', newline='') as stream:
        writer = csv.writer(stream)
        writer.writerow(['k','n','modulus','residue','count_including_holes',
                         'degree','support_size','holes'])
        writer.writerows(rows)
    tests['direct_expansion'] = {'k_min':2,'k_max':8,'n_min':0,'n_max':16,
        'moduli':[2,3,4,5], 'parameter_comparisons':comparisons,
        'individual_residue_counts':residue_entries,
        'largest_degree':sum(weights(8,16)), 'passed':True}
    print('Dense polynomial comparisons passed', flush=True)

    # Exhaust all words; test both complete fibers and the block parser.
    word_checks, fiber_checks, block_checks = 0, 0, 0
    for k in range(2, 9):
        for n in range(12):
            fibers: dict[int, list[tuple[int, ...]]] = {}
            for word in product((0,1), repeat=n):
                v = value(word, k)
                canonical = normalize(word, k)
                check(is_canonical(canonical,k), 'normal form forbidden pattern')
                check(value(canonical,k) == v, 'normalization changes value')
                blocks = decode_canonical_pair(canonical, word, k)
                for lo, hi in blocks:
                    # Compare using the actual positional weights, not a shift-
                    # invariant assumption about the exceptional initial weights.
                    ws = weights(k,n)
                    check(sum((canonical[i]-word[i])*ws[i]
                              for i in range(lo,hi)) == 0, 'block changes value')
                block_checks += 1
                fibers.setdefault(v, []).append(word)
                word_checks += 1
            for v, fiber in fibers.items():
                forms = {normalize(word,k) for word in fiber}
                check(len(forms) == 1, 'nonunique normal form')
                canonical = next(iter(forms))
                check(coefficient_for_canonical(canonical,k) == len(fiber),
                      f'fiber counter mismatch {(k,n,v)}')
                fiber_checks += 1
    tests['exhaustive_words'] = {'k_min':2,'k_max':8,'n_min':0,'n_max':11,
        'words_checked':word_checks,'fibers_checked':fiber_checks,
        'pair_factorizations_checked':block_checks,'passed':True}
    print('Exhaustive normal forms and fiber factorizations passed', flush=True)

    capped = 0
    for k in range(2,6):
        for q in range(1,5):
            distributions = build_machine(k,cap=q+1).distributions(12)
            for n, row in enumerate(distributions):
                check(row[q] == direct[k,n][q], f'capped mismatch {(k,q,n)}')
                capped += 1
    tests['exact_multiplicity'] = {'k_min':2,'k_max':5,'q_min':1,'q_max':4,
        'n_min':0,'n_max':12,'comparisons':capped,'passed':True}

    parity_comparisons, transition_checks = 0, 0
    for k in range(2,26):
        names, edges, accepting = parity_machine(k)
        check(len(names) == 4*k+2, 'parity state count')
        sequence = dfa_sequence(edges, accepting, 250)
        check(sequence == odd_counts(k,250), 'parity rational formula')
        parity_comparisons += 251
        general = build_machine(k,modulus=2)
        labels = [parity_label(v,r,k) for v,r in general.states]
        label_index = {s:i for i,s in enumerate(names)}
        for i, (v,r) in enumerate(general.states):
            label = labels[i]
            check(accepting[label_index[label]] == (v[0] == 1), 'parity acceptance')
            for bit in (0,1):
                target = general.edges[i][bit]
                actual = 'X' if target < 0 else labels[target]
                expected = names[edges[label_index[label]][bit]]
                check(actual == expected, f'quotient transition {(k,i,bit)}')
                transition_checks += 1
        if k <= 8:
            (output/f'certificates/parity_k{k}.json').write_text(json.dumps({
                'k':k,'states':names,'edges_by_input_0_1':edges,
                'accepting':accepting,'initial_state':0},indent=2)+'\n')
    tests['uniform_parity'] = {'k_min':2,'k_max':25,'n_min':0,'n_max':250,
        'sequence_terms_checked':parity_comparisons,
        'quotient_transitions_checked':transition_checks,'passed':True}
    print('Uniform parity machines and capped counters passed', flush=True)

    tests['mod3_certificates'] = [
        certificate(2,[1,-2,4,-6,8,-10,8,-6],
                    [1,-4,8,-12,16,-20,19,-12,4],
                    output/'certificates/mod3_k2.json'),
        certificate(3,[1,-2,0,4,-6,0,8,-10,0,8,-6],
                    [1,-4,4,4,-12,8,8,-20,11,8,-12,4],
                    output/'certificates/mod3_k3.json'),
    ]
    state_rows = [[k]+[len(build_machine(k,modulus=m).states) for m in (2,3,4,5)]
                  for k in range(2,9)]
    with (output/'data/state_counts.csv').open('w',newline='') as stream:
        writer=csv.writer(stream)
        writer.writerow(['k','m2','m3','m4','m5'])
        writer.writerows(state_rows)
    with (output/'data/odd_counts.csv').open('w',newline='') as stream:
        writer=csv.writer(stream)
        writer.writerow(['k','n','odd_coefficients'])
        for k in range(2,9):
            writer.writerows((k,n,a) for n,a in enumerate(odd_counts(k,100)))

    if symbolic:
        import sympy as sp
        z,u=sp.symbols('z u')
        H=(1+2*u)/(1-2*z+2*u-2*z*u)
        A1=((1-z)*H-1)/(z*(1-u))
        C1=(1+(z-u)*A1)/(1-z)
        C2=(1+(z-u/z)*A1)/(1-z)
        F=A1+z*(C2-C1)
        D=u*F/(1-u)
        expressions=[F-(1-u)*A1, D-u*A1,
                     H-(1+z*A1+z*C1),
                     (1+u)*(1-z)*H-(1+u+z*C1+z*u*D)]
        check(all(sp.cancel(expr)==0 for expr in expressions), 'symbolic elimination')
        tests['symbolic_elimination']={'sympy':sp.__version__,'identities':4,'passed':True}
    else:
        tests['symbolic_elimination']={'performed':False,'reason':'use --symbolic'}
    summary['elapsed_seconds']=round(perf_counter()-start,3)
    summary['all_passed']=True
    (output/'data/verification_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))
    return summary


if __name__ == '__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,
                        default=Path(__file__).resolve().parent.parent)
    parser.add_argument('--symbolic',action='store_true')
    args=parser.parse_args()
    verify(args.output,args.symbolic)
