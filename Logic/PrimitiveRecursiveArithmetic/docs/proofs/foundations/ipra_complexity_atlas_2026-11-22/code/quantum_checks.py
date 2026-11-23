#!/usr/bin/env python3
"""Independent exact finite checks for the X/Toffoli/H gate model.

Two independent evaluators are compared:
  * enumerate Hadamard choice paths and sum their signed integer counts;
  * update amplitude pairs a+b*sqrt(2), with a,b Python Fractions.
No external quantum or linear algebra package is used. These finite checks
are evidence about the constructions, not proofs of the general theorems.
"""
from __future__ import annotations

import itertools
import json
from fractions import Fraction

ZERO = (Fraction(0), Fraction(0))
ONE = (Fraction(1), Fraction(0))


def add(z,w): return z[0]+w[0], z[1]+w[1]
def sub(z,w): return z[0]-w[0], z[1]-w[1]
def invsqrt2(z): return z[1], z[0]/2

def square(z):
    a,b = z
    return a*a+2*b*b, 2*a*b


def classical_step(y, gate):
    if gate[0] == 'X':
        return y ^ (1 << gate[1])
    if gate[0] == 'T':
        _, a,b,c = gate
        assert len({a,b,c}) == 3
        return y ^ ((1 << c) if ((y >> a)&1 and (y >> b)&1) else 0)
    raise ValueError(gate)


def pair_simulation(qubits, initial, gates):
    amplitudes = [ZERO] * (1 << qubits)
    amplitudes[initial] = ONE
    for gate in gates:
        new = [ZERO] * (1 << qubits)
        if gate[0] == 'H':
            bit = 1 << gate[1]
            for y in range(1 << qubits):
                if not (y & bit):
                    a,b = amplitudes[y],amplitudes[y|bit]
                    new[y] = invsqrt2(add(a,b))
                    new[y|bit] = invsqrt2(sub(a,b))
        else:
            for y,z in enumerate(amplitudes):
                new[classical_step(y,gate)] = z
        amplitudes = new
    return amplitudes


def path_simulation(qubits, initial, gates):
    h = sum(g[0] == 'H' for g in gates)
    sums = [0] * (1 << qubits)
    paths = []
    for choices in range(1 << h):
        y, sign, j = initial,1,0
        for gate in gates:
            if gate[0] == 'H':
                wire = gate[1]
                before = (y >> wire) & 1
                after = (choices >> j) & 1
                if before and after:
                    sign = -sign
                y = (y & ~(1 << wire)) | (after << wire)
                j += 1
            else:
                y = classical_step(y,gate)
        sums[y] += sign
        paths.append((y,sign))
    return h,sums,paths


def exact_acceptance(amplitudes, output):
    total = ZERO
    for y,z in enumerate(amplitudes):
        if (y >> output) & 1:
            total = add(total,square(z))
    return total


def check_circuit(qubits, initial, gates, output):
    h,sums,paths = path_simulation(qubits,initial,gates)
    amplitudes = pair_simulation(qubits,initial,gates)
    if h % 2:
        expected = [(Fraction(0),Fraction(s,1 << ((h+1)//2))) for s in sums]
    else:
        expected = [(Fraction(s,1 << (h//2)),Fraction(0)) for s in sums]
    assert amplitudes == expected, (qubits,initial,gates,amplitudes,expected)
    norm = ZERO
    for z in amplitudes:
        norm = add(norm,square(z))
    assert norm == ONE
    assert sum(s*s for s in sums) == 1 << h
    A = sum(s*s for y,s in enumerate(sums) if (y >> output)&1)
    assert exact_acceptance(amplitudes,output) == (Fraction(A,1 << h),Fraction(0))
    return h,A,sums,paths


def pp_machine_counts(paths, h, output):
    """Enumerate both selector modes and every auxiliary-bit assignment."""
    assert h >= 2
    accepted = rejected = 0
    mode0_gap = 0
    for y,su in paths:
        for z,sv in paths:
            g = su*sv if y == z and (y >> output)&1 else 0
            for extra in (0,1):
                accept = (g == 1) or (g == 0 and extra == 0)
                accepted += accept
                rejected += not accept
                mode0_gap += 1 if accept else -1
    mode0_branches = accepted+rejected
    mode1_gap = 0
    threshold = (1 << (2*h)) - (1 << (h-1))
    for j in range(1 << (2*h+1)):
        accept = j < threshold
        accepted += accept
        rejected += not accept
        mode1_gap += 1 if accept else -1
    assert mode0_branches == 1 << (2*h+1)
    assert accepted+rejected == 1 << (2*h+2)
    assert mode1_gap == -(1 << h)
    return accepted,rejected,mode0_gap,mode1_gap


def gate_options(qubits):
    result = [('X',j) for j in range(qubits)] + [('H',j) for j in range(qubits)]
    for target in range(qubits):
        remaining = [j for j in range(qubits) if j != target]
        for a,b in itertools.combinations(remaining,2):
            result.append(('T',a,b,target))
    return result


def boolean_evaluate(width, assignment, gates):
    values = [(assignment >> i)&1 for i in range(width)]
    for gate in gates:
        if gate[0] == '0': value = 0
        elif gate[0] == '1': value = 1
        elif gate[0] == 'not': value = 1-values[gate[1]]
        elif gate[0] == 'and': value = values[gate[1]] & values[gate[2]]
        elif gate[0] == 'or': value = values[gate[1]] | values[gate[2]]
        else: raise ValueError(gate)
        values.append(value)
    return values[-1]


def reversible_compile(width, gates):
    """Reserve a separate constant-one control; handle duplicate inputs."""
    one = width
    next_wire = width+1
    logical = list(range(width))
    quantum = [('X',one)]
    def copy(source,target):
        assert len({one,source,target}) == 3
        quantum.append(('T',one,source,target))
    for gate in gates:
        target = next_wire
        next_wire += 1
        if gate[0] == '1': quantum.append(('X',target))
        elif gate[0] == '0': pass
        elif gate[0] == 'not':
            copy(logical[gate[1]],target)
            quantum.append(('X',target))
        else:
            a,b = logical[gate[1]],logical[gate[2]]
            if a == b:
                copy(a,target)
            elif gate[0] == 'and':
                quantum.append(('T',a,b,target))
            elif gate[0] == 'or':
                # OR(a,b) = a XOR b XOR (a AND b).
                copy(a,target)
                copy(b,target)
                quantum.append(('T',a,b,target))
            else: raise ValueError(gate)
        logical.append(target)
    return next_wire,tuple(quantum),logical[-1]


def main():
    checked = pp_checked = pad_checked = embedding_checked = 0
    gap_signs = set()
    h_values = set()
    pp_branches_enumerated = 0
    # Exhaustive ordered circuits over the stated finite gate choices.
    for q,max_length in ((1,5),(2,4),(3,3)):
        options = gate_options(q)
        for length in range(max_length+1):
            for gates in itertools.product(options,repeat=length):
                for initial in range(1 << q):
                    h,A,sums,paths = check_circuit(q,initial,gates,0)
                    checked += 1
                    h_values.add(h)
                    # Independently verify fresh-wire HH padding and enumerate
                    # the PP machine on a deterministic selection of circuits.
                    if checked % 17 == 0 or (length == 0 and initial == 0):
                        padded = gates+(('H',q),('H',q))
                        hp,Ap,sp,ppaths = check_circuit(q+1,initial,padded,0)
                        assert hp == h+2 and Ap == 4*A
                        assert sp[:1 << q] == [2*s for s in sums]
                        assert sp[1 << q:] == [0]*(1 << q)
                        pad_checked += 1
                        acc,rej,gap0,gap1 = pp_machine_counts(ppaths,hp,0)
                        assert gap0 == 2*Ap
                        assert acc-rej == 2*Ap-(1 << hp)
                        assert (acc > rej) == (2*Ap > 1 << hp)
                        gap_signs.add((acc > rej)-(acc < rej))
                        pp_branches_enumerated += acc+rej
                        pp_checked += 1
    # Exact classical randomized embedding, including repeated-input gates and
    # both possible fixed classical input bits, with 0–3 random bits.
    for random_bits in range(4):
        width = random_bits+1
        b = min(1,width-1)
        templates = [
            (('0',),), (('1',),), (('not',0),),
            (('and',0,0),), (('or',0,0),),
            (('and',0,b),), (('or',0,b),),
            (('and',0,b),('not',width)),
            (('not',0),('or',width,b)),
            (('1',),('and',width,b)),
        ]
        for classical_gates in templates:
            qubits,rev,output = reversible_compile(width,classical_gates)
            for fixed_input in (0,1):
                gates = tuple(('H',i+1) for i in range(random_bits))+rev
                h,A,sums,paths = check_circuit(qubits,fixed_input,gates,output)
                expected = sum(boolean_evaluate(width,fixed_input|(seed << 1),classical_gates)
                               for seed in range(1 << random_bits))
                assert h == random_bits and A == expected
                assert len({y for y,sign in paths}) == 1 << random_bits
                assert all(sign == 1 for y,sign in paths)
                embedding_checked += 1
    assert gap_signs == {-1,0,1}
    assert 0 in h_values
    print(json.dumps({
        'status':'passed',
        'exhaustive_small_circuit_initial_state_checks':checked,
        'exact_amplitude_model':'rational pairs a+b*sqrt(2), independently updated',
        'hadamard_counts_covered':sorted(h_values),
        'fresh_wire_double_H_checks':pad_checked,
        'PP_gap_cases_with_all_branches_enumerated':pp_checked,
        'PP_total_branches_enumerated':pp_branches_enumerated,
        'PP_gap_signs_covered':sorted(gap_signs),
        'classical_randomized_embedding_checks':embedding_checked,
        'duplicate_Boolean_gate_inputs':'included and compiled to copy gates',
        'limits':'Finite implementation checks; no general theorem or object-iPRA derivation is machine-verified here.'
    },indent=2))


if __name__ == '__main__':
    main()
