#!/usr/bin/env python3
"""Finite validation for R01--R23; this is not an iPRA proof certificate.

Only Python's standard library is used. Independent exhaustive small-instance
checks exercise exact counts, witness constructors, and lower-bound identities.
The large asymptotic parameters are checked as integer inequalities, never by
allocating enormous truth tables.
"""
from itertools import product, permutations
from math import comb, factorial
import unittest


def majority_error_upper(q, bad, runs):
    """Number of tuples having at least half their trials bad (ties included)."""
    return sum(comb(runs, j) * bad**j * (q-bad)**(runs-j)
               for j in range((runs+1)//2, runs+1))


def xor_translate(mask, shift, q):
    return sum(1 << (u ^ shift) for u in range(q) if mask >> u & 1)


def covering_tuple(mask, q, k):
    """Least radix tuple covering the q-point XOR group, or None."""
    full = (1 << q)-1
    shifts = [xor_translate(mask, s, q) for s in range(q)]
    for tup in product(range(q), repeat=k):
        union = 0
        for s in tup:
            union |= shifts[s]
        if union == full:
            return tup
    return None


def circuit_value(n, gates, output, x):
    values = [(x >> i) & 1 for i in range(n)] + [0, 1]
    for table, left, right in gates:
        assert 0 <= table < 16
        assert 0 <= left < len(values) and 0 <= right < len(values)
        values.append((table >> (2*values[left]+values[right])) & 1)
    assert 0 <= output < len(values)
    return values[output]


def circuit_truth(n, gates, output):
    return sum(circuit_value(n, gates, output, x) << x
               for x in range(1 << n))


def small_circuit_tables(n, s):
    """Exact enumeration; intended only for s <= 1."""
    assert s in (0, 1)
    possible = [()]
    if s:
        possible += [((t, l, r),) for t in range(16)
                     for l in range(n+2) for r in range(n+2)]
    return {circuit_truth(n, gates, out) for gates in possible
            for out in range(n+2+len(gates))}


def dnf_compile(n, table):
    """Truth table -> finite AND/OR/NOT circuit, with constants as input wires."""
    assert 0 <= table < (1 << (1 << n))
    gates = []
    def add(truth, left, right):
        gates.append((truth, left, right))
        return n+2+len(gates)-1
    not_inputs = [add(3, i, n) for i in range(n)]  # table 3 is NOT-left
    terms = []
    for x in range(1 << n):
        if not (table >> x & 1):
            continue
        literals = [i if x >> i & 1 else not_inputs[i] for i in range(n)]
        if not literals:
            term = n+1
        else:
            term = literals[0]
            for lit in literals[1:]:
                term = add(8, term, lit)  # AND
        terms.append(term)
    out = n if not terms else terms[0]
    for term in terms[1:]:
        out = add(14, out, term)  # OR
    return gates, out


def query_trees(n, depth):
    """All binary bit-query trees up to a small depth; tuples encode nodes."""
    trees = [0, 1]
    if depth:
        children = query_trees(n, depth-1)
        trees += [(i, left, right) for i in range(n)
                  for left in children for right in children]
    return trees


def query_run(tree, x):
    seen = set()
    while isinstance(tree, tuple):
        i, left, right = tree
        seen.add(i)
        tree = right if x >> i & 1 else left
    return tree, seen


def insertion_sort_trace(keys):
    """Independent comparison algorithm; record only answer bits."""
    indices, trace = [], []
    for i in range(len(keys)):
        position = len(indices)
        while position:
            greater = keys[indices[position-1]] > keys[i]
            trace.append(greater)
            if not greater:
                break
            position -= 1
        indices.insert(position, i)
    assert [keys[i] for i in indices] == sorted(keys)
    return tuple(trace)


class FiniteChecks(unittest.TestCase):
    def test_integer_majority_amplification(self):
        for q in (1, 2, 4, 8, 16, 32):
            for bad in range(q//3+1):
                for d in range(1, 6):
                    runs = 12*d
                    error = majority_error_upper(q, bad, runs)
                    self.assertLess((1 << d)*error, q**runs)
                    weighted = sum(comb(runs, j)*bad**j*(q-bad)**(runs-j)
                                   * (1 << j) for j in range(runs+1))
                    self.assertEqual(weighted, (q+bad)**runs)

    def test_translate_cover_and_noncover(self):
        for m in range(4):
            q, k = 1 << m, m+1
            full = (1 << q)-1
            for mask in range(1 << q):
                count = mask.bit_count()
                if 2*(q-count) < q:
                    witness = covering_tuple(mask, q, k)
                    self.assertIsNotNone(witness)
                    union = 0
                    for shift in witness:
                        union |= xor_translate(mask, shift, q)
                    self.assertEqual(union, full)
                if k*count < q:
                    self.assertIsNone(covering_tuple(mask, q, k))

    def test_union_bound_supplies_least_good_seed(self):
        q = 4
        for sets in product(range(1 << q), repeat=3):
            if sum(s.bit_count() for s in sets) < q:
                union = sets[0] | sets[1] | sets[2]
                good = [u for u in range(q) if not (union >> u & 1)]
                self.assertTrue(good)
                self.assertTrue(all(not (s >> min(good) & 1) for s in sets))

    def test_pp_integer_constructions(self):
        for q in (1, 2, 4, 8, 16):
            for count in range(q+1):
                self.assertEqual(q+count > q, count > 0)
                if q >= 2:
                    h = q//2
                    complement_count = q-count+h+1
                    self.assertTrue(0 <= complement_count <= 2*q)
                    self.assertEqual(complement_count > q, 2*count <= q)

    def test_counting_sum_product_and_zero_padding(self):
        q_left, q_right = 2, 4
        for left in range(1 << q_left):
            for right in range(1 << q_right):
                # Left's extra padding bit is required to be zero.
                additive = sum(((left >> w) & 1) if tag == 0 and w < q_left
                               else (((right >> w) & 1) if tag else 0)
                               for tag in (0, 1) for w in range(q_right))
                multiplicative = sum(((left >> u) & 1)*((right >> v) & 1)
                                     for u in range(q_left)
                                     for v in range(q_right))
                self.assertEqual(additive, left.bit_count()+right.bit_count())
                self.assertEqual(multiplicative, left.bit_count()*right.bit_count())

    def test_finite_restart_expectation(self):
        for q in (1, 2, 4, 8):
            for bad in range(q//2+1):
                for cap in range(1, 9):
                    total_rounds = sum(bad**i*q**(cap-i) for i in range(cap))
                    self.assertLessEqual(total_rounds, 2*q**cap)
                    self.assertLessEqual((1 << cap)*bad**cap, q**cap)
                    # An independent explicit enumeration for smaller cases.
                    if q**cap <= 4096:
                        empirical = 0
                        for tape in product(range(q), repeat=cap):
                            used = 0
                            for block in tape:
                                used += 1
                                if block >= bad:
                                    break
                            empirical += used
                        self.assertEqual(empirical, total_rounds)

    def test_small_circuits_and_missing_tables(self):
        for n in (1, 2, 3):
            for s in (0, 1):
                tables = small_circuit_tables(n, s)
                bound = (n+s+2)*(16*(n+s+2)**2)**s
                self.assertLessEqual(len(tables), bound)
                if len(tables) < 1 << (1 << n):
                    hard = next(h for h in range(1 << (1 << n)) if h not in tables)
                    self.assertNotIn(hard, tables)
        self.assertEqual(len(small_circuit_tables(2, 1)), 16)

    def test_dnf_compiler(self):
        for n in range(4):
            for table in range(1 << (1 << n)):
                gates, output = dnf_compile(n, table)
                self.assertEqual(circuit_truth(n, gates, output), table)
                if n:
                    self.assertLessEqual(len(gates), n*(1 << n)+n)

    def test_large_parameter_inequalities_without_huge_allocations(self):
        for n in range(4, 257):
            s = (1 << n)//(16*(n+1))
            self.assertLessEqual(n+s+2, 1 << n)
            self.assertLessEqual(n+(4+2*n)*s, 1 << (n-1))
        for n in range(64, 257):
            m = n.bit_length()-2
            self.assertTrue(n < 4*(1 << m))
            self.assertLessEqual(2*(1 << m), n)
            self.assertLessEqual(n**3, 1 << (n//2))
            upper = n*n*(1 << (n//2))+n+4*(1 << (n-m))
            self.assertLessEqual(n*upper, 18*(1 << n))
        for r in range(101):
            d = 16*(r+1)**2
            m = 12*d*r
            self.assertLess(m+1, 1 << d)
        for c in range(1, 21):
            for k in range(21):
                t = 4*(k+c+4)
                self.assertLess(4+c+(k+1)*(t+1), 1 << t)

    def test_comparison_sorting_leaf_counts(self):
        for n in range(1, 8):
            traces = [insertion_sort_trace(p) for p in permutations(range(n))]
            self.assertEqual(len(set(traces)), factorial(n))
            self.assertGreaterEqual(1 << max(map(len, traces)), factorial(n))
            total_depth = sum(map(len, traces))
            for j in range(1, factorial(n).bit_length()):
                if 2*(1 << j) <= factorial(n):
                    self.assertGreaterEqual(2*total_depth, j*factorial(n))

    def test_query_adversaries_and_parity_pairing(self):
        for n in (1, 2, 3):
            trees = query_trees(n, n-1)
            for tree in trees:
                output0, seen0 = query_run(tree, 0)
                missing = next(i for i in range(n) if i not in seen0)
                self.assertEqual(query_run(tree, 1 << missing)[0], output0)
                parity_successes = sum(query_run(tree, x)[0] == x.bit_count()%2
                                       for x in range(1 << n))
                self.assertEqual(2*parity_successes, 1 << n)
            # Regard the entire set of trees as a finite seed family.
            error0 = sum(query_run(t, 0)[0] != 0 for t in trees)
            for i in range(n):
                seen = sum(i in query_run(t, 0)[1] for t in trees)
                error_i = sum(query_run(t, 1 << i)[0] != 1 for t in trees)
                self.assertLessEqual(len(trees)-seen, error0+error_i)

    def test_public_random_equality_exact_counts(self):
        for n in range(1, 5):
            q = 1 << n
            for x in range(q):
                for y in range(q):
                    single = sum(((x & mask).bit_count()%2) ==
                                 ((y & mask).bit_count()%2) for mask in range(q))
                    self.assertEqual(single, q if x == y else q//2)
                    for k in (1, 2):
                        count = sum(all(((x & mask).bit_count()%2) ==
                                        ((y & mask).bit_count()%2) for mask in masks)
                                    for masks in product(range(q), repeat=k))
                        self.assertEqual(count, q**k if x == y else (q//2)**k)

    def test_weighted_cost_and_binary_counter(self):
        for costs in product(range(4), repeat=3):
            for weights in product(range(4), repeat=3):
                weight = sum(weights)
                if not weight:
                    continue
                total = sum(w*c for w, c in zip(weights, costs))
                self.assertLessEqual(min(costs)*weight, total)
                self.assertLessEqual(total, max(costs)*weight)
        flips = 0
        for old in range(4096):
            flips += (old ^ (old+1)).bit_count()
            self.assertEqual(flips+(old+1).bit_count(), 2*(old+1))


if __name__ == '__main__':
    unittest.main(verbosity=2)
