"""Independent exact quaternion witnesses, group checks, and solver cross-checks."""
from fractions import Fraction
import importlib.util
from itertools import permutations, product
from types import SimpleNamespace
import unittest

from fastunknot.diagram import Diagram, DiagramError
from fastunknot.compressed_words import WordArena
from fastunknot.su2 import (Ring, SU2Limit, bridge_presentation, compile_bridge,
    compile_diagram_presentation, compile_presentation, compile_slp,
    quaternion_mul, quaternion_inverse, simplify_presentation, solve_formula,
    su2_decide, wirtinger_presentation)


def multiply(p, q):
    # Independent scalar quaternion arithmetic, not the symbolic compiler.
    a, b, c, d = p
    e, f, g, h = q
    return (a*e-b*f-c*g-d*h, a*f+b*e+c*h-d*g,
            a*g-b*h+c*e+d*f, a*h+b*g-c*f+d*e)


def inverse(q):
    return (q[0], -q[1], -q[2], -q[3])


def word_value(word, images):
    answer = (1, 0, 0, 0)
    for letter in word:
        q = images[abs(letter)]
        answer = multiply(answer, q if letter > 0 else inverse(q))
    return answer


def assign_formula(formula, images):
    return {f'g{g}_{label}': value for g, q in images.items()
            for label, value in zip('abcd', q) if f'g{g}_{label}' in formula.ring.names}


class SU2CompilerTests(unittest.TestCase):
    def test_quaternion_signs_and_norm(self):
        ring = Ring()
        q = tuple(ring.var(c) for c in 'abcd')
        got = quaternion_mul(ring, q, quaternion_inverse(ring, q))
        self.assertEqual(got[1:], ({}, {}, {}))
        self.assertEqual(got[0], ring.squares(q))
        i, j, k = (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)
        self.assertEqual(multiply(i, j), k)
        self.assertEqual(multiply(j, i), tuple(-x for x in k))

    def test_rational_trefoil_witness(self):
        half = Fraction(1, 2)
        images = {1: (half, half, half, half), 2: (half, half, -half, -half)}
        word = (1, 2, 1, -2, -1, -2)
        self.assertEqual(word_value(word, images), (1, 0, 0, 0))
        formula = compile_presentation([1, 2], [word], chunk_size=10, gauge=False)
        residuals, inequality = formula.evaluate(assign_formula(formula, images))
        self.assertTrue(all(x == 0 for x in residuals))
        self.assertGreater(inequality, 0)
        self.assertFalse(formula.metadata['knot_provenance'])

    def test_distinct_commuting_images_are_not_nonabelian(self):
        # <a,b | b=a^2> is cyclic despite the distinct images a=i, b=-1.
        formula = compile_presentation([1, 2], [(2, -1, -1)], gauge=False, chunk_size=10)
        images = {1: (0, 1, 0, 0), 2: (-1, 0, 0, 0)}
        residuals, inequality = formula.evaluate(assign_formula(formula, images))
        self.assertTrue(all(x == 0 for x in residuals))
        self.assertEqual(inequality, 0)
        # Even equal trace does not certify conjugacy in the presented group:
        # these two distinct rational order-three quaternions still commute.
        half = Fraction(1, 2)
        images = {1: (-half, half, half, half),
                  2: (-half, -half, -half, -half)}
        residuals, inequality = formula.evaluate(assign_formula(formula, images))
        self.assertTrue(all(x == 0 for x in residuals))
        self.assertEqual(inequality, 0)
        with self.assertRaises(TypeError):
            compile_presentation([1, 2], [(2, -1, -1)], meridional=True)

    def test_chunk_auxiliaries_are_unique_prefix_values(self):
        images = {1: (0, 1, 0, 0), 2: (0, 0, 1, 0)}
        word = (1, 1, 1, 1, 2, 2, 2, 2)
        for size in (1, 2, 3, 7, 8):
            formula = compile_presentation([1, 2], [word], chunk_size=size, gauge=False)
            assignment = assign_formula(formula, images)
            for aux, stop in enumerate(range(size, len(word), size)):
                q = word_value(word[:stop], images)
                assignment.update({f'u{aux}_{label}': value for label, value in zip('abcd', q)})
            residuals, inequality = formula.evaluate(assignment)
            self.assertTrue(all(x == 0 for x in residuals))
            self.assertGreater(inequality, 0)
            self.assertLessEqual(formula.summary()['max_equation_degree'], max(2, size+1))

    def test_binary_power_does_not_expand(self):
        arena = WordArena(max_nodes=10_000, max_work=100_000)
        root = arena.power(arena.letter(1), 1 << 120)
        formula = compile_slp([1, 2], arena, [root], gauge=False)
        self.assertEqual(formula.metadata['product_gates'], 120)
        self.assertEqual(formula.metadata['auxiliary_quaternions'], 120)
        self.assertEqual(formula.summary()['aggregate_degree_bound'], 4)
        self.assertLess(formula.summary()['polynomial_terms'], 4000)
        self.assertLess(len(formula.to_smt2()), 200_000)

    def test_slp_exact_values_and_hybrid_degree(self):
        arena = WordArena()
        word = [1, 2, -1, -2] * 2
        root = arena.from_word(word)
        images = {1: (0, 1, 0, 0), 2: (0, 0, 1, 0)}
        self.assertEqual(word_value(word, images), (1, 0, 0, 0))
        for degree in (1, 2, 3, 8):
            formula = compile_slp([1, 2], arena, [root], inline_degree=degree, gauge=False)
            assignment = assign_formula(formula, images)
            values, degrees = {0: (1, 0, 0, 0)}, {0: 0}
            cuts = 0
            for node in arena._reachable([root]):
                rule = arena.rules[node]
                if rule[0] == 't':
                    values[node] = images[abs(rule[1])] if rule[1] > 0 else inverse(images[abs(rule[1])])
                    degrees[node] = 1
                else:
                    _, a, b = rule
                    values[node], degrees[node] = multiply(values[a], values[b]), degrees[a]+degrees[b]
                    if degrees[node] > degree:
                        assignment.update({f'u{cuts}_{label}': value
                                           for label, value in zip('abcd', values[node])})
                        cuts += 1
                        degrees[node] = 1
            residuals, inequality = formula.evaluate(assignment)
            self.assertTrue(all(x == 0 for x in residuals))
            self.assertGreater(inequality, 0)
            self.assertLessEqual(formula.summary()['aggregate_degree_bound'], max(4, 4*degree))

    def test_bridge_letter_bound_and_cyclic_closure(self):
        for strands, word in [(2,[1]*3), (3,[1,2]), (3,[1,2,-2,1,-1,2]),
                               (3,[1,-2,1,-2]), (4,[1,2,3,2,-2])]:
            diagram = Diagram.from_braid(strands, word)
            presentation = bridge_presentation(diagram)
            conjugacies = presentation['conjugacies']
            self.assertEqual(sum(len(w) for _, _, w in conjugacies), len(word))
            self.assertEqual(len(conjugacies), presentation['overpasses'])
            self.assertEqual([t for _,t,_ in conjugacies],
                             list(range(2,len(conjugacies)+1))+[1])
            f = compile_bridge(diagram)
            self.assertLessEqual(f.metadata['auxiliary_quaternions'],
                                 len(word) // f.metadata['chunk_size'])

    def test_tietze_moves_preserve_finite_group_solution_counts(self):
        permutations3 = tuple(permutations(range(3)))
        identity = tuple(range(3))
        def mul(a,b): return tuple(a[b[i]] for i in range(3))
        def inv(a): return tuple(a.index(i) for i in range(3))
        def count(gens, relators):
            result = 0
            for values in product(permutations3, repeat=len(gens)):
                images = dict(zip(gens, values))
                valid = True
                for w in relators:
                    q = identity
                    for x in w: q = mul(q, images[x] if x > 0 else inv(images[-x]))
                    if q != identity: valid = False;break
                result += valid
            return result
        for strands, word in [(2,[1]*3), (3,[1,-2,1,-2]), (3,[1,2])]:
            d = Diagram.from_braid(strands, word)
            gens, relators = wirtinger_presentation(d)
            simplified = simplify_presentation(gens, relators)
            expected = count(gens, relators)
            self.assertEqual(expected, count(simplified['generators'], simplified['relators']))
            b = bridge_presentation(d)
            words = [tuple(w)+(s,)+tuple(-x for x in reversed(w))+(-t,)
                     for s,t,w in b['conjugacies']]
            self.assertEqual(expected, count(b['generators'], words))

    def test_limits_and_malformed_inputs_never_produce_verdicts(self):
        d = Diagram.from_braid(2,[1]*3)
        self.assertEqual(su2_decide(d, seconds=0)['status'], 'INCONCLUSIVE')
        self.assertEqual(su2_decide(d, max_work=0)['status'], 'INCONCLUSIVE')
        with self.assertRaises(SU2Limit): compile_bridge(d, max_terms=0)
        with self.assertRaises(ValueError): simplify_presentation([1], [[0,0]])
        with self.assertRaises(ValueError): compile_presentation([1], [[2]])
        with self.assertRaises(ValueError): compile_slp([1], SimpleNamespace(rules=[None,('c',1,0)]), [1])
        with self.assertRaises(DiagramError): compile_bridge(Diagram(((0,1,2,3),)))
        class Cancelled(Exception): pass
        def cancel(): raise Cancelled()
        with self.assertRaises(Cancelled): su2_decide(d, check=cancel)

    @unittest.skipUnless(importlib.util.find_spec('z3'), 'optional exact solver not installed')
    def test_exact_solver_on_known_group_and_knot_queries(self):
        cyclic = compile_presentation([1,2], [[2,-1,-1]], chunk_size=10)
        self.assertEqual(solve_formula(cyclic, seconds=3)['status'], 'NO_NONABELIAN')
        for strands, word, expected in [(1,[], 'UNKNOT'), (3,[1,2], 'UNKNOT'),
                                        (2,[1]*3,'KNOTTED'), (3,[1,-2,1,-2],'KNOTTED')]:
            result = su2_decide(Diagram.from_braid(strands,word), presentation='tietze',
                                seconds=3, trace_zero_probe=True)
            self.assertEqual(result['status'], expected)
            if expected == 'KNOTTED': self.assertTrue(result['model_checked_exactly'])


if __name__ == '__main__':
    unittest.main()
