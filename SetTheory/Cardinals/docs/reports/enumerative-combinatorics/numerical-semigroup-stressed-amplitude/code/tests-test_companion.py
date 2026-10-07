#!/usr/bin/env python3
"""Bounded regression and rejection tests; effective under Python -O."""
import importlib.util
from fractions import Fraction as Q
from pathlib import Path
import sys
import unittest

sys.dont_write_bytecode=True
INITIAL_DIGIT_LIMIT=sys.get_int_max_str_digits()
ROOT=Path(__file__).resolve().parents[1]
SPEC=importlib.util.spec_from_file_location("report274_exact",ROOT/"companion"/"exact_checks.py")
EXACT=importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(EXACT)


class ExactCompanionTests(unittest.TestCase):
    def test_full_original_inequalities(self):
        self.assertTrue(EXACT.stressed((3,)))
        self.assertFalse(EXACT.stressed((1,3)))  # repeated source index 1
        self.assertFalse(EXACT.stressed((1,1,3)))
        self.assertFalse(EXACT.stressed((2,2)))
        self.assertTrue(EXACT.stressed((2,1,3)))
        self.assertEqual([len(EXACT.stressed_words(n)) for n in range(1,7)], [1,2,7,14,50,96])

    def test_boundary_polynomial_endpoints(self):
        expected=EXACT._shift(EXACT._power(EXACT.A_POLY,3),3)
        self.assertEqual(EXACT.boundary_polynomial(1),expected)
        for r in range(1,7):
            p=EXACT.boundary_polynomial(r)
            self.assertEqual(p,EXACT.transformed_boundary_polynomial(r))
            self.assertTrue(all(type(c) is int and c>=0 for c in p))
            self.assertEqual(len(p)-1,9*r+3)

    def test_length_refinement_and_zero_conventions(self):
        aggregate=(0,)
        for length in range(1,9):
            self.assertEqual(EXACT.genus_polynomial(length,True),EXACT.renewal_polynomial(length))
            aggregate=EXACT._add(aggregate,EXACT.genus_polynomial(length))
        self.assertEqual(aggregate[:3],(0,0,0))
        self.assertEqual(aggregate[3],1)
        self.assertEqual(aggregate[4],0)

    def test_general_transform_non_genus_activities(self):
        activities=(Q(5,4),Q(2,3),Q(1,2))
        mapped=EXACT.activity_transform(activities)
        u,v,w=activities
        for r in range(1,6):
            self.assertEqual(EXACT.general_boundary(r,activities),u*(u+v)*EXACT.activity_partition(r,mapped))
        self.assertEqual((u+v)/(v+w),(mapped[0]+mapped[1])/(mapped[1]+mapped[2]))

    def test_matching_allocation_and_marginals(self):
        self.assertGreater(EXACT.eligibility_checks(3)["aggregate_allocations"],100)
        local=EXACT.forbidden_marginal_checks()
        self.assertEqual(local["local_marginals"],54)
        self.assertEqual(local["four_block_product_checks"],3)

    def test_looped_container(self):
        graph=EXACT.cyclic_graph(5,{1,2,3,4})
        self.assertTrue(any(i in graph[i] for i in graph))
        self.assertTrue(all(len(graph[i])==4 for i in graph))
        with self.assertRaises(ValueError):
            EXACT.container(5,{2},{1})
        result=EXACT.container_checks(5)
        self.assertGreater(result["looped_graphs"],0)
        self.assertGreater(result["independent_sets"],result["graphs"])

    def test_overwritten_original_mark(self):
        # Find a bounded witness independently from the standardization loop.
        found=False
        for length in range(4,10):
            for word in EXACT.stressed_words(length):
                if word.count(3)<4:
                    continue
                d,sums,overwrite,image=EXACT.standardize(word,2)
                for q in range(1,length//3+1):
                    if word[q-1]==1 and q in overwrite:
                        found=True
                        self.assertEqual(image[q-1],3)
                        independent={i for i in range(1,d+1) if image[i-1]==1}
                        f,r=EXACT.container(d,sums,independent)
                        relations,_=EXACT.translated_relations(length,d,f|r,overwrite,q)
                        self.assertTrue(all((image[i-1],image[j-1])!=(1,3) for i,j in relations))
            if found:
                break
        self.assertTrue(found)

    def test_matching_is_parameter_deterministic(self):
        parameters=(48,47,set(range(1,48)),{43,44,45,46,47},7)
        first=EXACT.translated_relations(*parameters)
        second=EXACT.translated_relations(*parameters)
        self.assertEqual(first,second)
        relations,selected=first
        self.assertGreater(len(selected),0)
        self.assertGreaterEqual(8*len(selected),len(relations))
        blocks,_=EXACT.reflection_blocks(48)
        index={x:i for i,b in enumerate(blocks) for x in b}
        endpoints=[index[x] for pair in selected for x in pair]
        self.assertEqual(len(set(endpoints)),len(endpoints))

    def test_rational_certificate(self):
        certificate=EXACT.rational_certificate()
        self.assertEqual(certificate["x"],"33/50")
        self.assertEqual(certificate["pair_factors"]["P"],"225707/250000")
        self.assertEqual(certificate["endpoint_E_squared"],"1120000/1121931")

    def test_ascii_integer_cap(self):
        self.assertEqual(sys.get_int_max_str_digits(),INITIAL_DIGIT_LIMIT)
        self.assertEqual(EXACT.parse_integer("0"*639+"1","n",1,12),1)
        for text in ("9"*640,"1"*641,"0"*641,"-1","+1"," 1","1 ","1.0","١","",None):
            with self.subTest(text_type=type(text).__name__,length=len(text) if isinstance(text,str) else 0):
                with self.assertRaises(ValueError):
                    EXACT.parse_integer(text,"n",1,12)

    def test_integer_parameter_caps(self):
        calls=((EXACT.stressed_words,(13,)),(EXACT.stressed_words,(True,)),
               (EXACT.boundary_polynomial,(11,)),(EXACT.renewal_polynomial,(0,)),
               (EXACT.container_checks,(10,)),(EXACT.eligibility_checks,(9,)),
               (EXACT.standardization_checks,(13,)),(EXACT.cyclic_graph,(257,{1})),
               (EXACT.reflection_blocks,(257,)),(EXACT.run_checks,(13,)),
               (EXACT.genus_polynomial,(1,1)))
        for function,args in calls:
            with self.subTest(function=function.__name__,args=args):
                with self.assertRaises(ValueError):
                    function(*args)

    def test_rational_and_collection_caps(self):
        invalid=((True,1,1),(1.0,1,1),(0,1,1),(-1,1,1),(17,1,1),(Q(1,2**129),1,1),(1,2),None)
        for activities in invalid:
            with self.subTest(activities=str(activities)):
                with self.assertRaises(ValueError):
                    EXACT.checked_activities(activities)
        for sums in ({0},{True},{4},set()):
            with self.assertRaises(ValueError):
                EXACT.cyclic_graph(3,sums)
        with self.assertRaises(ValueError):
            EXACT.translated_relations(12,11,{1,2},{13},2)

    def test_explicit_checks_survive_optimization(self):
        with self.assertRaises(EXACT.CheckFailure):
            EXACT.ensure(False,"this must raise under -O as well")
        self.assertNotIn("assert ",Path(EXACT.__file__).read_text())


if __name__=="__main__":
    suite=unittest.defaultTestLoader.loadTestsFromTestCase(ExactCompanionTests)
    result=unittest.TextTestRunner(stream=sys.stderr,verbosity=1).run(suite)
    if not result.wasSuccessful():
        raise SystemExit(1)
    print(f"Report 274 companion regression tests passed: {result.testsRun}")
