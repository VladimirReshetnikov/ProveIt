import copy
import itertools
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path[:0] = [str(ROOT/'code'), str(ROOT/'experiments')]
from pattern_kernel.core import Block, Tile, expand, certify_cubic_graph, kernelize
from pattern_kernel.signatures import tile_table, power
from routed_patterns import build_kernel, components, solve, verify_result, verify_source_witness
from routing_oracle import graph_table
from routing_families import star_triangle, connected_context, routed_edges, routed_beads


class RoutingTests(unittest.TestCase):
    def test_variable_width_partitions(self):
        data = components(star_triangle())
        self.assertEqual(data['permutation'], [1,0])
        self.assertEqual([x['left'] for x in data['groups']], [(0,), (1,2)])

    def test_small_explicit_verdicts(self):
        for tile in [star_triangle(), routed_beads([1,0]), connected_context()]:
            for n in range(1,13):
                with self.subTest(tile=tile, n=n):
                    chain = (Block(tile,n),)
                    result = solve(chain)
                    original, _ = expand(chain)
                    direct = certify_cubic_graph(original)
                    self.assertEqual(result['graph_proof']['verdict'], direct['verdict'])
                    self.assertTrue(verify_result(chain,result))

    def test_mixed_connected_and_routed(self):
        for a,b in [(1,1),(2,3),(17,13),(2**257+1,2**133+3)]:
            chain = (Block(star_triangle(),a), Block(connected_context(),b))
            result = solve(chain)
            self.assertTrue(verify_result(chain,result))

    def test_huge_source_addresses(self):
        n = 2**4096+1
        chain = (Block(star_triangle(),n),)
        result = solve(chain)
        self.assertTrue(verify_result(chain,result))
        source = verify_source_witness(chain,result['source_witness'])
        self.assertLessEqual(len(source['crossings']),3)
        self.assertTrue(all(int(x['copy'],16)<n for x in source['crossings']))
        self.assertEqual(len(result['kernel']['edges']),54)

    def test_old_route_rejects_new_family(self):
        with self.assertRaises(ValueError):
            kernelize((Block(star_triangle(),10**10),))
        self.assertTrue(verify_result((Block(star_triangle(),10**10),),
                                     solve((Block(star_triangle(),10**10),))))

    def test_naive_constant_cap_loses_routing(self):
        tile = routed_edges([1,0])
        self.assertNotEqual(power(tile_table(tile),5),power(tile_table(tile),4))
        reduced,_,_ = build_kernel((Block(tile,5),),close=False)
        self.assertEqual(graph_table(reduced),power(tile_table(tile),5))

    def test_complete_signatures(self):
        for perm in itertools.permutations(range(3)):
            tile = routed_edges(perm)
            for n in [1,2,4,7,17,101]:
                reduced,_,_ = build_kernel((Block(tile,n),),close=False)
                self.assertEqual(graph_table(reduced),power(tile_table(tile),n))

    def test_variable_width_complete_signatures(self):
        tile = star_triangle()
        for n in [1,2,3,8,9,18,101]:
            reduced,_,_ = build_kernel((Block(tile,n),),close=False)
            self.assertEqual(graph_table(reduced),power(tile_table(tile),n))

    def test_general_threshold(self):
        from routed_patterns.core import connected_cutoff
        self.assertEqual([connected_cutoff(k) for k in range(9)],
                         [1,3,4,4,5,6,7,8,9])
        for k in range(9):
            tile = routed_edges([1,0])
            reduced,_,_ = build_kernel((Block(tile,57),),threshold=k,close=False)
            self.assertEqual(graph_table(reduced,k),power(tile_table(tile,k),57,k))

    def test_reject_partition_mismatch(self):
        # Input partition {0,1},{2}, output partition {0,2},{1}.
        tile = Tile(6,((0,1),(1,3),(3,5),(2,4)),(0,1,2),(3,4,5))
        with self.assertRaises(ValueError):
            build_kernel((Block(tile,100),))
        build_kernel((Block(tile,3),))  # exact finite literal fallback

    def test_reject_private_components(self):
        tile = Tile(4,((0,1),(2,3)),(0,),(1,))
        with self.assertRaises(ValueError):
            build_kernel((Block(tile,100),))

    def test_certificate_mutations(self):
        chain = (Block(star_triangle(),2**80+1),)
        original = solve(chain)
        variants = []
        r=copy.deepcopy(original);r['plans'][0]['paths'][0]['exit']=0;variants.append(r)
        r=copy.deepcopy(original);r['plans'][0]['paths'][0]['cycle']=[0];variants.append(r)
        r=copy.deepcopy(original);r['kernel']['edges'][0]=[0,0];variants.append(r)
        r=copy.deepcopy(original);r['source_sha256']='bad';variants.append(r)
        r=copy.deepcopy(original);r['graph_proof']['cost']+=1;variants.append(r)
        r=copy.deepcopy(original)
        r['source_witness']['blocks'][0]['paths'][0]['segments'][0]['repeat']='0x0'
        variants.append(r)
        r=copy.deepcopy(original)
        r['source_witness']['blocks'][0]['paths'][0]['segments'][0]['word'][0]='0xffff'
        variants.append(r)
        r=copy.deepcopy(original);r['source_witness']['blocks'][0]['paths'].pop();variants.append(r)
        for variant in variants:
            self.assertFalse(verify_result(chain,variant))

    def test_positive_flow_mutation(self):
        chain=(Block(star_triangle(),1),)
        result=solve(chain)
        self.assertTrue(verify_result(chain,result))
        result['graph_proof']['four_flows'].pop()
        self.assertFalse(verify_result(chain,result))

    def test_bool_counts_rejected(self):
        with self.assertRaises(ValueError):
            Block(star_triangle(),True)


if __name__ == '__main__':
    unittest.main()
