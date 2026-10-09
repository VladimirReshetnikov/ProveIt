import copy
import itertools
import math
import random
import unittest
from unittest.mock import patch

from disk_kernel import (Candidate, ResourceLimit, canonical, partitions, root_row,
                         reduce_family, disk_compatible, minimum_completion, validate_partition)
from certificate_check import reference_row, graph_completion, verify_certificate
from signed_kernel import signed_row, signed_graph_completion, signed_states
from surface_model import glue_two, assemble_patches
from assembly import Layer, extend, solve, replay_surface


def complemented(v, width):
    top = (1 << (width - 1)) - 1
    ans = 0
    for i in range(top + 1):
        if v >> i & 1:
            ans |= 1 << (top ^ i)
    return ans


def coordinate_partition(r, mask):
    return canonical([0] + [(i + 1 if mask >> i & 1 else 0) for i in range(r - 1)])


def dimension(vectors):
    base = {}
    for v in vectors:
        while v:
            p = v.bit_length() - 1
            if p not in base:
                base[p] = v
                break
            v ^= base[p]
    return len(base)


def merge_layer(r):
    options = [Candidate(tuple(range(r)) * 2, 0)]
    for i in range(r):
        for j in range(i + 1, r):
            labels = list(range(r)) * 2
            labels = [i if a == j else a for a in labels]
            options.append(Candidate(canonical(labels), 1 + (i + j) % 3))
    return Layer(r, r, tuple(options))


class AlgebraTests(unittest.TestCase):
    def test_bell_counts(self):
        self.assertEqual([len(list(partitions(r))) for r in range(1, 9)], [1,2,5,15,52,203,877,4140])

    def test_two_row_constructions(self):
        for r in range(1, 8):
            for p in partitions(r):
                self.assertEqual(root_row(p), reference_row(p))

    def test_factorization_all_pairs(self):
        for r in range(1, 7):
            ps = list(partitions(r))
            rows = {p: root_row(p) for p in ps}
            dual = {p: complemented(rows[p], r) for p in ps}
            for p in ps:
                for q in ps:
                    expected = graph_completion(p, q)
                    self.assertEqual(disk_compatible(p, q), expected)
                    self.assertEqual((rows[p] & dual[q]).bit_count() % 2, expected)

    def test_full_and_graded_ranks(self):
        for r in range(1, 9):
            ps = list(partitions(r))
            self.assertEqual(dimension(root_row(p) for p in ps), 1 << (r - 1))
            for c in range(1, r + 1):
                self.assertEqual(dimension(root_row(p) for p in ps if max(p)+1 == c), math.comb(r-1,c-1))

    def test_coordinate_basis_sharpness(self):
        for r in range(1, 9):
            for mask in range(1 << (r - 1)):
                p = coordinate_partition(r, mask)
                self.assertEqual(root_row(p), 1 << mask)

    def test_permutation_invariance(self):
        rng = random.Random(8)
        for _ in range(200):
            r = rng.randrange(2, 8)
            ps = list(partitions(r))
            p,q = rng.choice(ps),rng.choice(ps)
            perm = list(range(r)); rng.shuffle(perm)
            self.assertEqual(disk_compatible(p,q), disk_compatible(canonical(p[i] for i in perm),canonical(q[i] for i in perm)))

    def test_guard_counterexample(self):
        family = [Candidate((0,0,1),0),Candidate((0,1,0),0),Candidate((0,1,1),1)]
        out = reduce_family(family).retained
        self.assertTrue(any(x.partition[1] == x.partition[2] for x in family))
        self.assertFalse(any(x.partition[1] == x.partition[2] for x in out))
        for q in partitions(3):
            a,b = minimum_completion(family,q), minimum_completion(out,q)
            self.assertEqual(None if a is None else a.cost, None if b is None else b.cost)


class CertificateTests(unittest.TestCase):
    def setUp(self):
        self.items = [Candidate((0,0,1),0), Candidate((0,1,0),0), Candidate((0,1,1),1)]
        self.cert = reduce_family(self.items).certificate
    def verify(self, cert=None, ps=None, costs=None):
        return verify_certificate(ps or [x.partition for x in self.items],
                                  costs if costs is not None else [x.cost for x in self.items],
                                  self.cert if cert is None else cert)
    def test_valid_and_independent(self):
        with patch('disk_kernel.root_row', side_effect=RuntimeError('producer disabled')):
            self.assertTrue(self.verify())
    def test_expansion_mutation(self):
        c = copy.deepcopy(self.cert); c['expansions'][2] = [0]
        self.assertFalse(self.verify(c))
    def test_cost_mutation(self):
        self.assertFalse(self.verify(costs=[0,0,-1]))
    def test_source_mutation(self):
        self.assertFalse(self.verify(ps=[(0,0,1),(0,1,0),(0,0,0)]))
    def test_duplicate_retained(self):
        c = copy.deepcopy(self.cert); c['retained'].append(c['retained'][0])
        self.assertFalse(self.verify(c))
    def test_extra_schema_field(self):
        c = copy.deepcopy(self.cert); c['trusted'] = True
        self.assertFalse(self.verify(c))
    def test_bool_and_float_indices(self):
        for val in (True, 0.0, -1, 99):
            c = copy.deepcopy(self.cert); c['retained'][0] = val
            self.assertFalse(self.verify(c))
    def test_false_version_or_width(self):
        for k,v in [('version',True),('version',2),('width',True),('width',2)]:
            c = copy.deepcopy(self.cert);c[k]=v
            self.assertFalse(self.verify(c))
    def test_repeated_expansion_index(self):
        c=copy.deepcopy(self.cert);c['expansions'][2]=[0,1,0,0]
        self.assertFalse(self.verify(c))
    def test_empty_family(self):
        result=reduce_family([])
        self.assertTrue(verify_certificate([],[],result.certificate))
    def test_huge_signed_costs(self):
        family = [Candidate(x.partition, -(1<<4096)+x.cost) for x in self.items]
        c = reduce_family(family).certificate
        self.assertTrue(verify_certificate([x.partition for x in family],[x.cost for x in family],c))
    def test_width_budget(self):
        with self.assertRaises(ResourceLimit):
            root_row((0,)*30)
        self.assertFalse(verify_certificate([x.partition for x in self.items],[0,0,1],self.cert,max_width=2))
    def test_callback_not_truthiness(self):
        class Check:
            calls=0
            def __bool__(self): return False
            def __call__(self): self.calls+=1
        c=Check();reduce_family(self.items,check=c)
        self.assertGreater(c.calls,0)
    def test_callback_cancel(self):
        def stop(): raise ResourceLimit('cancelled')
        with self.assertRaises(ResourceLimit):
            reduce_family(self.items,check=stop)
    def test_invalid_partitions(self):
        for p in [(),(1,),(0,2),(0,True),(0,-1),(0,1.0)]:
            with self.assertRaises(ValueError):validate_partition(p)
    def test_weighted_random_families(self):
        rng=random.Random(99)
        for _ in range(100):
            r=rng.randrange(1,7);ps=list(partitions(r))
            items=[Candidate(rng.choice(ps),rng.randrange(-20,21)) for _ in range(rng.randrange(1,60))]
            out=reduce_family(items)
            self.assertTrue(verify_certificate([x.partition for x in items],[x.cost for x in items],out.certificate))
            for q in ps:
                a,b=minimum_completion(items,q),minimum_completion(out.retained,q)
                self.assertEqual(None if a is None else a.cost,None if b is None else b.cost)


class SurfaceTests(unittest.TestCase):
    def test_literal_all_small_pairs(self):
        for r in range(1,5):
            for p in partitions(r):
                for q in partitions(r):
                    s=glue_two(p,q)
                    self.assertEqual(s['chi'],max(p)+max(q)+2-r)
                    self.assertEqual(s['is_disk'],graph_completion(p,q))
    def test_twists_do_not_change_tree_disks(self):
        p,q=(0,0,1,2),(0,1,1,1)
        self.assertTrue(graph_completion(p,q))
        for twists in itertools.product((0,1),repeat=4):
            self.assertTrue(glue_two(p,q,twists)['is_disk'])
    def test_parallel_arc_obstruction(self):
        self.assertTrue(glue_two((0,),(0,))['is_disk'])
        s=glue_two((0,0),(0,0))
        self.assertFalse(s['is_disk']);self.assertEqual(s['chi'],0)
        self.assertEqual(s['components'][0]['boundary_circles'],2)
    def test_mobius_control(self):
        s=glue_two((0,0),(0,0),(0,1))
        self.assertFalse(s['components'][0]['orientable'])
        self.assertEqual(s['components'][0]['boundary_circles'],1)
    def test_bad_pairing(self):
        with self.assertRaises(ValueError):
            assemble_patches([(0,),(0,)], [((0,0),(1,0)),((0,0),(1,0))])
    def test_signed_factorization(self):
        for r in range(1,6):
            states=list(signed_states(r))
            rows=[signed_row(p,s) for p,s in states]
            for i,(p,s) in enumerate(states):
                for j,(q,t) in enumerate(states):
                    self.assertEqual((rows[i]&rows[j]).bit_count()%2,
                                     signed_graph_completion(p,s,q,t))
    def test_signed_topological_oracle(self):
        rng=random.Random(91)
        for _ in range(200):
            r=rng.randrange(1,7);ps=list(partitions(r));p,q=rng.choice(ps),rng.choice(ps)
            t=tuple(rng.randrange(2) for i in range(r))
            surf=glue_two(p,q,t)
            expected=surf['component_count']==1 and surf['components'][0]['orientable']
            self.assertEqual(expected,signed_graph_completion(p,(0,)*r,q,t))


class AssemblyTests(unittest.TestCase):
    def test_identity_extension(self):
        for p in partitions(5):self.assertEqual(extend(p,tuple(range(5))*2,5),p)
    def test_cycle_rejected(self):
        self.assertIsNone(extend((0,0),(0,0,0),1))
    def test_sealed_component_rejected(self):
        self.assertIsNone(extend((0,1),(0,1,1),1))
    def test_complete_layered_search(self):
        rng=random.Random(11)
        for r in range(2,7):
            initial=[Candidate(p,rng.randrange(100)) for p in partitions(r)]
            layers=[merge_layer(r)]*2
            caps=[Candidate(p,0) for p in list(partitions(r))[::max(1,r*r)]]
            a=solve(initial,layers,caps,compressed=False)
            b=solve(initial,layers,caps,collect_certificates=True)
            self.assertEqual((a['status'],a['cost']),(b['status'],b['cost']))
            for e in b['certificates']:
                self.assertTrue(verify_certificate(e['partitions'],e['costs'],e['certificate']))
            if b['witness'] is not None:
                s=replay_surface(initial,layers,caps,b['witness'])
                self.assertTrue(s['is_disk']);self.assertEqual(s['cost'],b['cost'])
    def test_negative_result_only_grammar(self):
        a=solve([Candidate((0,0),0)],[],[Candidate((0,0),0)])
        self.assertEqual(a['status'],'NO_DISK_IN_GRAMMAR')
    def test_witness_index_validation(self):
        for v in (True,-1,1,0.0):
            with self.assertRaises(ValueError):
                replay_surface([Candidate((0,),0)],[],[Candidate((0,),0)],[v,0])

if __name__=='__main__':unittest.main()
