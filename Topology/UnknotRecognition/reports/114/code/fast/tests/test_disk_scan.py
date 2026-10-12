import copy
import random
import unittest
from unittest.mock import patch

from fastunknot import Diagram, khovanov_rank, recognize
from fastunknot.disk_frontier import certify_disk, GeometryError, verify_disk_certificate
from fastunknot.disk_scan import DiskAdaptiveScan
from fastunknot.radical_transfer import snapshot
from fastunknot.scan_fast import FastScan
from fastunknot.geometry import ScanLimit
from fastunknot.window_scan import khovanov_window
from fastunknot.minimal_window import khovanov_minimal_window_auto
from disk_oracles import braid_pd, cube_ranks, scan_pd, profile, block_problem, regular_representation_homology


class EagerDiskScan(DiskAdaptiveScan):
    """Exercise the full path on small actual diagrams, including adjacent maps."""
    def eliminate(self):
        if not self._try_profile():
            FastScan.eliminate(self)


def synthetic_scan(b=3, m=24, sparse=False, **options):
    alg, c = block_problem(b=b, m=m, q=1, sparse=sparse)
    prefix = [tuple(range(3*j, 3*j+4)) for j in range(b-1)]
    cyclic = certify_disk(prefix).cyclic_order
    matching = alg.intern(tuple(sorted(tuple(sorted((cyclic[2*j], cyclic[2*j+1]))) for j in range(b))))
    c.mid = [matching] * c.n
    scan = DiskAdaptiveScan(shape_cache=False, **options)
    scan.algebra = alg
    scan.mid, scan.deg, scan.out = c.mid, c.deg, c.out
    scan.inc = [set() for _ in c.mid]
    for j, row in enumerate(c.out):
        for k in row:
            scan.inc[k].add(j)
    scan.live, scan.points = c.n, frozenset(cyclic)
    scan.processed_crossings = prefix
    return scan


class DiskIntegrationTests(unittest.TestCase):
    def test_geometry_declines_and_replay_corruption(self):
        for pd in ([(0,1,2,3),(4,5,6,7)], [(0,1,0,1)], [(0,2,1,3),(0,4,1,5)]):
            with self.assertRaises(GeometryError):
                certify_disk(pd)
        pd = [(4,7,8,10)]
        cert = certify_disk(pd).as_dict()
        self.assertTrue(verify_disk_certificate(pd, cert))
        cert['internal_edges'] += 1
        with self.assertRaises(GeometryError):
            verify_disk_certificate(pd, cert)

    def test_actual_adaptive_switch_preserves_nonzero_survivor_map(self):
        scan = synthetic_scan(m=12, transfer_polls=1000000)
        expected = regular_representation_homology(snapshot(scan), scan.algebra)
        scan.eliminate()
        self.assertEqual(scan.stats['disk_transfers'], 1)
        self.assertGreater(scan.stats['schur_update_pairs'], 0)
        self.assertTrue(any(scan.out))
        self.assertEqual(scan.live, 2)
        self.assertEqual(regular_representation_homology(snapshot(scan), scan.algebra), expected)

    def test_budget_and_geometry_declines_preserve_arrays_and_resume(self):
        for reason in ('budget', 'geometry'):
            scan = synthetic_scan(transfer_polls=2 if reason == 'budget' else 100000)
            if reason == 'geometry':
                scan.processed_crossings = [(100,101,102,103)]
            before = copy.deepcopy((scan.mid,scan.deg,scan.out,scan.inc,scan.live))
            expected = regular_representation_homology(snapshot(scan),scan.algebra)
            self.assertFalse(scan._try_transfer())
            self.assertEqual((scan.mid,scan.deg,scan.out,scan.inc,scan.live),before)
            scan.eliminate()
            self.assertEqual(regular_representation_homology(snapshot(scan),scan.algebra),expected)

    def test_global_abort_remains_global_and_atomic(self):
        scan = synthetic_scan()
        before = copy.deepcopy((scan.mid,scan.deg,scan.out,scan.inc,scan.live))
        calls = 0
        def abort():
            nonlocal calls
            calls += 1
            if calls == 20:
                raise ScanLimit('global deadline')
        scan.hook = abort
        with self.assertRaises(ScanLimit):
            scan._try_transfer()
        self.assertEqual((scan.mid,scan.deg,scan.out,scan.inc,scan.live),before)
        self.assertEqual(scan.stats['disk_budget_fallbacks'],0)

    def test_random_diagrams_eager_adaptive_and_prefix_profiles(self):
        rng = random.Random(2026100821)
        transfers = 0
        for sample in range(100):
            s = rng.choice((2,3,4)); n = rng.randint(s-1,8)
            word = list(range(1,s)) + [rng.choice((-1,1))*rng.randrange(1,s) for _ in range(n-s+1)]
            rng.shuffle(word); pd = braid_pd(s,word)
            order = list(range(n)); rng.shuffle(order)
            expected = cube_ranks(pd)
            a = scan_pd(pd,DiskAdaptiveScan,order=order,check=True)
            b = scan_pd(pd,EagerDiskScan,order=order,check=True)
            self.assertEqual(a.ranks_by_degree(),expected)
            self.assertEqual(b.ranks_by_degree(),expected)
            transfers += b.stats['disk_transfers']
            if sample < 40:
                a,b = FastScan(shape_cache=True),EagerDiskScan(shape_cache=True)
                for j in order:
                    a.add_crossing(pd[j]); b.add_crossing(pd[j])
                    self.assertEqual(profile(a),profile(b))
        self.assertGreater(transfers,0)

    def test_api_windows_composition_and_global_limits(self):
        d = Diagram.from_braid(3,[1,-2]*5)
        expected = khovanov_rank(d.pd)['by_degree']
        full = khovanov_rank(d.pd,reduction='disk-adaptive',composition='component-dense',check_d_squared=True)
        self.assertEqual(full['by_degree'],expected)
        # Force full-transfer attempts so both window MRO paths are exercised.
        with patch.object(DiskAdaptiveScan,'eliminate',EagerDiskScan.eliminate):
            for lo,hi in ((0,2),(2,7),(0,10)):
                target = {h:c for h,c in expected.items() if lo<=h<=hi}
                for query in (lambda: khovanov_window(d.pd,lo,hi,reduction='disk-adaptive',check_d_squared=True),
                              lambda: khovanov_minimal_window_auto(d,lo,hi,reduction='disk-adaptive',check_d_squared=True)):
                    result = query()
                    self.assertEqual(result['by_degree'],target)
                    self.assertIn('disk_attempts',result['stats'])
        result = recognize(d,reduction='disk-adaptive',seconds=0)
        self.assertEqual(result.status,'UNKNOWN')
        with self.assertRaises(ScanLimit):
            khovanov_rank(d.pd,reduction='disk-adaptive',max_objects=0)


if __name__ == '__main__':
    unittest.main()
