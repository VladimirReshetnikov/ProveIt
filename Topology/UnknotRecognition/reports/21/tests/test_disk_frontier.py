from pathlib import Path
import sys, unittest, random, copy
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'experiments'))
from common import *
from disk_frontier import *
from radical import *
from fastunknot.planar import Planar
from fastunknot.geometry import ScanLimit

class GeometryTests(unittest.TestCase):
    def test_single_crossing(self):
        cert=certify_disk([(4,7,8,10)])
        self.assertEqual(cert.cyclic_order,(4,7,8,10))
        verify_disk_certificate([(4,7,8,10)],cert)

    def test_reject_disconnected_prefix(self):
        with self.assertRaises(GeometryError): certify_disk([(0,1,2,3),(4,5,6,7)])

    def test_reject_positive_genus(self):
        with self.assertRaises(GeometryError): certify_disk([(0,1,0,1)])

    def test_reject_multi_boundary_frontier(self):
        # Two vertices joined by parallel edges; frontier stubs on both sides.
        with self.assertRaises(GeometryError): certify_disk([(0,2,1,3),(0,4,1,5)])

    def test_three_pairings_cannot_use_one_order(self):
        triples=[((0,1),(2,3)),((0,2),(1,3)),((0,3),(1,2))]
        import itertools
        for p in itertools.permutations(range(4)):
            with self.assertRaises(GeometryError): verify_common_order(triples,p)
        alg=Planar(False); mids=[alg.intern(m) for m in triples]
        c=Complex(mids,[0,1,2],[{}, {}, {}])
        with self.assertRaises(GeometryError): reduce_complex(c,alg)

    def test_certificate_corruption(self):
        pd=[(0,1,2,3)];cert=certify_disk(pd).as_dict();cert['internal_edges']=1
        with self.assertRaises(GeometryError): verify_disk_certificate(pd,cert)

    def test_relabeling(self):
        pd=braid_pd(3,[1,-2]*3)
        for k in range(1,len(pd)):
            try: c=certify_disk(pd[:k])
            except GeometryError: continue
            remap={x:100-7*x for row in pd for x in row}
            new=certify_disk([tuple(remap[x] for x in row) for row in pd[:k]])
            self.assertEqual(new.cyclic_order,canonical_cycle(tuple(remap[x] for x in c.cyclic_order)))

    def test_ear_order_and_smoothing_states(self):
        rng=random.Random(6170); count=0
        for sample in range(80):
            s=rng.choice((2,3,4));n=rng.randint(max(3,s-1),8)
            word=list(range(1,s))+[rng.choice((-1,1))*rng.randint(1,s-1) for _ in range(n-s+1)]
            rng.shuffle(word);pd=braid_pd(s,word)
            try: order=bipolar_order(pd)
            except GeometryError: continue
            count+=1;validate_connected_cut_order(pd,order)
            scan=FastScan(shape_cache=False);prefix=[]
            for j in order:
                prefix.append(pd[j]);scan.add_crossing(pd[j],reduce_now=False)
                cert=certify_disk(prefix)
                verify_common_order([scan.algebra.pairs[m] for m in scan.mid if m is not None],cert.cyclic_order)
                scan.eliminate()
            certified=scan_pd(pd,RadicalScan,mode='always',order=order)
            self.assertEqual(certified.ranks_by_degree(),cube_ranks(pd))
            self.assertEqual(certified.stats['disk_declines'],0)
        self.assertGreater(count,20)

    def test_articulation_declined(self):
        pd=[(0,0,1,2),(1,3,4,2),(3,5,5,4)]
        diagram_graph(pd)
        with self.assertRaises(GeometryError):bipolar_order(pd)

    def test_adaptive_and_budgeted_interface(self):
        pd=braid_pd(3,[1,-2]*6)
        a=scan_pd(pd,FastScan); b=scan_pd(pd,RadicalScan,mode='adaptive')
        self.assertEqual(a.ranks_by_degree(),b.ranks_by_degree())
        c=RadicalScan(mode='adaptive',shape_cache=False)
        c.add_crossing((0,1,2,3),reduce_now=False)
        result=c.eliminate(update_budget=0)
        self.assertIs(type(result),bool)
        c.check_d_squared()

    def test_bounded_product_cache(self):
        alg=Planar(False);m=alg.intern(((0,1),(2,3)))
        c=Complex([m]*4,[0,0,1,1],[{2:7,3:6},{2:10,3:4},{},{}])
        a=reduce_complex(c,alg,cache_limit=0,certificate=True)
        b=reduce_complex(c,alg,cache_limit=1,certificate=True)
        self.assertEqual(a.complex,b.complex)
        self.assertEqual(a.stats['cache_peak'],0);self.assertLessEqual(b.stats['cache_peak'],1)
        verify_reduction(c,b,alg)
        with self.assertRaises(ValueError):reduce_complex(c,alg,cache_limit=-1)


class DriverTests(unittest.TestCase):
    def test_validated_recognition(self):
        from certified_driver import recognize_certified
        self.assertEqual(recognize_certified(braid_pd(2,[1]))['status'],'UNKNOT')
        self.assertEqual(recognize_certified(braid_pd(2,[1]*3))['status'],'KNOTTED')

    def test_link_and_virtual_rejected(self):
        from certified_driver import recognize_certified
        with self.assertRaises(ValueError):recognize_certified(braid_pd(2,[1,-1]))
        with self.assertRaises(ValueError):recognize_certified([(0,1,0,1)])
        with self.assertRaises(ValueError):recognize_certified([])

    def test_resource_limit_not_verdict(self):
        from certified_driver import recognize_certified
        with self.assertRaises(ScanLimit):recognize_certified(braid_pd(2,[1]),max_objects=0)

if __name__=='__main__': unittest.main()
