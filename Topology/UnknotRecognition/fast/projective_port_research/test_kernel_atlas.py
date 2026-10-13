"""Complete independent query and rejected-ray coverage after kernel integration."""
from itertools import combinations
import random
import unittest

from .common import Block, Prepared
from .filtered import FilterLimit
from .kernel_atlas import KernelPrepared, KernelFilteredAtlas
from .test_filtered import compiled
from experiments.oracle import all_rays, positive


class KernelAtlasTests(unittest.TestCase):
    def test_complete_queries_and_all_rejected_rays(self):
        rng = random.Random(17320261012)
        for i in range(60):
            d = 1+i % 3
            blocks = tuple(Block(3, ((1, 1, -1),) if rng.randrange(2) else (),
                tuple(tuple(rng.randrange(3) for _ in range(3)) for _ in range(d)),
                tuple(p for p in combinations(range(3), 2) if rng.random()<.2)) for _ in range(2))
            co = compiled(blocks)
            p = KernelFilteredAtlas(co)
            s = co.source
            rays = all_rays(s.n, s.equations, s.conflicts)
            for q in range(8):
                cost = tuple(rng.randrange(-3, 4) for _ in range(s.n))
                zero = tuple(j for j in range(s.n) if rng.random()<.1)
                excluded = tuple(frozenset(j for j in range(s.n) if rng.random()<.4) for _ in range(q % 4))
                eligible = tuple(r for r in rays if not any(all(r[j] for j in e) for e in excluded))
                a = p.solve(cost, zeros=zero, excluded=excluded)
                self.assertEqual(a['status']=='POSITIVE', bool(positive(eligible, cost, zero)))
            cost = tuple(rng.randrange(-2, 5) for _ in range(s.n))
            expected = {r for r in rays if sum(a*b for a,b in zip(r,cost))>0}
            result = p.search(cost, lambda x:dict(accepted=False), max_rejected=None, max_transitions=None)
            self.assertEqual(result['status'], 'NO_ACCEPTED_EXTREME')
            self.assertEqual({tuple(a['coordinates']) for a in result['trace']}, expected)
            self.assertEqual(len(result['trace']), len(expected))

    def test_prepared_atlas_identical(self):
        from projective_ports.fixtures import nonextreme_assembly
        blocks = nonextreme_assembly()
        old, new = Prepared(blocks, ray_method='zeros'), KernelPrepared(blocks)
        for key in ('raw_rays', 'zero_rays', 'rays', 'simplices', 'vertices', 'tables'):
            self.assertEqual(getattr(old, key), getattr(new, key))
        self.assertEqual(old.solve(((1,)*b.n for b in blocks)),
                         new.solve(((1,)*b.n for b in blocks)))

    def test_caps_and_caller_exceptions(self):
        p = KernelFilteredAtlas(compiled((Block(2, (), ((1, 1),)),)*2))
        self.assertEqual(p.search((1,)*4, lambda x:dict(accepted=True),
                                 max_transitions=0)['status'], 'INCONCLUSIVE')
        self.assertEqual(p.search((1,)*4, lambda x:dict(accepted=False),
                                 max_rejected=0)['status'], 'INCONCLUSIVE')
        def stop(*args):
            raise FilterLimit('caller stop')
        with self.assertRaisesRegex(FilterLimit, 'caller stop'):
            p.search((1,)*4, lambda x:dict(accepted=True), check=stop)
        with self.assertRaisesRegex(FilterLimit, 'caller stop'):
            p.search((1,)*4, stop)
        with self.assertRaises(ValueError):
            p.search((1,)*4, lambda x:dict(accepted=1))


if __name__ == '__main__':
    unittest.main()
