"""Independent small-cone oracles and filter/callback regression cases."""
from itertools import combinations
import random
import unittest

from .common import Block, Source, compile_two_block
from .filtered import FilteredAtlas, Budget, FilterLimit
from projective_ports.source import synchronized_source, Compilation, compile_variable_separator
from experiments.oracle import all_rays, positive


def compiled(blocks):
    source, _, offsets = synchronized_source(blocks, tuple((0,)*b.n for b in blocks))
    maps = tuple(tuple(range(off, off+b.n)) for off,b in zip(offsets, blocks))
    return Compilation(source, tuple(blocks), maps)


class FilteredTests(unittest.TestCase):
    def test_random_queries_and_full_rejected_enumeration(self):
        rng = random.Random(11720261012)
        queries = 0
        for i in range(60):
            d = 1+i % 3
            blocks = tuple(Block(3, ((1, 1, -1),) if rng.randrange(2) else (),
                tuple(tuple(rng.randrange(3) for _ in range(3)) for _ in range(d)),
                tuple(p for p in combinations(range(3), 2) if rng.random()<.2)) for _ in range(2))
            co = compiled(blocks)
            p = FilteredAtlas(co)
            s = co.source
            rays = all_rays(s.n, s.equations, s.conflicts)
            for q in range(8):
                cost = tuple(rng.randrange(-3, 4) for _ in range(s.n))
                zero = tuple(j for j in range(s.n) if rng.random()<.1)
                excluded = tuple(frozenset(j for j in range(s.n) if rng.random()<.4) for _ in range(q % 4))
                eligible = tuple(r for r in rays if not any(all(r[j] for j in e) for e in excluded))
                a = p.solve(cost, zeros=zero, excluded=excluded)
                self.assertEqual(a['status']=='POSITIVE', bool(positive(eligible, cost, zero)))
                queries += 1
            cost = tuple(rng.randrange(-2, 5) for _ in range(s.n))
            expected = {r for r in rays if sum(a*b for a,b in zip(r,cost))>0}
            result = p.search(cost, lambda x:dict(accepted=False), max_rejected=None, max_transitions=None)
            self.assertEqual(result['status'], 'NO_ACCEPTED_EXTREME')
            self.assertEqual({tuple(a['coordinates']) for a in result['trace']}, expected)
            self.assertEqual(len(result['trace']), len(expected))
        self.assertEqual(queries, 480)

    def test_clause_coverage_is_distributed_across_blocks(self):
        # Synchronized scalar blocks choose either coordinate in each block.
        co = compiled((Block(2, (), ((1, 1),)),)*3)
        p = FilteredAtlas(co)
        all_even = frozenset((0, 2, 4))
        all_odd = frozenset((1, 3, 5))
        a = p.solve((1,)*6, excluded=(all_even, all_odd))
        self.assertEqual(a['status'], 'POSITIVE')
        x = co.reconstruct(a['vectors'])
        self.assertTrue(any(x[j]==0 for j in all_even))
        self.assertTrue(any(x[j]==0 for j in all_odd))

    def test_zero_port_and_rejection_limit(self):
        co = compiled((Block(2, (), ((0, 0),)),)*2)
        p = FilteredAtlas(co)
        a = p.search((1,)*4, lambda x:dict(accepted=x[3]==1), max_rejected=None)
        self.assertEqual(a['status'], 'ACCEPTED_EXTREME')
        self.assertEqual(len(a['rejected']), 3)
        b = p.search((1,)*4, lambda x:dict(accepted=False), max_rejected=1)
        self.assertEqual(b['status'], 'INCONCLUSIVE')
        self.assertEqual(len(b['rejected']), 1)

    def test_master_copy_exclusions(self):
        s = Source(3, ((1, -1, 0), (1, 0, -1)))
        co = compile_variable_separator(s, (0,))
        p = FilteredAtlas(co)
        self.assertEqual(p.solve((1,)*3)['status'], 'POSITIVE')
        self.assertEqual(p.solve((1,)*3, excluded=((0,),))['status'], 'NO_POSITIVE')
        a = p.search((1,)*3, lambda x:dict(accepted=False), max_rejected=None)
        self.assertEqual(a['status'], 'NO_ACCEPTED_EXTREME')
        self.assertEqual(len(a['rejected']), 1)

    def test_nonextreme_assembly_recovers_a_new_source_ray(self):
        from projective_ports.fixtures import nonextreme_assembly
        p = FilteredAtlas(compiled(nonextreme_assembly()))
        a = p.search((1,)*5, lambda x:dict(accepted=False), max_rejected=None)
        self.assertEqual(a['status'], 'NO_ACCEPTED_EXTREME')
        s = p.compilation.source
        self.assertEqual({tuple(x['coordinates']) for x in a['trace']},
                         set(all_rays(s.n, s.equations, s.conflicts)))

    def test_caps_and_callback_exceptions(self):
        p = FilteredAtlas(compiled((Block(2, (), ((1, 1),)),)*2))
        self.assertEqual(p.search((1,)*4, lambda x:dict(accepted=True),
                                 max_transitions=0)['status'], 'INCONCLUSIVE')
        class Stop:
            def __bool__(self):
                return False
            def __call__(self, *args):
                raise FilterLimit('external')
        with self.assertRaisesRegex(FilterLimit, 'external'):
            p.search((1,)*4, lambda x:dict(accepted=False), check=Stop())
        with self.assertRaisesRegex(FilterLimit, 'external'):
            p.search((1,)*4, Stop())
        with self.assertRaises(ValueError):
            p.search((1,)*4, lambda x:dict(accepted=1))
        with self.assertRaises(ValueError):
            p.search((1,)*4, lambda x:dict(accepted=True), max_rejected=True)
        with self.assertRaises(ValueError):
            p.solve((1,)*4, excluded=((True,),))
        with self.assertRaises(ValueError):
            Budget(True, lambda: None)


if __name__ == '__main__':
    unittest.main()
