"""Feasible-tuple parity, signed lifts, new rays and cancellation semantics."""
from fractions import Fraction as Q
from itertools import product
import random
import unittest

from fastunknot.port_subspace import PortBlock, compress_common_ports


def feasible(block, x):
    return (all(sum(a*v for a, v in zip(row, x)) == 0 for row in block.equations)
            and all(not (x[i] and x[j]) for i, j in block.conflicts))


class CommonPortTests(unittest.TestCase):
    def test_restriction_creates_a_new_ray(self):
        a = PortBlock(2, (), ((1, 0), (0, 1)))
        b = PortBlock(1, (), ((1,), (1,)))
        r = compress_common_ports((a, b))
        self.assertEqual(r.dimension, 1)
        self.assertEqual(r.original_nullities, (2, 1))
        self.assertEqual(r.restricted_nullities, (1, 1))
        self.assertFalse(feasible(r.blocks[0], (1, 0)))
        self.assertFalse(feasible(r.blocks[0], (0, 1)))
        self.assertTrue(feasible(r.blocks[0], (1, 1)))
        self.assertEqual(r.lift_port((3,)), (3, 3))

    def test_signed_lift_uses_nonnegative_selected_rows(self):
        b = PortBlock(3, ((-1, 1, 1),), ((1, 0, 0), (0, 1, 0), (0, 0, 1)))
        r = compress_common_ports((b, b))
        self.assertEqual(r.coordinates, (0, 1))
        self.assertEqual(r.lift_basis, ((1, 0, 1), (0, 1, -1)))
        self.assertEqual(r.lift_port((5, 2)), (5, 2, 3))
        self.assertEqual(r.reduce_master((2, 3, 7)), (9, -4))
        self.assertTrue(all(v >= 0 for b in r.blocks for row in b.ports for v in row))
        # Merely projecting and dropping the old equation would admit this.
        self.assertFalse(feasible(r.blocks[0], (2, 5, 0)))

    def test_zero_intersection_preserves_local_zero_port_vectors(self):
        a = PortBlock(2, (), ((1, 0), (0, 0)))
        b = PortBlock(2, (), ((0, 0), (1, 0)))
        r = compress_common_ports((a, b))
        self.assertEqual(r.dimension, 0)
        self.assertEqual(r.lift_port((0,)), (0, 0))
        self.assertEqual(r.reduce_master((1, 2)), (0,))
        self.assertTrue(all(feasible(b, (0, 3)) for b in r.blocks))
        self.assertFalse(feasible(r.blocks[0], (1, 0)))
        with self.assertRaises(ValueError):
            r.lift_port((1,))

    def test_exhaustive_small_integer_tuples(self):
        rng = random.Random(11320261012)
        xs = tuple(product(range(3), repeat=3))
        for model in range(100):
            d = 1+model % 4
            blocks = tuple(PortBlock(3,
                (tuple(rng.randrange(-2, 3) for _ in range(3)),) if model % 3 else (),
                tuple(tuple(rng.randrange(3) for _ in range(3)) for _ in range(d)),
                ((0, 1),) if model % 2 else ()) for _ in range(2))
            r = compress_common_ports(blocks)
            master = tuple(rng.randrange(-3, 4) for _ in range(d))
            reduced_master = r.reduce_master(master)
            self.assertTrue(all(h <= g for h, g in zip(r.restricted_nullities, r.original_nullities)))
            for x, y in product(xs, repeat=2):
                old = all(feasible(b, v) for b, v in zip(blocks, (x, y))) and blocks[0].image(x) == blocks[1].image(y)
                new = all(feasible(b, v) for b, v in zip(r.blocks, (x, y))) and r.blocks[0].image(x) == r.blocks[1].image(y)
                self.assertEqual(old, new, (model, x, y))
                if new:
                    port = blocks[0].image(x)
                    z = r.blocks[0].image(x)
                    self.assertEqual(r.lift_port(z), port)
                    self.assertEqual(sum(a*b for a, b in zip(master, port)),
                                     sum(a*b for a, b in zip(reduced_master, z)))

    def test_rational_row_changes_do_not_change_subspace(self):
        b = PortBlock(3, ((Q(2, 3), -1, 0),), ((1, 0, 0), (0, 1, 0), (0, 0, 1)))
        c = PortBlock(3, ((2, -3, 0), (4, -6, 0), (0, 0, 0)), b.ports)
        r = compress_common_ports((b, c))
        self.assertEqual(r.dimension, 2)
        self.assertEqual(r.lift_port((3, 7)), (3, 2, 7))

    def test_callback_exceptions_and_falsey_callable(self):
        class Stop(RuntimeError):
            pass
        class Callback:
            def __bool__(self):
                return False
            def __call__(self):
                raise Stop('propagate')
        with self.assertRaisesRegex(Stop, 'propagate'):
            compress_common_ports((), check=Callback())
        calls = 0
        def check():
            nonlocal calls
            calls += 1
            if calls == 5:
                raise Stop('elimination')
        with self.assertRaisesRegex(Stop, 'elimination'):
            compress_common_ports((PortBlock(2, (), ((1, 0), (0, 1))),), check=check)

    def test_validation(self):
        for n, eq, p, conflicts in ((True, (), ((1,),), ()), (1, ((1, 0),), ((1,),), ()),
                (1, (), ((-1,),), ()), (1, (), ((True,),), ()), (1, (), ((1.0,),), ()),
                (1, (), (), ()), (2, (), ((1, 0),), ((0, 0),)), (2, (), ((1, 0),), ((0, True),))):
            with self.assertRaises(ValueError):
                PortBlock(n, eq, p, conflicts)
        with self.assertRaises(ValueError):
            compress_common_ports(())
        with self.assertRaises(ValueError):
            compress_common_ports((PortBlock(1, (), ((1,),)), PortBlock(1, (), ((1,), (2,)))))
        r = compress_common_ports((PortBlock(1, (), ((1,),)),))
        with self.assertRaises(ValueError):
            r.reduce_master((1, 2))
        with self.assertRaises(ValueError):
            r.lift_port((1, 2))
        with self.assertRaises(ValueError):
            r.original_blocks[0].image((1, 2))


if __name__ == '__main__':
    unittest.main()
