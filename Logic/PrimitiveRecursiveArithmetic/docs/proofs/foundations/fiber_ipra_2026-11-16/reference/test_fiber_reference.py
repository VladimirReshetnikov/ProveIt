from fractions import Fraction
import unittest

from fiber_reference import (
    FiberError,
    NetCertificate,
    Quantifier,
    bisection_trace,
    check_monotone_on_finite_lattice,
    dyadic_scaled_discrepancy,
    dyadic_value,
    finite_demand_closure,
    finite_net_lift,
    herbrand_capsule,
    least_accepted,
    least_valid_in_capsule,
    master_certificate,
    mixed_radix_decode,
    mixed_radix_encode,
    verify_bisection_trace,
    verify_bounded_strategy,
    verify_dyadic_adjacent_motion,
    verify_dyadic_cauchy_bound,
)


class FiberReferenceTests(unittest.TestCase):
    def test_mixed_radix_roundtrip(self) -> None:
        bounds = (3, 5, 2, 7)
        for a in range(bounds[0]):
            for b in range(bounds[1]):
                values = (a, b, 1, 6)
                code = mixed_radix_encode(values, bounds)
                self.assertEqual(mixed_radix_decode(code, bounds), values)

    def test_mixed_radix_rejects_bad_value(self) -> None:
        with self.assertRaises(FiberError):
            mixed_radix_encode((3,), (3,))

    def test_least_accepted(self) -> None:
        self.assertEqual(least_accepted(20, lambda x: x >= 7 and x % 3 == 1), 7)
        self.assertIsNone(least_accepted(5, lambda x: x == 8))

    def test_master_certificate(self) -> None:
        bounds = (8, 9, 6)
        verifiers = (
            lambda x: x >= 3 and x % 2 == 1,
            lambda x: x * x >= 20,
            lambda x: x == 4,
        )
        code, witnesses = master_certificate(bounds, verifiers)
        self.assertEqual(witnesses, (3, 5, 4))
        self.assertEqual(mixed_radix_decode(code, bounds), witnesses)

    def test_monotone_demand_closure(self) -> None:
        capacities = (4, 5, 3)

        def step(v: tuple[int, ...]) -> tuple[int, ...]:
            x, y, z = v
            return (min(4, y), min(5, x + 1), min(3, (y + 1) // 2))

        self.assertTrue(check_monotone_on_finite_lattice(capacities, step))
        closure = finite_demand_closure(capacities, step)
        self.assertEqual(closure.fixed_point, (4, 5, 3))
        self.assertLessEqual(closure.iterations, sum(capacities))

    def test_least_prefixed_empirically(self) -> None:
        capacities = (3, 3)

        def step(v: tuple[int, ...]) -> tuple[int, ...]:
            x, y = v
            return (min(3, y), min(3, x + 1))

        closure = finite_demand_closure(capacities, step)
        fp = closure.fixed_point
        for x in range(4):
            for y in range(4):
                candidate = (x, y)
                image = step(candidate)
                if all(a <= b for a, b in zip(image, candidate, strict=True)):
                    self.assertTrue(all(a <= b for a, b in zip(fp, candidate, strict=True)))

    def test_bounded_strategy(self) -> None:
        # For every x<5 choose y<6 with y=x+1 and y>x.
        quantifiers = (
            Quantifier("forall", lambda history: 5),
            Quantifier("exists", lambda history: 6),
        )
        strategy = {(x,): x + 1 for x in range(5)}
        leaf = lambda h: h[1] == h[0] + 1 and h[1] > h[0]
        self.assertTrue(verify_bounded_strategy(quantifiers, strategy, leaf))
        bad = dict(strategy)
        bad[(3,)] = 3
        self.assertFalse(verify_bounded_strategy(quantifiers, bad, leaf))

    def test_nested_strategy(self) -> None:
        # exists a<3, forall b<4, exists c<8: c=a+b and c<8
        quantifiers = (
            Quantifier("exists", lambda h: 3),
            Quantifier("forall", lambda h: 4),
            Quantifier("exists", lambda h: 8),
        )
        strategy = {(): 2}
        strategy.update({(2, b): 2 + b for b in range(4)})
        self.assertTrue(
            verify_bounded_strategy(
                quantifiers, strategy, lambda h: h[2] == h[0] + h[1]
            )
        )

    def test_dyadic_adjacent_motion(self) -> None:
        # floor(2^n / 3) is an adjacent-unit name for 1/3.
        numerators = tuple((1 << n) // 3 for n in range(16))
        self.assertTrue(verify_dyadic_adjacent_motion(numerators))
        self.assertTrue(verify_dyadic_cauchy_bound(numerators))
        for n in range(len(numerators)):
            for m in range(n, len(numerators)):
                self.assertLess(
                    abs(dyadic_value(numerators[n], n) - dyadic_value(numerators[m], m)),
                    Fraction(1, 1 << n) if m > n else Fraction(1, 1),
                )

    def test_dyadic_exact_bound(self) -> None:
        nums = (0, 1, 2, 5, 10, 21)
        self.assertTrue(verify_dyadic_adjacent_motion(nums))
        self.assertEqual(dyadic_scaled_discrepancy(nums, 1, 5), 5)
        self.assertLessEqual(5, (1 << 4) - 1)

    def test_finite_net_lift(self) -> None:
        domain = tuple(Fraction(i, 8) for i in range(9))
        net = NetCertificate((Fraction(0), Fraction(1, 2), Fraction(1)), Fraction(1, 4))
        f = lambda x: x * (1 - x)
        result = finite_net_lift(
            domain=domain,
            net=net,
            f=f,
            modulus_delta=Fraction(1, 4),
            local_bound=Fraction(1, 4),
        )
        self.assertEqual(set(result), set(domain))
        self.assertTrue(all(bound == Fraction(1, 2) for _, bound in result.values()))

    def test_net_detects_missing_coverage(self) -> None:
        net = NetCertificate((Fraction(0),), Fraction(1, 10))
        with self.assertRaises(FiberError):
            finite_net_lift(
                (Fraction(1),), net, lambda x: x, Fraction(2), Fraction(0)
            )

    def test_bisection_trace(self) -> None:
        polynomial = lambda x: x * x - 2
        trace = bisection_trace(polynomial, Fraction(1), Fraction(2), 12)
        self.assertTrue(verify_bisection_trace(polynomial, trace))
        left, right = trace[-1]
        self.assertLessEqual(polynomial(left), 0)
        self.assertGreaterEqual(polynomial(right), 0)
        self.assertEqual(right - left, Fraction(1, 1 << 12))

    def test_herbrand_capsule(self) -> None:
        capsule = herbrand_capsule((9, 8, 7, 6), lambda x: x % 3 == 1)
        self.assertEqual(least_valid_in_capsule(capsule, lambda x: x % 3 == 1), 7)


if __name__ == "__main__":
    unittest.main(verbosity=2)
