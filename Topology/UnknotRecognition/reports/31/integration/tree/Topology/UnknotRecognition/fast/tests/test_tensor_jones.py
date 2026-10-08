"""Independent full-cube, turning-number, and resource checks for tensors."""
import json
from fractions import Fraction
from pathlib import Path
import random
import unittest
from unittest.mock import patch

from fastunknot import Diagram
from fastunknot.geometry import ScanLimit
from fastunknot.separator_order import verify_width_bounded_order
from fastunknot.tensor_jones import (TensorLimit, _divide_loop, _local_tensor, _decode_integer,
                                    _add_valuations,
                                    rotation_cochain, tensor_jones)
from check_potts_independent import laurent_jones


def diagrams(count, seed):
    """Seeded small knot closures without optional report-package imports."""
    rng = random.Random(seed)
    accepted = 0
    while accepted < count:
        strands = rng.randrange(2, 5)
        word = [rng.choice((-1, 1))*rng.randrange(1, strands)
                for _ in range(rng.randrange(1, 9))]
        try:
            diagram = Diagram.from_braid(strands, word)
        except ValueError:
            continue
        order = list(range(diagram.crossings))
        rng.shuffle(order)
        accepted += 1
        yield diagram, order


def coefficients(result):
    return {e: int(c, 16) for e, c in result["jones_polynomial"]["coefficients_hex"]}


def independent_turning_numbers(diagram, smoothing, bends):
    """Follow literal oriented smoothing circles using independently made edges."""
    occurrences = {}
    for v, row in enumerate(diagram.pd):
        for j, label in enumerate(row):
            occurrences.setdefault(label, []).append(4*v+j)
    reverse = {}
    for endpoints in occurrences.values():
        a, b = endpoints
        reverse[a], reverse[b] = b, a
    smoothing_partner = {}
    for v in range(diagram.crossings):
        pairs = ((0, 3), (1, 2)) if smoothing >> v & 1 else ((0, 1), (2, 3))
        for a, b in pairs:
            smoothing_partner[4*v+a] = 4*v+b
            smoothing_partner[4*v+b] = 4*v+a
    unseen = set(reverse)
    rotations = []
    while unseen:
        start = current = min(unseen)
        turn = 0
        while True:
            opposite = reverse[current]
            outgoing = smoothing_partner[opposite]
            turn += bends[current] + (1 if (outgoing-opposite) % 4 == 1 else -1)
            unseen.discard(current)
            unseen.discard(opposite)
            current = outgoing
            if current == start:
                break
        rotations.append(turn)
    return rotations


class TensorJonesTests(unittest.TestCase):
    def test_valuation_addition_against_exact_rationals(self):
        rng = random.Random(2648)
        for _ in range(300):
            k = rng.randrange(1, 8)
            z = 1 << k
            pairs = []
            for _ in range(2):
                mantissa = rng.choice((-1, 1))*rng.randrange(1, 10000)
                exponent = rng.randrange(-20, 21)
                while mantissa % z == 0:
                    exponent += 1
                    mantissa //= z
                pairs.append((exponent, mantissa))
            value = _add_valuations(pairs[0], pairs[1], k)
            expected = sum(Fraction(z)**e*m for e, m in pairs)
            if value is None:
                self.assertEqual(expected, 0)
            else:
                self.assertNotEqual(value[1] % z, 0)
                self.assertEqual(Fraction(z)**value[0]*value[1], expected)
            self.assertIsNone(_add_valuations(pairs[0], (pairs[0][0], -pairs[0][1]), k))

    def test_integral_vertex_gauge_covariance_and_closed_invariance(self):
        rng = random.Random(2646)
        for diagram, order in diagrams(15, 2647):
            alpha = diagram.alpha()
            beta = rotation_cochain(diagram)
            height = [rng.randrange(-1000, 1001) for _ in range(diagram.crossings)]
            changed = tuple(beta[d] + height[alpha[d]//4]-height[d//4]
                            for d in range(len(beta)))
            for v in range(diagram.crossings):
                first = dict(_local_tensor(v, alpha, beta))
                second = dict(_local_tensor(v, alpha, changed))
                self.assertEqual(set(first), set(second))
                for mask, polynomial in first.items():
                    shift = sum((1 if mask >> j & 1 else -1)
                                * height[max(4*v+j, alpha[4*v+j])//4] for j in range(4))
                    self.assertEqual(dict(second[mask]), {e+shift: c for e, c in polynomial})
            expected = coefficients(tensor_jones(diagram, order=order, certified=False))
            with patch("fastunknot.tensor_jones.rotation_cochain", return_value=changed):
                actual = coefficients(tensor_jones(diagram, order=order, certified=False))
            self.assertEqual(actual, expected)
            integer = tensor_jones(diagram, order=order, certified=False, arithmetic="integer")
            with patch("fastunknot.tensor_jones.rotation_cochain", return_value=changed):
                transformed = tensor_jones(diagram, order=order, certified=False, arithmetic="integer")
            self.assertEqual(coefficients(transformed), expected)
            self.assertEqual(transformed["max_coefficient_bits"], integer["max_coefficient_bits"])
            self.assertEqual(transformed["peak_states"], integer["peak_states"])

    def test_every_smoothed_circle_has_rotation_plus_or_minus_four(self):
        cases = list(diagrams(20, 2640))
        checked = 0
        for diagram, _ in cases:
            if diagram.crossings > 10:
                continue
            for outer in (0, len(diagram.faces())-1):
                bends = rotation_cochain(diagram, outer_face=outer)
                for smoothing in range(1 << diagram.crossings):
                    turns = independent_turning_numbers(diagram, smoothing, bends)
                    self.assertTrue(all(abs(turn) == 4 for turn in turns))
                    checked += len(turns)
        self.assertGreater(checked, 1000)

    def test_independent_full_polynomials_mirrors_orders_and_outer_faces(self):
        rng = random.Random(2641)
        cases = list(diagrams(40, 2642))
        root = Path(__file__).resolve().parents[1] / "examples"
        for name in ("conway", "kinoshita_terasaka", "hard_unknot_8"):
            d = Diagram.from_json(json.loads((root / (name+".json")).read_text()))
            cases.append((d, list(range(d.crossings))))
        cases.append((Diagram.from_pd([]), []))
        for diagram, order in cases:
            for d in (diagram, diagram.mirror()):
                expected = {-e: c for e, c in laurent_jones(d).items()}
                variants = [order, list(reversed(order))]
                shuffled = list(order)
                rng.shuffle(shuffled)
                variants.append(shuffled)
                for i, supplied in enumerate(variants):
                    for arithmetic in ("laurent", "integer", "integer-global"):
                        result = tensor_jones(d, order=supplied, certified=False,
                                              arithmetic=arithmetic,
                                              outer_face=0 if i < 2 or not d.crossings
                                              else len(d.faces())-1)
                        self.assertEqual(coefficients(result), expected)
                        self.assertEqual(result["polynomial_identity"]["is_one"], expected == {0: 1})
                        self.assertLessEqual(result["peak_states"], 1 << result["max_boundary"])

    def test_integer_decoder_extreme_signed_coefficients_and_both_shift_directions(self):
        for n in range(1, 13):
            k = max(1, (2*n+9)//8)
            cases = [{0: 1}, {-2*n: 4**n}, {2*n: -4**n},
                     {-2*n: -(4**n)//2, 2*n: (4**n)//2}, {0: 4**n}]
            for polynomial in cases:
                w = n
                for extra in (0, 40*n+10):
                    g = 6*w-4-8*max(polynomial)-extra
                    value = sum(c << (k*(6*w-8*e+delta-g))
                                for e, c in polynomial.items() for delta in (-4, 4))
                    decoded, shortcut = _decode_integer(value, crossings=n, writhe=w,
                        laurent_shift=g, encoding_bits=k, check=lambda: None)
                    self.assertEqual(decoded, polynomial)
                    self.assertEqual(shortcut, polynomial == {0: 1})
        with self.assertRaises(ValueError):
            _decode_integer(1, crossings=10, writhe=0, laurent_shift=0,
                            encoding_bits=1, check=lambda: None)
        with self.assertRaises(ArithmeticError):
            _decode_integer(1, crossings=3, writhe=3, laurent_shift=0,
                            encoding_bits=1, check=lambda: None)

    def test_certified_order_and_source_free_pd(self):
        source = Diagram.from_braid(4, [1, -2, 3, -1, 2, -3, 1, 2, 3])
        d = Diagram.from_pd(source.pd)
        result = tensor_jones(d, order=list(reversed(range(d.crossings))))
        self.assertTrue(verify_width_bounded_order(d.pd, result["order_certificate"]))
        self.assertEqual(coefficients(result), {-e: c for e, c in laurent_jones(d).items()})
        self.assertEqual(result["max_boundary"], result["order_certificate"]["profile"][0])

    def test_local_caps_and_global_interruptions_publish_no_partial_polynomial(self):
        d = Diagram.from_braid(3, [1, -2]*5)
        exact = tensor_jones(d)
        self.assertEqual(tensor_jones(d, max_transitions=exact["transitions"]), exact)
        statistics = {"sentinel": 1}
        with self.assertRaises(TensorLimit) as caught:
            tensor_jones(d, max_transitions=exact["transitions"]-1, statistics=statistics)
        self.assertEqual(caught.exception.transitions, exact["transitions"]-1)
        self.assertEqual(statistics, {"sentinel": 1})
        for options in ({"max_states": 0}, {"max_transitions": 0}, {"max_states": 1}):
            with self.assertRaises(TensorLimit):
                tensor_jones(d, **options)
        calls = 0
        def interrupt():
            nonlocal calls
            calls += 1
            if calls == 200:
                raise ScanLimit("injected tensor deadline")
        with self.assertRaises(ScanLimit):
            tensor_jones(d, check=interrupt, statistics=statistics)
        self.assertEqual(statistics, {"sentinel": 1})

    def test_input_validation_and_corrupted_normalization(self):
        d = Diagram.from_braid(2, [1, 1, 1])
        for options in ({"max_states": -1}, {"max_states": True},
                        {"max_transitions": -1}, {"certified": 1},
                        {"arithmetic": "floating"},
                        {"outer_face": True}, {"outer_face": -1},
                        {"outer_face": len(d.faces())}, {"order": [0]}):
            with self.assertRaises(ValueError):
                tensor_jones(d, **options)
        with self.assertRaises(ArithmeticError):
            _divide_loop({0: 1}, lambda: None)
        with patch("fastunknot.tensor_jones.rotation_cochain", return_value=(0,)*12):
            with self.assertRaises(ArithmeticError):
                tensor_jones(d, certified=False)
        with patch("fastunknot.separator_order.verify_width_bounded_order", return_value=False):
            with self.assertRaises(ArithmeticError):
                tensor_jones(d)


if __name__ == "__main__":
    unittest.main()
