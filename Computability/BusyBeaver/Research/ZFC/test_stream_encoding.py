#!/usr/bin/env python3
"""Codec and concrete grammar regressions, not formal proof objects."""
import itertools
import random
import unittest
import kernel_metrics as k
import stream_encoding as s


class StreamEncodingTests(unittest.TestCase):
    def test_exhaustive_list_roundtrips_and_exact_bitlength(self):
        checked = 0
        for length in range(6):
            for xs in itertools.product(range(5), repeat=length):
                xs = list(xs)
                code = s.encode_list(xs)
                self.assertEqual(s.decode_list(code), xs)
                self.assertEqual(code.bit_length(), sum(x + 1 for x in xs))
                checked += 1
        self.assertEqual(checked, 3906)

    def test_every_small_natural_and_strict_descent(self):
        for code in range(65536):
            self.assertEqual(s.encode_list(s.decode_list(code)), code)
            if code:
                head, tail = s.uncons(code)
                self.assertLess(tail, code)
                self.assertEqual(s.cons(head, tail), code)
                self.assertEqual(code.bit_length(), head + 1 + tail.bit_length())

    def test_random_large_fields(self):
        rng = random.Random(20261016)
        for _ in range(100):
            head = rng.randrange(200)
            tail = rng.getrandbits(200)
            self.assertEqual(s.uncons(s.cons(head, tail)), (head, tail))

    def test_concrete_formula_and_frame_roundtrips(self):
        for f in k.templates(k.Mem(0, 1)).values():
            p = k.to_nand(k.alpha_reuse(k.normalize(f)))
            equality = 'eq' in k.metrics(p)['operators']
            self.assertEqual(s.decode_formula(s.encode_formula(p), equality=equality), p)
            self.assertEqual(s.deserialize_frame(s.serialize_frame(p)), p)
        result = s.experiment()
        self.assertEqual(result['totals'], {
            'natural_register_input_bits': 2789, 'framed_binary_bits': 2831,
            'reference_gamma_frame_bits': 3080, 'saved_framed_bits': 249})

    def test_strict_rejection_at_both_boundaries(self):
        for bad in (-1, True, None, 1.0):
            with self.assertRaises(ValueError): s.decode_list(bad)
        with self.assertRaises(ValueError): s.uncons(0)
        with self.assertRaises(ValueError): s.cons(False, 0)
        for fields in ([], [0], [0, 1], [1], [4], [3, 0, 1], [0, 0, 0, 0, 1, 1]):
            with self.assertRaises(ValueError, msg=repr(fields)):
                s.decode_formula(s.encode_list(fields))
        frame = s.serialize_frame(k.Mem(0, 1))
        for bad in (None, '', '2', '0', '000', frame[:-1], frame+'0',
                    '0'+k.gamma(1), '0'+k.gamma(3)+'10', '1'+frame[1:]):
            with self.assertRaises(ValueError, msg=repr(bad)): s.deserialize_frame(bad)


if __name__ == '__main__':
    unittest.main(verbosity=2)
