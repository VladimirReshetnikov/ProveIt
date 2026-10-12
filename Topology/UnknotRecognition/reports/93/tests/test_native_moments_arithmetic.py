"""Exhaustive arithmetic check of occupancy from global label inventory."""

from collections import Counter
import unittest

from native_moments import _decode


def partitions(labels):
    if not labels:
        yield []
        return
    first, *rest = labels
    for partition in partitions(rest):
        yield [[first]] + partition
        for index in range(len(partition)):
            yield [([first] + block if j == index else block)
                   for j, block in enumerate(partition)]


class NativeMomentArithmeticTests(unittest.TestCase):
    def test_every_partition_of_eight_labels(self):
        r = 8
        shift = (2 * r).bit_length()
        edge_bits = (2 * (r + (r * r << shift))).bit_length()
        packing = dict(codec='pair', sum_bits=shift, edge_bits=edge_bits)
        unit = 1 << edge_bits
        total, accepted = 0, 0
        for partition in partitions(list(range(1, r + 1))):
            total += 1
            histogram = Counter({17 * unit: 3})  # Silent orbits may have multiplicity.
            for index, block in enumerate(partition):
                histogram[sum(i + (i * i << shift) for i in block) + (3 * index + 2) * unit] += 1
            rows = [dict(weight=[weight], orbits=copies) for weight, copies in sorted(histogram.items())]
            valid = all(len(block) == 2 for block in partition)
            try:
                matching, lengths = _decode(rows, r, packing, lambda: None)
            except ArithmeticError:
                self.assertFalse(valid)
            else:
                self.assertTrue(valid)
                accepted += 1
                for index, block in enumerate(partition):
                    a, b = (label - 1 for label in block)
                    self.assertEqual(matching[a], b)
                    self.assertEqual(matching[b], a)
                    self.assertEqual(lengths[a], 3 * index + 2)
                    self.assertEqual(lengths[b], 3 * index + 2)
        self.assertEqual(total, 4140)
        self.assertEqual(accepted, 105)


if __name__ == '__main__':
    unittest.main()
