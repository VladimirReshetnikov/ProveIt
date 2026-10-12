"""Compare sparse passenger transport with full positive matrix elimination."""

from copy import deepcopy
from itertools import permutations, product
import random
import unittest

from fastunknot.raw_passenger_transport import transport_raw_passenger


def full_matrix_oracle(counts, schedule, passenger):
    """Independent dense update of donors and passenger; no timestamp checker.

    Invalid donor column-leaf schedules return None. A separate object labels
    the passenger row, and every surviving row/column pair is updated, even
    when the sparse algorithm can omit its zero fill.
    """
    marker = object()
    rows = {r: dict(row) for r, row in counts.items()}
    rows[marker] = dict(passenger)
    columns = set(passenger)
    for row in counts.values():
        columns.update(row)
    for r, g in schedule:
        if r not in rows or g not in columns or rows[r].get(g, 0) != 1:
            return None
        if any(i != r and i is not marker and row.get(g, 0)
               for i, row in rows.items()):
            return None
        previous = rows
        columns = columns - {g}
        rows = {}
        for i, row in previous.items():
            if i == r:
                continue
            rows[i] = {h: row.get(h, 0) + row.get(g, 0) * previous[r].get(h, 0)
                       for h in columns}
    if set(rows) != {marker}:
        return None
    return {h: value for h, value in rows[marker].items() if value}


class RawPassengerTransportTests(unittest.TestCase):
    def test_branching_merging_and_initial_internal_coefficients(self):
        counts = {10: {5: 1, 7: 2, 9: 3, 20: 4},
                  11: {7: 1, 9: 5, 20: 6},
                  12: {9: 1, 20: 7}}
        schedule = [[10, 5], [11, 7], [12, 9]]
        passenger = {5: 11, 7: 13, 9: 17, 20: 19, 99: 23}
        # Contributions are 11*(4+2*6+3*7+2*5*7) + 13*(6+5*7) + 17*7 + 19.
        expected = {20: 1848, 99: 23}
        self.assertEqual(full_matrix_oracle(counts, schedule, passenger), expected)
        self.assertEqual(transport_raw_passenger(counts, schedule, passenger), expected)

    def test_uncapped_counts_and_large_integer_products(self):
        a, b, c = (1 << 8192) + 3, (1 << 4096) + 5, (1 << 1024) + 7
        x, d, e = (1 << 2048) + 11, 13, 17
        counts = {0: {0: 1, 1: a, 3: b},
                  1: {1: 1, 2: c, 3: d},
                  2: {2: 1, 3: e}}
        schedule = [[0, 0], [1, 1], [2, 2]]
        expected = {3: x * (b + a * d + a * c * e)}
        self.assertEqual(transport_raw_passenger(counts, schedule, {0: x}), expected)
        self.assertEqual(full_matrix_oracle(counts, schedule, {0: x}), expected)
        capped = {r: {h: min(2, v) for h, v in row.items()} for r, row in counts.items()}
        self.assertNotEqual(transport_raw_passenger(capped, schedule, {0: x}), expected)

    def test_exhaustive_two_by_three_sources(self):
        accepted = 0
        for entries in product(range(3), repeat=6):
            counts = {r: {h: entries[3*r+h] for h in range(3)
                          if entries[3*r+h]} for r in range(2)}
            for row_order in permutations(range(2)):
                for columns in permutations(range(3), 2):
                    schedule = [list(pair) for pair in zip(row_order, columns)]
                    passenger = {0: 2, 1: 3, 2: 5, 9: 7}
                    expected = full_matrix_oracle(counts, schedule, passenger)
                    if expected is None:
                        continue
                    accepted += 1
                    self.assertEqual(transport_raw_passenger(counts, schedule, passenger),
                                     expected)
        self.assertGreater(accepted, 100)

    def test_random_acyclic_sources_with_relabelled_columns(self):
        rng = random.Random(20261012)
        for _ in range(120):
            size = rng.randrange(1, 9)
            columns = rng.sample(range(100, 300), size + 4)
            row_ids = rng.sample(range(500, 800), size)
            counts = {}
            for i, row_id in enumerate(row_ids):
                row = {columns[i]: 1}
                for j in range(i + 1, len(columns)):
                    value = rng.randrange(6)
                    if value:
                        row[columns[j]] = value
                counts[row_id] = row
            schedule = [[row_ids[i], columns[i]] for i in range(size)]
            passenger = {h: rng.randrange(12) for h in columns}
            passenger[997] = 19
            expected = full_matrix_oracle(counts, schedule, passenger)
            self.assertIsNotNone(expected)
            self.assertEqual(transport_raw_passenger(counts, schedule, passenger), expected)

    def test_empty_and_zero_passengers_and_unrelated_columns(self):
        self.assertEqual(transport_raw_passenger({}, [], {}), {})
        self.assertEqual(transport_raw_passenger({}, [], {3: 0, 7: 11}), {7: 11})
        counts, schedule = {4: {6: 1, 8: 9}}, [[4, 6]]
        self.assertEqual(transport_raw_passenger(counts, schedule, {}), {})
        self.assertEqual(transport_raw_passenger(counts, schedule, {6: 0, 13: 2}), {13: 2})
        self.assertEqual(transport_raw_passenger({0: {0: 1}}, [[0, 0]], {0: 5}), {})

    def test_multiple_survivors_and_explicit_source_zeros(self):
        counts = {2: {4: 1, 7: 0, 9: 3, 12: 5},
                  3: {7: 1, 4: 0, 9: 11, 12: 0}}
        schedule = [[2, 4], [3, 7]]
        self.assertEqual(transport_raw_passenger(counts, schedule, {4: 2, 7: 3}),
                         {9: 39, 12: 10})

    def test_inputs_are_not_mutated(self):
        counts = {2: {3: 1, 4: 5}, 7: {4: 1, 9: 11}}
        schedule, passenger = [[2, 3], [7, 4]], {3: 13, 4: 0, 99: 0}
        original = deepcopy((counts, schedule, passenger))
        transport_raw_passenger(counts, schedule, passenger)
        self.assertEqual((counts, schedule, passenger), original)

    def test_invalid_donor_data_and_schedules(self):
        cases = [
            ({0: {0: 1}}, []),
            ({0: {0: 1}}, [(0, 0)]),
            ({0: {0: 1}}, [[0, 0], [0, 0]]),
            ({0: {0: 1}, 1: {0: 1, 1: 1}}, [[0, 0], [1, 1]]),
            ({0: {0: 1}}, [[0, True]]),
            ({0: {0: 1}}, [[True, 0]]),
            ({0: {0: 1}}, [[0, -1]]),
            ({0: {0: 2}}, [[0, 0]]),
            ({0: {}}, [[0, 0]]),
            ({0: {0: -1}}, [[0, 0]]),
            ({0: {0: True}}, [[0, 0]]),
            ({False: {0: 1}}, [[0, 0]]),
            ({0: {False: 1}}, [[0, 0]]),
            ({0: {0: 1.0}}, [[0, 0]]),
            ([], []),
            ({0: []}, [[0, 0]]),
        ]
        for counts, schedule in cases:
            with self.assertRaises(ValueError):
                transport_raw_passenger(counts, schedule, {})

    def test_invalid_passenger_data(self):
        for passenger in ([], None, {0: -1}, {-1: 2}, {True: 2},
                          {0: True}, {0: 1.0}, {'0': 1}, {0: '0x1'}):
            with self.assertRaises(ValueError):
                transport_raw_passenger({}, [], passenger)

    def test_callback_exception_propagates(self):
        calls = 0

        def abort():
            nonlocal calls
            calls += 1
            if calls == 5:
                raise ValueError('passenger transport cancellation')

        with self.assertRaisesRegex(ValueError, 'passenger transport cancellation'):
            transport_raw_passenger({0: {0: 1, 1: 3}}, [[0, 0]], {0: 7}, check=abort)


if __name__ == '__main__':
    unittest.main()
