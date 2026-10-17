"""Adversarial checks for the new block certificate's substantive obligations."""
import unittest
import edge_replacement_search as c


class Certificates(unittest.TestCase):
    def setUp(self):
        self.machine = c.parse_table('''#! start 0
0 0 0 R 1
0 1 1 R 2
1 0 0 L 2
1 1 1 L 2
2 0 0 R 2
2 1 1 L 3
3 0 0 R 2
3 1 1 R 4
''')
        self.windows = c.abstract_windows(self.machine, 2)
        self.row = (0, 0)
        self.patterns = self.windows[0]
        self.originals = {}
        for bits in self.patterns:
            tr, stop = c.trace(self.machine, 0, bits, 2, 16)
            targets = {}
            for i, conf in enumerate(tr, 1):
                if conf[0] != 1:
                    targets.setdefault(c.key(self.machine, conf), i)
            self.originals[bits] = targets, len(tr), stop

    def test_direction_changing_deletion(self):
        edge = c.Edge(0, -1, 3)
        cert, failure = c.check_row(self.machine, self.row, edge, self.patterns, 2, 16,
                                    1, frozenset({self.row}), self.originals)
        self.assertIsNone(failure)
        self.assertEqual(cert, [[0, 2, 2]])
        self.assertTrue(c.independent_check(self.machine, 1, {self.row: edge},
                         self.windows, 2, 16, {self.row: cert}))

    def test_different_whole_tape_does_not_match(self):
        cert, failure = c.check_row(self.machine, self.row, c.Edge(1, -1, 3),
                                    self.patterns, 2, 16, 1, frozenset({self.row}), self.originals)
        self.assertIsNone(cert)
        self.assertIsNotNone(failure)

    def test_other_changed_row_must_not_execute(self):
        cert, failure = c.check_row(self.machine, self.row, c.Edge(0, -1, 3),
                                    self.patterns, 2, 16, 1,
                                    frozenset({self.row, (3, 0)}), self.originals)
        self.assertIsNone(cert)
        self.assertEqual(failure[-1], 'changed_row')

    def test_removed_target_is_forbidden(self):
        cert, failure = c.check_row(self.machine, self.row, c.Edge(0, 1, 1),
                                    self.patterns, 2, 16, 1, frozenset({self.row}), self.originals)
        self.assertIsNone(cert)
        self.assertEqual(failure[-1], 'removed')

    def test_zero_progress_certificate_is_rejected(self):
        with self.assertRaises(AssertionError):
            c.independent_check(self.machine, 1, {self.row: c.Edge(0, -1, 3)},
                                self.windows, 2, 16, {self.row: [[0, 0, 0]]})

    def test_missing_window_certificate_is_rejected(self):
        with self.assertRaises(AssertionError):
            c.independent_check(self.machine, 1, {self.row: c.Edge(0, -1, 3)},
                                self.windows, 2, 16, {self.row: []})

    def test_forged_step_count_is_rejected(self):
        with self.assertRaises(AssertionError):
            c.independent_check(self.machine, 1, {self.row: c.Edge(0, -1, 3)},
                                self.windows, 2, 16, {self.row: [[0, 2, 1]]})

    def test_blank_trace_is_in_abstract_reachability(self):
        ones, head, q = set(), 0, self.machine.start
        for _ in range(200):
            bits = sum((int(head + i in ones) << (i + 2)) for i in range(-2, 3))
            self.assertIn(bits, self.windows[q])
            if q == self.machine.halt:
                break
            edge = self.machine.rows[q, int(head in ones)]
            if edge.write:
                ones.add(head)
            else:
                ones.discard(head)
            head += edge.move
            q = edge.target

    def test_incomplete_machine_is_rejected(self):
        with self.assertRaises(ValueError):
            c.parse_table('#! start 0\n0 0 1 R 1\n')


if __name__ == '__main__':
    unittest.main(verbosity=2)
