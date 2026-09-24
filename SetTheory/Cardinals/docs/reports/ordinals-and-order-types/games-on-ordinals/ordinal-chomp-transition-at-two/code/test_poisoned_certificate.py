#!/usr/bin/env python3
"""Regression tests for the poisoned <4,6,9> certificate.

Run with code/ on sys.path, e.g. `python code/test_poisoned_certificate.py`
from the package root, or `make test`.  Python 3.9 or later.
"""
import sys
from pathlib import Path as _Path
sys.path.insert(0, str(_Path(__file__).resolve().parent))
import copy
from functools import lru_cache
import itertools
import json
from pathlib import Path
import tempfile
import unittest

from make_poisoned_certificate import generate, mex
from verify_poisoned_certificate import check_certificate

ROOT = Path(__file__).resolve().parents[1]


class CertificateTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.certificate = json.loads((ROOT/"certificates"/"s469_poisoned.json").read_text())

    def test_regeneration(self):
        self.assertEqual(generate(), self.certificate)

    def test_independent_verification(self):
        self.assertTrue(check_certificate(ROOT/"certificates"/"s469_poisoned.json")["verified"])

    def test_corrupted_label_rejected(self):
        damaged = copy.deepcopy(self.certificate)
        row = damaged["rows"][0]
        damaged["rows"][0] = str((int(row[0])+1) % 3) + row[1:]
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)/"bad.json"
            path.write_text(json.dumps(damaged))
            with self.assertRaises(ValueError):
                check_certificate(path)

    def test_corrupted_transition_rejected(self):
        damaged = copy.deepcopy(self.certificate)
        damaged["transition_recent_indices"][0][0] = 16
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)/"bad.json"
            path.write_text(json.dumps(damaged))
            with self.assertRaises(ValueError):
                check_certificate(path)

    def test_capped_mex_identity(self):
        for mask in range(256):
            values = [i for i in range(8) if mask >> i & 1]
            for cutoff in range(1, 6):
                self.assertEqual(min(cutoff, mex(values)),
                                 min(cutoff, mex([min(cutoff, x) for x in values])))

    def test_general_boundary_recurrence(self):
        """Check the theorem's identities for eight semigroups and three cutoffs."""
        cases = [(2, 3), (3, 4), (3, 5), (3, 4, 5),
                 (4, 5, 6, 7), (4, 6, 9), (5, 6, 7), (6, 7, 8, 9)]
        for generators in cases:
            membership = [True] + [False]*300
            for n in range(1, 301):
                membership[n] = any(n >= a and membership[n-a] for a in generators)
            gaps = [n for n in range(301) if not membership[n]]
            f = max(gaps)
            c = f+1
            last = c+f+10
            def member(n):
                return n >= 0 and membership[n]
            ideals = []
            for mask in range(1 << len(gaps)):
                tail = frozenset(g for i, g in enumerate(gaps) if mask >> i & 1)
                if all(a in tail for b in tail for a in gaps if member(b-a)):
                    ideals.append(tail)
            ideals.sort(key=lambda tail: (len(tail), tuple(sorted(tail))))
            @lru_cache(maxsize=None)
            def sg(position):
                return mex([sg(frozenset(z for z in position if not member(z-y)))
                            for y in position])
            def state(x, tail):
                return frozenset(y for y in range(1, x) if member(y)) | frozenset(x+g for g in tail)
            values = {(x, tail): sg(state(x, tail))
                      for x in range(c, last+1) for tail in ideals}
            for x in range(c+f, last+1):
                for tail in ideals:
                    options = []
                    for y in range(1, x-f):
                        if member(y):
                            ap = frozenset(z for z in range(1, y+f+1)
                                           if member(z) and not member(z-y))
                            options.append(sg(ap))
                    for d in range(1, f+1):
                        target = frozenset(g for g in gaps if g < d or g-d in tail)
                        self.assertIn(target, ideals)
                        options.append(values[x-d, target])
                    for a in tail:
                        target = frozenset(g for g in tail if not member(g-a))
                        options.append(values[x, target])
                    for cutoff in (1, 2, 3):
                        self.assertEqual(min(cutoff, values[x, tail]),
                                         min(cutoff, mex([min(cutoff, v) for v in options])),
                                         (generators, x, tail, cutoff))


if __name__ == "__main__":
    unittest.main(verbosity=2)
