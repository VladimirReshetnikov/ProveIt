"""Targeted rejection checks for the new mathematical certificate checker."""
import json
from pathlib import Path
import unittest
import check_certificate as cc

HERE = Path(__file__).resolve().parent


class CertificateChecks(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.old = cc.parse((HERE / 'source_zfc253.tm').read_bytes())
        cls.new = cc.parse((HERE / 'zfc253_shortcut.tm').read_bytes())
        cls.masks = json.loads((HERE / 'invariant_radius2.json').read_text())['state_pattern_masks']

    def test_actual_certificate(self):
        self.assertEqual(cc.check_invariant(self.old, self.masks), (7044, [8, 9, 24, 25]))
        self.assertEqual(cc.check_macro(self.old, self.new), 8)

    def test_initial_blank_is_required(self):
        masks = self.masks.copy()
        masks[0] &= ~1
        with self.assertRaisesRegex(ValueError, 'initial'):
            cc.check_invariant(self.old, masks)

    def test_missing_reachable_pattern_rejected(self):
        masks = self.masks.copy()
        masks[60] &= ~(1 << 8)
        with self.assertRaisesRegex(ValueError, 'closure'):
            cc.check_invariant(self.old, masks)

    def test_all_windows_is_closed_but_does_not_prove_guard(self):
        with self.assertRaisesRegex(ValueError, 'guarded'):
            cc.check_invariant(self.old, [(1 << 32) - 1] * 254)

    def test_invalid_mask_width_rejected(self):
        masks = self.masks.copy()
        masks[0] |= 1 << 32
        with self.assertRaisesRegex(ValueError, '32'):
            cc.check_invariant(self.old, masks)

    def test_wrong_macro_target_rejected(self):
        rows = self.new.copy()
        rows[60, 0] = (0, 1, 52)
        with self.assertRaisesRegex(ValueError, 'replacement'):
            cc.check_macro(self.old, rows)

    def test_other_changed_row_rejected(self):
        rows = self.new.copy()
        rows[0, 0] = (0, 1, 52)
        with self.assertRaisesRegex(ValueError, 'exactly'):
            cc.check_macro(self.old, rows)

    def test_left_zero_guard_is_necessary(self):
        old = cc.local_run(self.old, 60, 0, {-1}, 3)
        new = cc.local_run(self.new, 60, 0, {-1}, 1)
        self.assertNotEqual(old, new)


if __name__ == '__main__':
    unittest.main()
