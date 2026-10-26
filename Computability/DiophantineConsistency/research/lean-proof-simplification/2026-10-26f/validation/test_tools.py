#!/usr/bin/env python3
"""Tests only the supplied read-only Python helpers, not Lean proofs."""
import unittest
from static_audit import mask_noncode
from check_axiom_log import check
class Tests(unittest.TestCase):
    def test_comments(self):
        s='-- sorry\n/- axiom /- native_decide -/ sorry -/\ntheorem ok := by decide\n'
        x=mask_noncode(s); self.assertNotIn('sorry',x); self.assertNotIn('axiom',x); self.assertIn('decide',x); self.assertEqual(s.count('\n'),x.count('\n'))
    def test_strings(self):
        self.assertNotIn('sorry',mask_noncode('"sorry \\" axiom"'))
    def test_raw_strings(self):
        self.assertNotIn('sorry',mask_noncode('r##"sorry " axiom"##'))
    def test_axioms(self):
        r=check("'A.x' depends on axioms: [propext, Classical.choice, Quot.sound]",{'A.x'}); self.assertFalse(r['errors'])
    def test_prime(self): self.assertFalse(check("'A.x'' does not depend on any axioms",{"A.x'"})['errors'])
    def test_error(self): self.assertTrue(check("error: type mismatch\n'A.x' does not depend on any axioms",{'A.x'})['errors'])
    def test_wrapped(self): self.assertFalse(check("'A.x' depends on axioms: [propext,\n Classical.choice, Quot.sound]",{'A.x'})['errors'])
    def test_unclosed(self): self.assertTrue(check("'A.x' does not depend on any axioms\n'A.y' depends on axioms: [propext",{'A.x'})['errors'])
    def test_malformed(self): self.assertTrue(check("'A.x' depends on axioms: [propext Classical.choice]",{'A.x'})['errors'])
    def test_warning(self): self.assertTrue(check("'A.x' does not depend on any axioms\nwarning: declaration uses 'sorry'",{'A.x'})['errors'])
    def test_two_same_line(self): self.assertTrue(check("'A.x' does not depend on any axioms\n'A.bad' depends on axioms: [sorryAx] 'A.y' depends on axioms: [propext]",{'A.x'})['errors'])
    def test_empty(self): self.assertTrue(check('',set())['errors'])
    def test_missing(self): self.assertTrue(check("'A.x' does not depend on any axioms",{'A.y'})['errors'])
    def test_sorry(self): self.assertTrue(check("'A.x' depends on axioms: [sorryAx]",{'A.x'})['errors'])
    def test_native(self): self.assertTrue(check("'A.x' depends on axioms: [A.x._nativeDecide_1]",{'A.x'})['errors'])
    def test_legacy_native(self): self.assertTrue(check("'A.x' depends on axioms: [Lean.ofReduceBool]",{'A.x'})['errors'])
if __name__=='__main__': unittest.main()
