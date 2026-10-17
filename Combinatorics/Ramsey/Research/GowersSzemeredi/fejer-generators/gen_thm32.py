"""Theorem 3.2 is the case `c i = i` of the linear-pattern bound.

`progressionAverage f` is `linearPatternAverage (fun i => (i : ZMod N)) f` by definition, and
`k ≤ N` makes these coefficients distinct. The linear-pattern modules stop importing
Proofs03ProgressionAverage (they take its two analytic lemmas), and Proofs03ProgressionAverage
imports them and keeps only theorem_3_2_holds; its progression-specific copies are deleted.
"""
from foldlib import Fold

F = Fold()
PA, LS = 'Proofs03ProgressionAverage', 'Proofs03LinearPatternStep'
moved = F.take(PA, 'sum_rpow_le_rpow_average') + '\n' + F.take(PA, 'le_rpow_mul_of_sq_le')
s = F.get(LS)
old = 'import GowersSzemeredi.Proofs03ProgressionAverage\n'
assert s.startswith(old)
s = ('import GowersSzemeredi.Proofs03Equivalences\nimport Mathlib.Analysis.Convex.Jensen\n'
     'import Mathlib.Analysis.Convex.SpecificFunctions.Pow\n' + s[len(old):])
anchor = 'namespace LeanProofs.GowersSzemeredi\n\n'
i = s.index(anchor) + len(anchor)
F.text[LS] = s[:i] + moved + '\n' + s[i:]

F.text[PA] = '''import GowersSzemeredi.Proofs03LinearPatternBound

/-!
# The generalized von Neumann bound for arithmetic progressions

This module proves the repaired prime-modulus form of Theorem 3.2. The
progression average is the linear-pattern average with coefficients
`c i = i`, and the restriction `k ≤ N` makes these coefficients distinct, so
the theorem is a case of `linearPattern_uniform_last_bound`.
-/

set_option autoImplicit false

namespace LeanProofs.GowersSzemeredi

/-- **Theorem 3.2.** Generalized von Neumann bound for progression averages,
in the corrected prime-modulus range `2 ≤ k ≤ N`. -/
theorem theorem_3_2_holds : theorem_3_2 := by
  intro N k _ _ hk2 hkN f hf alpha ha0 hu
  refine linearPattern_uniform_last_bound hk2 (fun i => ((i : Nat) : ZMod N)) ?_ f hf alpha ha0 hu
  intro i j h
  have := (ZMod.natCast_eq_natCast_iff' (i : Nat) j N).1 h
  rwa [Nat.mod_eq_of_lt (i.2.trans_le hkN), Nat.mod_eq_of_lt (j.2.trans_le hkN), Fin.val_inj] at this

end LeanProofs.GowersSzemeredi
'''
F.commit()
