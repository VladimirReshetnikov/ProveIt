import Mathlib

open Matrix

#check @Matrix.det_submatrix_equiv_self
#check @Matrix.fromBlocks_multiply
#check @Matrix.det_fromBlocks_zero₂₁
#check @Matrix.det_fromBlocks_zero₁₂
#check @Matrix.det_permute'
#check @RingHom.map_det
#check @Matrix.det_smul
#check @ZMod.intCast_zmod_eq_zero_iff_dvd
#check @Int.odd_iff
#check @Matrix.det_one
#check @Matrix.det_fin_one
#check @Matrix.det_mul
#check @Matrix.fromBlocks_one
#check @Equiv.sumCongr
#check (inferInstance : Fact (Nat.Prime 2))
#check @Matrix.det_fromBlocks₁₁
#check @Matrix.submatrix
#check @Matrix.det_reindex_self
example (x : ZMod 2) : x * x = x := by decide +kernel
example : ((-1 : ℤ) : ZMod 2) = 1 := by decide
