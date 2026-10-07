/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import Mathlib.Algebra.Lie.Prod
import OAI.Combinatorics.Progressions.Nilpotent.BCHQuotientLocalIsometry

namespace OAI

section

namespace Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

def tripleNeutral : (L × L × L) →ₗ[ℚ] L where
  toFun x := x.2.1 + x.2.2 - x.1
  map_add' x y := by dsimp; abel
  map_smul' r x := by simp [smul_add, smul_sub]

def tripleLeft : (L × L × L) →ₗ[ℚ] L where
  toFun x := x.1 - x.2.2
  map_add' x y := by dsimp; abel
  map_smul' r x := by simp [smul_sub]

def tripleRight : (L × L × L) →ₗ[ℚ] L where
  toFun x := x.1 - x.2.1
  map_add' x y := by dsimp; abel
  map_smul' r x := by simp [smul_sub]

def tripleAssemble (a b c : L) : L × L × L := (a + b + c, a + b, a + c)

@[simp] theorem tripleNeutral_assemble (a b c : L) : tripleNeutral (tripleAssemble a b c) = a := by
  change a + b + (a + c) - (a + b + c) = a
  abel

@[simp] theorem tripleLeft_assemble (a b c : L) : tripleLeft (tripleAssemble a b c) = b := by
  change a + b + c - (a + c) = b
  abel

@[simp] theorem tripleRight_assemble (a b c : L) : tripleRight (tripleAssemble a b c) = c := by
  change a + b + c - (a + b) = c
  abel

theorem tripleAssemble_decompose (x : L × L × L) :
    tripleAssemble (tripleNeutral x) (tripleLeft x) (tripleRight x) = x := by
  apply Prod.ext
  · change (x.2.1 + x.2.2 - x.1) + (x.1 - x.2.2) + (x.1 - x.2.1) = x.1
    abel
  · apply Prod.ext
    · change (x.2.1 + x.2.2 - x.1) + (x.1 - x.2.2) = x.2.1
      abel
    · change (x.2.1 + x.2.2 - x.1) + (x.1 - x.2.1) = x.2.2
      abel

omit [LieAlgebra ℚ L] in
theorem tripleAssemble_lie (a b c a' b' c' : L)
    (hbb : ⁅b, b'⁆ = 0) (hbc : ⁅b, c'⁆ = 0)
    (hcb : ⁅c, b'⁆ = 0) (hcc : ⁅c, c'⁆ = 0) :
    ⁅tripleAssemble a b c, tripleAssemble a' b' c'⁆ =
      tripleAssemble ⁅a, a'⁆ (⁅a, b'⁆ + ⁅b, a'⁆) (⁅a, c'⁆ + ⁅c, a'⁆) := by
  apply Prod.ext
  · change ⁅a + b + c, a' + b' + c'⁆ = _
    simp only [LieRing.add_lie, LieRing.lie_add, hbb, hbc, hcb, hcc, add_zero]
    change _ = ⁅a, a'⁆ + (⁅a, b'⁆ + ⁅b, a'⁆) + (⁅a, c'⁆ + ⁅c, a'⁆)
    abel
  · apply Prod.ext
    · change ⁅a + b, a' + b'⁆ = ⁅a, a'⁆ + (⁅a, b'⁆ + ⁅b, a'⁆)
      simp only [LieRing.add_lie, LieRing.lie_add, hbb, add_zero]
      abel
    · change ⁅a + c, a' + c'⁆ = ⁅a, a'⁆ + (⁅a, c'⁆ + ⁅c, a'⁆)
      simp only [LieRing.add_lie, LieRing.lie_add, hcc, add_zero]
      abel

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

noncomputable def realTripleEquiv :
    (ℝ ⊗[ℚ] (L × L × L)) ≃ₗ[ℝ] ((ℝ ⊗[ℚ] L) × (ℝ ⊗[ℚ] L) × (ℝ ⊗[ℚ] L)) :=
  (TensorProduct.prodRight ℚ ℝ ℝ L (L × L)).trans
    ((LinearEquiv.refl ℝ (ℝ ⊗[ℚ] L)).prodCongr (TensorProduct.prodRight ℚ ℝ ℝ L L))

@[simp] theorem realTripleEquiv_tmul (r : ℝ) (x : L × L × L) :
    realTripleEquiv (r ⊗ₜ[ℚ] x) = (r ⊗ₜ[ℚ] x.1, r ⊗ₜ[ℚ] x.2.1, r ⊗ₜ[ℚ] x.2.2) := rfl

theorem realTripleEquiv_neutral (x : ℝ ⊗[ℚ] (L × L × L)) :
    tripleNeutral (realTripleEquiv x) =
      (tripleNeutral : (L × L × L) →ₗ[ℚ] L).baseChange ℝ x := by
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
    simp only [realTripleEquiv_tmul, LinearMap.baseChange_tmul]
    change r ⊗ₜ[ℚ] x.2.1 + r ⊗ₜ[ℚ] x.2.2 - r ⊗ₜ[ℚ] x.1 =
      r ⊗ₜ[ℚ] (x.2.1 + x.2.2 - x.1)
    rw [TensorProduct.tmul_sub, TensorProduct.tmul_add]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem realTripleEquiv_left (x : ℝ ⊗[ℚ] (L × L × L)) :
    tripleLeft (realTripleEquiv x) =
      (tripleLeft : (L × L × L) →ₗ[ℚ] L).baseChange ℝ x := by
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
    simp only [realTripleEquiv_tmul, LinearMap.baseChange_tmul]
    change r ⊗ₜ[ℚ] x.1 - r ⊗ₜ[ℚ] x.2.2 = r ⊗ₜ[ℚ] (x.1 - x.2.2)
    rw [TensorProduct.tmul_sub]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem realTripleEquiv_right (x : ℝ ⊗[ℚ] (L × L × L)) :
    tripleRight (realTripleEquiv x) =
      (tripleRight : (L × L × L) →ₗ[ℚ] L).baseChange ℝ x := by
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
    simp only [realTripleEquiv_tmul, LinearMap.baseChange_tmul]
    change r ⊗ₜ[ℚ] x.1 - r ⊗ₜ[ℚ] x.2.1 = r ⊗ₜ[ℚ] (x.1 - x.2.1)
    rw [TensorProduct.tmul_sub]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem realTripleEquiv_first (x : ℝ ⊗[ℚ] (L × L × L)) :
    (realTripleEquiv x).1 = realificationLieHom (LieHom.fst ℚ L (L × L)) x := by
  induction x using TensorProduct.inductionOn with
  | tmul r x => rfl
  | add x y hx hy => simp only [map_add, Prod.fst_add, hx, hy]

theorem realTripleEquiv_second (x : ℝ ⊗[ℚ] (L × L × L)) :
    (realTripleEquiv x).2.1 = realificationLieHom
      ((LieHom.fst ℚ L L).comp (LieHom.snd ℚ L (L × L))) x := by
  induction x using TensorProduct.inductionOn with
  | tmul r x => rfl
  | add x y hx hy => simp only [map_add, Prod.fst_add, Prod.snd_add, hx, hy]

theorem realTripleEquiv_third (x : ℝ ⊗[ℚ] (L × L × L)) :
    (realTripleEquiv x).2.2 = realificationLieHom
      ((LieHom.snd ℚ L L).comp (LieHom.snd ℚ L (L × L))) x := by
  induction x using TensorProduct.inductionOn with
  | tmul r x => rfl
  | add x y hx hy => simp only [map_add, Prod.snd_add, hx, hy]

end Erdos3

end

end OAI
