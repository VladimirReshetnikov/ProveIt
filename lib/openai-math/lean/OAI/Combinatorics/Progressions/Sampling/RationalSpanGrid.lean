/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Set
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Data.Int.Interval
import Mathlib.Data.Set.Card
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.DiscreteSubset
import OAI.Combinatorics.Progressions.Estimates.RationalImageIntersections

namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

variable {ι κ : Type*}

def IntegralVector (x : ι → ℚ) : Prop := ∃ z : ι → ℤ, ∀ i, x i = (z i : ℚ)

theorem IntegralVector.nat_smul {x : ι → ℚ} (hx : IntegralVector x) (n : ℕ) :
    IntegralVector ((n : ℚ) • x) := by
  obtain ⟨z, hz⟩ := hx
  refine ⟨fun i => (n : ℤ) * z i, fun i => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, hz, Int.cast_mul, Int.cast_natCast]

def scaledIntegerGrid (L : ℕ) : Set (ι → ℚ) :=
  {x | ∃ z : ι → ℤ, x = (L : ℚ) • (fun i => (z i : ℚ))}

def denominatorGrid (L : ℕ) : Set (ι → ℚ) :=
  {x | IntegralVector ((L : ℚ) • x)}

theorem mem_denominatorGrid_iff (L : ℕ) (hL : 0 < L) (x : ι → ℚ) :
    x ∈ denominatorGrid L ↔ ∃ z : ι → ℤ, ∀ i, x i = (z i : ℚ) / L := by
  have hLq : (L : ℚ) ≠ 0 := by exact_mod_cast hL.ne'
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, fun i => ?_⟩
    apply (eq_div_iff hLq).mpr
    simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using hz i
  · rintro ⟨z, hz⟩
    refine ⟨z, fun i => ?_⟩
    change (L : ℚ) * x i = (z i : ℚ)
    rw [hz i, mul_div_cancel₀ _ hLq]

variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def matrixDenominator (A : Matrix ι κ ℚ) : ℕ :=
  arrayDenominator (fun ij : ι × κ => A ij.1 ij.2)

def clearedMatrix (A : Matrix ι κ ℚ) : Matrix ι κ ℤ :=
  fun i j => clearedArray (fun ij : ι × κ => A ij.1 ij.2) (i, j)

omit [DecidableEq ι] [DecidableEq κ] in
theorem matrixDenominator_pos (A : Matrix ι κ ℚ) : 0 < matrixDenominator A :=
  arrayDenominator_pos _

omit [DecidableEq ι] [DecidableEq κ] in
theorem matrixDenominator_le (A : Matrix ι κ ℚ) {H : ℕ}
    (hA : ∀ i j, RationalHeightLE (A i j) H) :
    matrixDenominator A ≤ H ^ (Fintype.card ι * Fintype.card κ) := by
  simpa only [matrixDenominator, Fintype.card_prod] using
    arrayDenominator_le (fun ij : ι × κ => A ij.1 ij.2) (fun ij => (hA ij.1 ij.2).2)

theorem clearedMatrix_cast (A : Matrix ι κ ℚ) :
    (clearedMatrix A).map (Int.castRingHom ℚ) = (matrixDenominator A : ℚ) • A := by
  ext i j
  exact clearedArray_cast (fun ij : ι × κ => A ij.1 ij.2) (i, j)

theorem integralVector_denominator_mulVec (A : Matrix ι κ ℚ) (x : κ → ℚ)
    (hx : IntegralVector x) :
    IntegralVector ((matrixDenominator A : ℚ) • (A *ᵥ x)) := by
  obtain ⟨z, hz⟩ := hx
  have hx_eq : x = fun i => (z i : ℚ) := funext hz
  refine ⟨(clearedMatrix A) *ᵥ z, fun i => ?_⟩
  rw [← Matrix.smul_mulVec, ← clearedMatrix_cast, hx_eq]
  exact ((Int.castRingHom ℚ).map_mulVec (clearedMatrix A) z i).symm

theorem exists_bounded_rational_left_inverse (B : Matrix ι κ ℚ)
    (hli : LinearIndependent ℚ B.col) {H : ℕ} (hH : 1 ≤ H)
    (hB : ∀ i j, RationalHeightLE (B i j) H) :
    ∃ C : Matrix κ ι ℚ, C * B = 1 ∧
      ∀ i j, RationalHeightLE (C i j) (rationalSolveHeight (Fintype.card κ) H) := by
  have hsurj : Function.Surjective Bᵀ.mulVec :=
    mulVec_surjective_of_independent_rows Bᵀ hli
  obtain ⟨S, hS, hSH⟩ := exists_bounded_rational_section Bᵀ hsurj hH (fun i j => hB j i)
  refine ⟨Sᵀ, ?_, fun i j => hSH j i⟩
  simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] using
    congrArg Matrix.transpose hS

theorem rational_embedding_grid_bounds (B : Matrix ι κ ℚ) (C : Matrix κ ι ℚ)
    (hCB : C * B = 1) :
    scaledIntegerGrid (matrixDenominator B * matrixDenominator C) ⊆
      {x | IntegralVector (B *ᵥ x)} ∧
    {x | IntegralVector (B *ᵥ x)} ⊆
      denominatorGrid (matrixDenominator B * matrixDenominator C) := by
  constructor
  · rintro x ⟨z, rfl⟩
    have hz : IntegralVector (fun i => (z i : ℚ)) := ⟨z, fun _ => rfl⟩
    have h := (integralVector_denominator_mulVec B _ hz).nat_smul (matrixDenominator C)
    simpa only [Set.mem_ofPred_eq, Matrix.mulVec_smul, smul_smul, Nat.cast_mul, mul_comm] using h
  · intro x hx
    have h := (integralVector_denominator_mulVec C (B *ᵥ x) hx).nat_smul (matrixDenominator B)
    rw [Matrix.mulVec_mulVec, hCB, Matrix.one_mulVec] at h
    simpa only [denominatorGrid, Set.mem_ofPred_eq, smul_smul, Nat.cast_mul] using h

theorem exists_bounded_subspace_grid (B : Matrix ι κ ℚ)
    (hli : LinearIndependent ℚ B.col) {H : ℕ} (hH : 1 ≤ H)
    (hB : ∀ i j, RationalHeightLE (B i j) H) :
    ∃ L : ℕ, 0 < L ∧
      L ≤ H ^ (Fintype.card ι * Fintype.card κ) *
        rationalSolveHeight (Fintype.card κ) H ^ (Fintype.card κ * Fintype.card ι) ∧
      scaledIntegerGrid L ⊆ {x | IntegralVector (B *ᵥ x)} ∧
      {x | IntegralVector (B *ᵥ x)} ⊆ denominatorGrid L := by
  obtain ⟨C, hCB, hC⟩ := exists_bounded_rational_left_inverse B hli hH hB
  exact ⟨matrixDenominator B * matrixDenominator C,
    Nat.mul_pos (matrixDenominator_pos B) (matrixDenominator_pos C),
    Nat.mul_le_mul (matrixDenominator_le B hB) (matrixDenominator_le C hC),
    rational_embedding_grid_bounds B C hCB⟩

def integerGridImage (D : Matrix κ ι ℚ) : Set (κ → ℚ) :=
  {x | ∃ z : ι → ℤ, x = D *ᵥ (fun i => (z i : ℚ))}

theorem rational_quotient_grid_bounds (D : Matrix κ ι ℚ) (S : Matrix ι κ ℚ)
    (hDS : D * S = 1) :
    scaledIntegerGrid (matrixDenominator D * matrixDenominator S) ⊆ integerGridImage D ∧
      integerGridImage D ⊆ denominatorGrid (matrixDenominator D * matrixDenominator S) := by
  constructor
  · intro x hx
    have hxS : IntegralVector (S *ᵥ x) :=
      (rational_embedding_grid_bounds S D hDS).1 (by simpa only [Nat.mul_comm] using hx)
    obtain ⟨z, hz⟩ := hxS
    refine ⟨z, ?_⟩
    rw [← funext hz, Matrix.mulVec_mulVec, hDS, Matrix.one_mulVec]
  · rintro x ⟨z, rfl⟩
    have hz : IntegralVector (fun i => (z i : ℚ)) := ⟨z, fun _ => rfl⟩
    have h := (integralVector_denominator_mulVec D _ hz).nat_smul (matrixDenominator S)
    simpa only [denominatorGrid, Set.mem_ofPred_eq, smul_smul, Nat.cast_mul, mul_comm] using h

theorem exists_bounded_quotient_grid (D : Matrix κ ι ℚ)
    (hsurj : Function.Surjective D.mulVec) {H : ℕ} (hH : 1 ≤ H)
    (hD : ∀ i j, RationalHeightLE (D i j) H) :
    ∃ L : ℕ, 0 < L ∧
      L ≤ H ^ (Fintype.card κ * Fintype.card ι) *
        rationalSolveHeight (Fintype.card κ) H ^ (Fintype.card ι * Fintype.card κ) ∧
      scaledIntegerGrid L ⊆ integerGridImage D ∧ integerGridImage D ⊆ denominatorGrid L := by
  obtain ⟨S, hDS, hS⟩ := exists_bounded_rational_section D hsurj hH hD
  exact ⟨matrixDenominator D * matrixDenominator S,
    Nat.mul_pos (matrixDenominator_pos D) (matrixDenominator_pos S),
    Nat.mul_le_mul (matrixDenominator_le D hD) (matrixDenominator_le S hS),
    rational_quotient_grid_bounds D S hDS⟩

end Erdos3

end

section

namespace Erdos3

theorem rational_grid_height_le_exp (n d H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (hd : (d : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    ((H ^ (n * d) * rationalSolveHeight d H ^ (d * n) : ℕ) : ℝ) ≤
      Real.exp ((p + 2) ^ 8) := by
  have hsolve := rationalSolveHeight_le_budget d H hp hd hH
  have hA := pow_le_pow_left₀ (Nat.cast_nonneg H) hH (n * d)
  have hC := pow_le_pow_left₀ (Nat.cast_nonneg (rationalSolveHeight d H)) hsolve (d * n)
  rw [← Real.exp_nat_mul] at hA hC
  have hlog : p + (p + 2) ^ 5 ≤ (p + 2) ^ 6 := by
    have hp5 := le_power_budget hp (by decide : 1 ≤ 5)
    calc
      _ ≤ 2 * (p + 2) ^ 5 := by linarith
      _ ≤ (p + 2) * (p + 2) ^ 5 :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by ring
  push_cast
  calc
    _ ≤ Real.exp ((n * d : ℕ) * p) * Real.exp ((d * n : ℕ) * (p + 2) ^ 5) :=
      mul_le_mul hA hC (by positivity) (by positivity)
    _ = Real.exp ((n : ℝ) * d * (p + (p + 2) ^ 5)) := by
      rw [← Real.exp_add]; congr 1; push_cast; ring
    _ ≤ Real.exp ((p + 2) ^ 2 * (p + 2) ^ 6) := by
      apply Real.exp_le_exp.mpr
      apply mul_le_mul _ hlog (by positivity) (by positivity)
      calc
        (n : ℝ) * d ≤ (p + 2) * (p + 2) := by gcongr <;> linarith
        _ = (p + 2) ^ 2 := by ring
    _ = _ := by rw [← pow_add]

theorem exists_subspace_grid_exp_bound {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (B : Matrix ι κ ℚ) (hli : LinearIndependent ℚ B.col)
    {H : ℕ} (hHpos : 1 ≤ H) (hB : ∀ i j, RationalHeightLE (B i j) H)
    {p : ℝ} (hp : 0 ≤ p) (hn : (Fintype.card ι : ℝ) ≤ p)
    (hd : (Fintype.card κ : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    ∃ L : ℕ, 0 < L ∧ (L : ℝ) ≤ Real.exp ((p + 2) ^ 8) ∧
      scaledIntegerGrid L ⊆ {x | IntegralVector (B.mulVec x)} ∧
      {x | IntegralVector (B.mulVec x)} ⊆ denominatorGrid L := by
  obtain ⟨L, hL, hbound, hinner, houter⟩ := exists_bounded_subspace_grid B hli hHpos hB
  refine ⟨L, hL, ?_, hinner, houter⟩
  exact (show (L : ℝ) ≤
    ((H ^ (Fintype.card ι * Fintype.card κ) *
      rationalSolveHeight (Fintype.card κ) H ^ (Fintype.card κ * Fintype.card ι) : ℕ) : ℝ) from
    by exact_mod_cast hbound).trans (rational_grid_height_le_exp _ _ _ hp hn hd hH)

theorem exists_quotient_grid_exp_bound {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (D : Matrix κ ι ℚ) (hsurj : Function.Surjective D.mulVec)
    {H : ℕ} (hHpos : 1 ≤ H) (hD : ∀ i j, RationalHeightLE (D i j) H)
    {p : ℝ} (hp : 0 ≤ p) (hn : (Fintype.card ι : ℝ) ≤ p)
    (hd : (Fintype.card κ : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    ∃ L : ℕ, 0 < L ∧ (L : ℝ) ≤ Real.exp ((p + 2) ^ 8) ∧
      scaledIntegerGrid L ⊆ integerGridImage D ∧ integerGridImage D ⊆ denominatorGrid L := by
  obtain ⟨L, hL, hbound, hinner, houter⟩ := exists_bounded_quotient_grid D hsurj hHpos hD
  refine ⟨L, hL, ?_, hinner, houter⟩
  have hcost := rational_grid_height_le_exp (Fintype.card ι) (Fintype.card κ) H hp hn hd hH
  have hbound' : (L : ℝ) ≤
      ((H ^ (Fintype.card ι * Fintype.card κ) *
        rationalSolveHeight (Fintype.card κ) H ^ (Fintype.card κ * Fintype.card ι) : ℕ) : ℝ) := by
    exact_mod_cast (by simpa only [Nat.mul_comm] using hbound)
  exact hbound'.trans hcost

end Erdos3

end

section

namespace Erdos3

theorem finite_card_rational_grid_box {ι : Type*} [Fintype ι]
    (S : Set (ι → ℚ)) (l N : ℕ) (hl : 0 < l) {B : ℝ}
    (hgrid : S ⊆ denominatorGrid l)
    (hbound : ∀ x ∈ S, ∀ i, |(x i : ℝ)| ≤ B)
    (hN : (l : ℝ) * B ≤ N) :
    S.Finite ∧ S.ncard ≤ (2 * N + 1) ^ Fintype.card ι := by
  classical
  let z : S → ι → ℤ := fun x => Classical.choose (hgrid x.property)
  have hz (x : S) (i : ι) : (l : ℚ) * x.val i = (z x i : ℚ) :=
    Classical.choose_spec (hgrid x.property) i
  have hzi (x : S) (i : ι) : z x i ∈ Set.Icc (-(N : ℤ)) N := by
    have heq : (l : ℝ) * (x.val i : ℝ) = (z x i : ℝ) := by exact_mod_cast hz x i
    have hb : |(z x i : ℝ)| ≤ (N : ℝ) := by
      rw [← heq, abs_mul, abs_of_nonneg (Nat.cast_nonneg l)]
      exact (mul_le_mul_of_nonneg_left (hbound x x.property i) (Nat.cast_nonneg l)).trans hN
    apply abs_le.mp
    exact_mod_cast hb
  let f : S → (ι → Set.Icc (-(N : ℤ)) N) := fun x i => ⟨z x i, hzi x i⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    funext i
    have hi : z x i = z y i := congrArg Subtype.val (congrFun hxy i)
    apply mul_left_cancel₀ (show (l : ℚ) ≠ 0 by exact_mod_cast hl.ne')
    rw [hz, hz, hi]
  let : Finite S := Finite.of_injective f hf
  have hcardI : Fintype.card (Set.Icc (-(N : ℤ)) N) = 2 * N + 1 := by
    have h := Int.card_fintype_Icc_of_le (-(N : ℤ)) N (show -(N : ℤ) ≤ N + 1 by omega)
    omega
  refine ⟨Set.toFinite S, ?_⟩
  have hc := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_coe_set_eq, Nat.card_eq_fintype_card, Fintype.card_fun, hcardI] using hc

end Erdos3

end

section

namespace Erdos3

theorem scaledIntegerGrid_subset_of_dvd {ι : Type*} {l m : ℕ} (h : l ∣ m) :
    (scaledIntegerGrid m : Set (ι → ℚ)) ⊆ scaledIntegerGrid l := by
  obtain ⟨k, rfl⟩ := h
  rintro x ⟨z, rfl⟩
  refine ⟨fun i => (k : ℤ) * z i, ?_⟩
  ext i
  simp only [Pi.smul_apply, smul_eq_mul, Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
  ring

theorem denominatorGrid_subset_of_dvd {ι : Type*} {l m : ℕ} (h : l ∣ m) :
    (denominatorGrid l : Set (ι → ℚ)) ⊆ denominatorGrid m := by
  obtain ⟨k, rfl⟩ := h
  intro x hx
  have hmul := IntegralVector.nat_smul hx k
  change IntegralVector (((l * k : ℕ) : ℚ) • x)
  simpa only [smul_smul, Nat.cast_mul, mul_comm] using hmul

end Erdos3

end

section

namespace Erdos3

open Topology

variable {ι : Type*}

def realIntegerGrid : Set (ι → ℝ) := Set.range (fun z : ι → ℤ => fun i => (z i : ℝ))

def realDenominatorGrid (l : ℕ) : Set (ι → ℝ) :=
  (fun x : ι → ℝ => (l : ℝ) • x) ⁻¹' realIntegerGrid

theorem isClosedEmbedding_integerVectors :
    IsClosedEmbedding (fun z : ι → ℤ => fun i => (z i : ℝ)) :=
  IsClosedEmbedding.piMap (fun _ => Real.isClosedEmbedding_intCast)

theorem isClosed_realIntegerGrid : IsClosed (realIntegerGrid : Set (ι → ℝ)) :=
  isClosedEmbedding_integerVectors.isClosed_range

theorem isClosed_realDenominatorGrid (l : ℕ) :
    IsClosed (realDenominatorGrid l : Set (ι → ℝ)) :=
  isClosed_realIntegerGrid.preimage (continuous_const_smul (l : ℝ))

theorem real_cast_mem_denominatorGrid_iff (l : ℕ) (x : ι → ℚ) :
    (fun i => (x i : ℝ)) ∈ realDenominatorGrid l ↔ x ∈ denominatorGrid l := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, fun i => ?_⟩
    have hi := (congrFun hz i).symm
    change (l : ℝ) * (x i : ℝ) = (z i : ℝ) at hi
    change (l : ℚ) * x i = (z i : ℚ)
    exact_mod_cast hi
  · rintro ⟨z, hz⟩
    refine ⟨z, funext (fun i => ?_)⟩
    have hi := hz i
    change (l : ℚ) * x i = (z i : ℚ) at hi
    change (z i : ℝ) = (l : ℝ) * (x i : ℝ)
    exact_mod_cast hi.symm

variable [Finite ι]

theorem isDiscrete_realIntegerGrid : IsDiscrete (realIntegerGrid : Set (ι → ℝ)) :=
  isClosedEmbedding_integerVectors.isEmbedding.isInducing.isDiscrete_range

theorem isDiscrete_realDenominatorGrid (l : ℕ) (hl : 0 < l) :
    IsDiscrete (realDenominatorGrid l : Set (ι → ℝ)) := by
  apply isDiscrete_realIntegerGrid.preimage (continuous_const_smul (l : ℝ)).continuousOn
  exact (Homeomorph.smulOfNeZero (α := ι → ℝ) (l : ℝ) (by exact_mod_cast hl.ne')).injective

theorem closed_discrete_of_real_grid {S : Set (ι → ℝ)} (l : ℕ) (hl : 0 < l)
    (hS : S ⊆ realDenominatorGrid l) : IsClosed S ∧ IsDiscrete S :=
  ⟨isClosed_of_subset_discrete_closed hS (isDiscrete_realDenominatorGrid l hl)
    (isClosed_realDenominatorGrid l), (isDiscrete_realDenominatorGrid l hl).mono hS⟩

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem scaled_grid_mulVec (B : Matrix ι κ ℚ) (l : ℕ) (x : κ → ℚ)
    (hx : IntegralVector (B *ᵥ x)) : B *ᵥ ((l : ℚ) • x) ∈ scaledIntegerGrid l := by
  obtain ⟨z, hz⟩ := hx
  exact ⟨z, by rw [Matrix.mulVec_smul, funext hz]⟩

theorem rational_preimage_grid_transport (B : Matrix ι κ ℚ) (C : Matrix κ ι ℚ)
    (hCB : C * B = 1) (l : ℕ) (Γ : Set (ι → ℚ))
    (hinner : scaledIntegerGrid l ⊆ Γ) (houter : Γ ⊆ denominatorGrid l) :
    scaledIntegerGrid (l * (matrixDenominator B * matrixDenominator C)) ⊆ B.mulVec ⁻¹' Γ ∧
      B.mulVec ⁻¹' Γ ⊆ denominatorGrid (l * (matrixDenominator B * matrixDenominator C)) := by
  constructor
  · rintro x ⟨z, rfl⟩
    apply hinner
    have hz : ((matrixDenominator B * matrixDenominator C : ℕ) : ℚ) •
        (fun i => (z i : ℚ)) ∈ scaledIntegerGrid (matrixDenominator B * matrixDenominator C) :=
      ⟨z, rfl⟩
    have h := scaled_grid_mulVec B l _ ((rational_embedding_grid_bounds B C hCB).1 hz)
    simpa only [smul_smul, Nat.cast_mul] using h
  · intro x hx
    have h := (integralVector_denominator_mulVec C ((l : ℚ) • (B *ᵥ x)) (houter hx)).nat_smul
      (matrixDenominator B)
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hCB, Matrix.one_mulVec] at h
    simpa only [denominatorGrid, Set.mem_ofPred_eq, smul_smul, Nat.cast_mul,
      mul_assoc, mul_left_comm, mul_comm] using h

theorem rational_image_grid_transport (D : Matrix κ ι ℚ) (S : Matrix ι κ ℚ)
    (hDS : D * S = 1) (l : ℕ) (Γ : Set (ι → ℚ))
    (hinner : scaledIntegerGrid l ⊆ Γ) (houter : Γ ⊆ denominatorGrid l) :
    scaledIntegerGrid (l * (matrixDenominator D * matrixDenominator S)) ⊆ D.mulVec '' Γ ∧
      D.mulVec '' Γ ⊆ denominatorGrid (l * (matrixDenominator D * matrixDenominator S)) := by
  constructor
  · intro y hy
    have hS := (rational_preimage_grid_transport S D hDS l Γ hinner houter).1
      (by simpa only [Nat.mul_comm] using hy)
    refine ⟨S *ᵥ y, hS, ?_⟩
    rw [Matrix.mulVec_mulVec, hDS, Matrix.one_mulVec]
  · rintro y ⟨x, hx, rfl⟩
    have h := (integralVector_denominator_mulVec D ((l : ℚ) • x) (houter hx)).nat_smul
      (matrixDenominator S)
    rw [Matrix.mulVec_smul] at h
    simpa only [denominatorGrid, Set.mem_ofPred_eq, smul_smul, Nat.cast_mul,
      mul_assoc, mul_left_comm, mul_comm] using h

theorem grid_allowance_mul_le_exp {p : ℝ} (hp : 0 ≤ p) {l K : ℕ}
    (hl : (l : ℝ) ≤ Real.exp p) (hK : (K : ℝ) ≤ Real.exp ((p + 2) ^ 8)) :
    ((l * K : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 9) := by
  calc
    _ ≤ Real.exp p * Real.exp ((p + 2) ^ 8) := by
      rw [Nat.cast_mul]
      exact mul_le_mul hl hK (Nat.cast_nonneg _) (by positivity)
    _ = Real.exp (p + (p + 2) ^ 8) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((p + 2) ^ 9) := by
      apply Real.exp_le_exp.mpr
      have hp8 := le_power_budget hp (by decide : 1 ≤ 8)
      calc
        _ ≤ 2 * (p + 2) ^ 8 := by linarith
        _ ≤ (p + 2) * (p + 2) ^ 8 :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = _ := by ring

theorem exists_preimage_grid_exp_bound (B : Matrix ι κ ℚ)
    (hli : LinearIndependent ℚ B.col) {H l : ℕ} (hHpos : 1 ≤ H) (hlpos : 0 < l)
    (hB : ∀ i j, RationalHeightLE (B i j) H) (Γ : Set (ι → ℚ))
    (hinner : scaledIntegerGrid l ⊆ Γ) (houter : Γ ⊆ denominatorGrid l)
    {p : ℝ} (hp : 0 ≤ p) (hn : (Fintype.card ι : ℝ) ≤ p)
    (hd : (Fintype.card κ : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p)
    (hl : (l : ℝ) ≤ Real.exp p) :
    ∃ L : ℕ, 0 < L ∧ (L : ℝ) ≤ Real.exp ((p + 2) ^ 9) ∧
      scaledIntegerGrid L ⊆ B.mulVec ⁻¹' Γ ∧ B.mulVec ⁻¹' Γ ⊆ denominatorGrid L := by
  obtain ⟨C, hCB, hC⟩ := exists_bounded_rational_left_inverse B hli hHpos hB
  have hK : ((matrixDenominator B * matrixDenominator C : ℕ) : ℝ) ≤
      Real.exp ((p + 2) ^ 8) := by
    have hc := Nat.mul_le_mul (matrixDenominator_le B hB) (matrixDenominator_le C hC)
    exact (show ((matrixDenominator B * matrixDenominator C : ℕ) : ℝ) ≤
      ((H ^ (Fintype.card ι * Fintype.card κ) *
        rationalSolveHeight (Fintype.card κ) H ^ (Fintype.card κ * Fintype.card ι) : ℕ) : ℝ) from
      by exact_mod_cast hc).trans (rational_grid_height_le_exp _ _ _ hp hn hd hH)
  exact ⟨l * (matrixDenominator B * matrixDenominator C),
    Nat.mul_pos hlpos (Nat.mul_pos (matrixDenominator_pos B) (matrixDenominator_pos C)),
    grid_allowance_mul_le_exp hp hl hK, rational_preimage_grid_transport B C hCB l Γ hinner houter⟩

theorem exists_image_grid_exp_bound (D : Matrix κ ι ℚ)
    (hsurj : Function.Surjective D.mulVec) {H l : ℕ} (hHpos : 1 ≤ H) (hlpos : 0 < l)
    (hD : ∀ i j, RationalHeightLE (D i j) H) (Γ : Set (ι → ℚ))
    (hinner : scaledIntegerGrid l ⊆ Γ) (houter : Γ ⊆ denominatorGrid l)
    {p : ℝ} (hp : 0 ≤ p) (hn : (Fintype.card ι : ℝ) ≤ p)
    (hd : (Fintype.card κ : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p)
    (hl : (l : ℝ) ≤ Real.exp p) :
    ∃ L : ℕ, 0 < L ∧ (L : ℝ) ≤ Real.exp ((p + 2) ^ 9) ∧
      scaledIntegerGrid L ⊆ D.mulVec '' Γ ∧ D.mulVec '' Γ ⊆ denominatorGrid L := by
  obtain ⟨S, hDS, hS⟩ := exists_bounded_rational_section D hsurj hHpos hD
  have hK : ((matrixDenominator D * matrixDenominator S : ℕ) : ℝ) ≤
      Real.exp ((p + 2) ^ 8) := by
    have hc := Nat.mul_le_mul (matrixDenominator_le D hD) (matrixDenominator_le S hS)
    have hc' : (matrixDenominator D * matrixDenominator S : ℕ) ≤
        H ^ (Fintype.card ι * Fintype.card κ) *
          rationalSolveHeight (Fintype.card κ) H ^ (Fintype.card κ * Fintype.card ι) := by
      simpa only [Nat.mul_comm] using hc
    exact (show ((matrixDenominator D * matrixDenominator S : ℕ) : ℝ) ≤
      ((H ^ (Fintype.card ι * Fintype.card κ) *
        rationalSolveHeight (Fintype.card κ) H ^ (Fintype.card κ * Fintype.card ι) : ℕ) : ℝ) from
      by exact_mod_cast hc').trans (rational_grid_height_le_exp _ _ _ hp hn hd hH)
  exact ⟨l * (matrixDenominator D * matrixDenominator S),
    Nat.mul_pos hlpos (Nat.mul_pos (matrixDenominator_pos D) (matrixDenominator_pos S)),
    grid_allowance_mul_le_exp hp hl hK, rational_image_grid_transport D S hDS l Γ hinner houter⟩

end Erdos3

end

section

namespace Erdos3

theorem grid_box_count_le_exp (C d l : ℕ) (hC : 2 ≤ C) {p : ℝ}
    (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) (hl : (l : ℝ) ≤ Real.exp p) :
    (((2 * ⌈(l : ℝ) * Real.exp ((p + C) ^ C)⌉₊ + 1) ^ d : ℕ) : ℝ) ≤
      Real.exp ((p + (C + 5)) ^ (C + 5)) := by
  let t := p + (C + 5 : ℕ)
  have ht : 5 ≤ t := by dsimp [t]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) C]
  have ht1 : 1 ≤ t := by linarith
  have hpt : p ≤ t := by dsimp [t]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) C]
  have hshift : p + C ≤ t := by dsimp [t]; push_cast; linarith
  have hpT : p ≤ t ^ C := by
    apply hpt.trans
    simpa only [pow_one] using pow_le_pow_right₀ ht1 (show 1 ≤ C by omega)
  have hprod : (l : ℝ) * Real.exp ((p + C) ^ C) ≤ Real.exp (t ^ (C + 1)) := by
    calc
      _ ≤ Real.exp (t ^ C) * Real.exp (t ^ C) :=
        mul_le_mul (hl.trans (Real.exp_le_exp.mpr hpT))
          (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by positivity) hshift C))
          (by positivity) (by positivity)
      _ = Real.exp (2 * t ^ C) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        rw [pow_succ]
        nlinarith [mul_le_mul_of_nonneg_right ht (by positivity : 0 ≤ t ^ C)]
  have hceil := (Nat.ceil_lt_add_one
    (show 0 ≤ (l : ℝ) * Real.exp ((p + C) ^ C) by positivity)).le
  have hone : 1 ≤ Real.exp (t ^ (C + 1)) := Real.one_le_exp (by positivity)
  have hcount : ((2 * ⌈(l : ℝ) * Real.exp ((p + C) ^ C)⌉₊ + 1 : ℕ) : ℝ) ≤
      Real.exp (t ^ (C + 2)) := by
    have hfive : (5 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
    calc
      _ ≤ 5 * Real.exp (t ^ (C + 1)) := by push_cast; linarith
      _ ≤ Real.exp 4 * Real.exp (t ^ (C + 1)) :=
        mul_le_mul_of_nonneg_right hfive (by positivity)
      _ = Real.exp (4 + t ^ (C + 1)) := (Real.exp_add _ _).symm
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        rw [show C + 2 = (C + 1) + 1 by omega, pow_succ t (C + 1)]
        have hpow : 1 ≤ t ^ (C + 1) := one_le_pow₀ ht1
        nlinarith [mul_le_mul_of_nonneg_right ht (by positivity : 0 ≤ t ^ (C + 1))]
  rw [Nat.cast_pow]
  calc
    _ ≤ (Real.exp (t ^ (C + 2))) ^ d := pow_le_pow_left₀ (Nat.cast_nonneg _) hcount d
    _ = Real.exp ((d : ℝ) * t ^ (C + 2)) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (t ^ (C + 3)) := by
      apply Real.exp_le_exp.mpr
      rw [show C + 3 = (C + 2) + 1 by omega, pow_succ' t (C + 2)]
      exact mul_le_mul_of_nonneg_right (hd.trans hpt) (by positivity)
    _ ≤ Real.exp (t ^ (C + 5)) := Real.exp_le_exp.mpr (pow_le_pow_right₀ ht1 (by omega))
    _ = _ := by simp [t]

end Erdos3

end

section

namespace Erdos3

theorem finite_index_of_bounded_grid_representatives {G ι : Type*} [Group G] [Fintype ι]
    (f : G → ι → ℚ) (hf : Function.Injective f) (Γ Λ : Subgroup G)
    (l N : ℕ) (hl : 0 < l) {B : ℝ}
    (hgrid : ∀ g ∈ Γ, f g ∈ denominatorGrid l) (hN : (l : ℝ) * B ≤ N)
    (hrep : ∀ g ∈ Γ, ∃ r ∈ Γ, (∀ i, |(f r i : ℝ)| ≤ B) ∧
      ∃ γ ∈ Λ, g = r * γ) :
    (Λ.subgroupOf Γ).FiniteIndex ∧ Λ.relIndex Γ ≤ (2 * N + 1) ^ Fintype.card ι := by
  classical
  let R : Set G := {r | r ∈ Γ ∧ ∀ i, |(f r i : ℝ)| ≤ B}
  let S : Set (ι → ℚ) := f '' R
  have hS := finite_card_rational_grid_box S l N hl
    (by rintro _ ⟨r, hr, rfl⟩; exact hgrid r hr.1)
    (by rintro _ ⟨r, hr, rfl⟩ i; exact hr.2 i) hN
  let : Finite S := hS.1.to_subtype
  let fR : R → S := fun r => ⟨f r.val, ⟨r.val, r.property, rfl⟩⟩
  have hfR : Function.Injective fR := by
    intro x y hxy
    exact Subtype.ext (hf (congrArg Subtype.val hxy))
  let : Finite R := Finite.of_injective fR hfR
  let q : R → (Γ ⧸ Λ.subgroupOf Γ) := fun r => QuotientGroup.mk (⟨r.val, r.property.1⟩ : Γ)
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨r, hr, hb, γ, hγ, heq⟩ := hrep g g.property
    refine ⟨⟨r, hr, hb⟩, ?_⟩
    apply QuotientGroup.eq.mpr
    change r⁻¹ * g.val ∈ Λ
    rw [heq, inv_mul_cancel_left]
    exact hγ
  let : Finite (Γ ⧸ Λ.subgroupOf Γ) := Finite.of_surjective q hq
  refine ⟨Subgroup.finiteIndex_of_finite_quotient, ?_⟩
  exact (Nat.card_le_card_of_surjective q hq).trans
    ((Nat.card_le_card_of_injective fR hfR).trans hS.2)

end Erdos3

end

section

namespace Erdos3

theorem grid_det_integer_multiple {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (l : ℕ)
    (hA : ∀ j, (fun i => A i j) ∈ realDenominatorGrid l) :
    ∃ z : ℤ, (l : ℝ) ^ Fintype.card ι * A.det = (z : ℝ) := by
  choose z hz using hA
  let B : Matrix ι ι ℤ := fun i j => z j i
  have he : B.map (Int.castRingHom ℝ) = (l : ℝ) • A := by
    ext i j
    exact congrFun (hz j) i
  refine ⟨B.det, ?_⟩
  rw [← Matrix.det_smul, ← he]
  exact ((Int.castRingHom ℝ).map_det B).symm

theorem one_div_pow_le_abs_grid_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (l : ℕ) (hl : 0 < l)
    (hA : ∀ j, (fun i => A i j) ∈ realDenominatorGrid l) (hne : A.det ≠ 0) :
    1 / (l : ℝ) ^ Fintype.card ι ≤ |A.det| := by
  have hlpos : (0 : ℝ) < l := by exact_mod_cast hl
  obtain ⟨z, hz⟩ := grid_det_integer_multiple A l hA
  have hz0 : z ≠ 0 := by
    intro hz0
    rw [hz0, Int.cast_zero] at hz
    exact (mul_ne_zero (pow_ne_zero _ hlpos.ne') hne) hz
  have habs : (1 : ℝ) ≤ |(z : ℝ)| := by exact_mod_cast Int.one_le_abs hz0
  rw [← hz, abs_mul, abs_of_pos (pow_pos hlpos _)] at habs
  exact (div_le_iff₀ (pow_pos hlpos _)).mpr (by simpa only [mul_comm] using habs)

end Erdos3

end

section

namespace Erdos3

theorem realDenominatorGrid_nat_smul_iff {ι : Type*} (l m : ℕ) (x : ι → ℝ) :
    (l : ℝ) • x ∈ realDenominatorGrid m ↔ x ∈ realDenominatorGrid (m * l) := by
  change (m : ℝ) • ((l : ℝ) • x) ∈ realIntegerGrid ↔ ((m * l : ℕ) : ℝ) • x ∈ realIntegerGrid
  rw [Nat.cast_mul, mul_smul]

theorem linearMap_grid_of_integer {ι κ V : Type*} [AddCommGroup V] [Module ℝ V]
    (c : V →ₗ[ℝ] (ι → ℝ)) (f : V →ₗ[ℝ] (κ → ℝ)) (δ : ℕ)
    (hf : ∀ x, c x ∈ realDenominatorGrid 1 → f x ∈ realDenominatorGrid δ)
    (l : ℕ) (x : V) (hx : c x ∈ realDenominatorGrid l) :
    f x ∈ realDenominatorGrid (δ * l) := by
  have hc : c ((l : ℝ) • x) ∈ realDenominatorGrid 1 := by
    rw [map_smul, realDenominatorGrid_nat_smul_iff, one_mul]
    exact hx
  have h := hf ((l : ℝ) • x) hc
  rw [map_smul, realDenominatorGrid_nat_smul_iff] at h
  exact h

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix

variable {ι κ V : Type*} [Fintype ι] [Fintype κ] [AddCommGroup V] [Module ℚ V]

noncomputable def spanningCoordinateMatrix (e : Basis ι ℚ V) (v : κ → V) : Matrix ι κ ℚ :=
  fun i j => e.repr (v j) i

theorem spanningCoordinateMatrix_mulVec (e : Basis ι ℚ V) (v : κ → V) (t : κ → ℚ) :
    e.equivFun (∑ j, t j • v j) = spanningCoordinateMatrix e v *ᵥ t := by
  ext i
  simp [spanningCoordinateMatrix, Matrix.mulVec, dotProduct, mul_comm]

noncomputable def rationalSpanGridStep (e : Basis ι ℚ V) (v : κ → V) (l : ℕ) : ℕ :=
  l * matrixDenominator (spanningCoordinateMatrix e v)

theorem rationalSpanGridStep_pos (e : Basis ι ℚ V) (v : κ → V) (l : ℕ) (hl : 0 < l) :
    0 < rationalSpanGridStep e v l :=
  Nat.mul_pos hl (matrixDenominator_pos _)

theorem rationalSpanGridStep_le (e : Basis ι ℚ V) (v : κ → V) (l : ℕ) {H : ℕ}
    (hv : ∀ i j, RationalHeightLE (e.repr (v j) i) H) :
    rationalSpanGridStep e v l ≤ l * H ^ (Fintype.card ι * Fintype.card κ) :=
  Nat.mul_le_mul_left l (matrixDenominator_le _ hv)

theorem rationalSpanGridStep_combination (e : Basis ι ℚ V) (v : κ → V) (l : ℕ) (z : κ → ℤ) :
    e.equivFun (∑ j, ((z j : ℚ) * (rationalSpanGridStep e v l : ℚ)) • v j) ∈ scaledIntegerGrid l := by
  classical
  let B := spanningCoordinateMatrix e v
  have hz : IntegralVector (fun j => (z j : ℚ)) := ⟨z, fun _ => rfl⟩
  have hB : IntegralVector (B *ᵥ ((matrixDenominator B : ℚ) • (fun j => (z j : ℚ)))) := by
    rw [Matrix.mulVec_smul]
    exact integralVector_denominator_mulVec B _ hz
  have heq : (fun j => (z j : ℚ) * (rationalSpanGridStep e v l : ℚ)) =
      (l : ℚ) • ((matrixDenominator B : ℚ) • (fun j => (z j : ℚ))) := by
    ext j
    simp only [rationalSpanGridStep, Nat.cast_mul, Pi.smul_apply, smul_eq_mul, B]
    ring
  rw [spanningCoordinateMatrix_mulVec, heq]
  exact scaled_grid_mulVec B l _ hB

end Erdos3

end

end OAI
