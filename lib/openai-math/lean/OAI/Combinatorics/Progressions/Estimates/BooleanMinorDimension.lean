/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import OAI.Combinatorics.Progressions.Linear.RealKernelJetInverse
import OAI.Combinatorics.Progressions.Polynomial.BooleanBlockCoefficientPhase
import OAI.Combinatorics.Progressions.Polynomial.EmbeddedMatrixDeterminantPolynomial

namespace OAI

section

namespace Erdos3

open scoped BigOperators ContDiff

variable {B F α O : Type*} [Fintype B] [Fintype F] [Fintype α]
  [DecidableEq B] [DecidableEq F] [DecidableEq α]

noncomputable def booleanSamplerMap (c : B → ℝ) (sets : O → Finset α)
    (a : BlockParameter B F α → ℝ) (o : O) : ℝ :=
  MvPolynomial.eval a (booleanSamplerPolynomial c (sets o))

noncomputable def booleanSelectedMinor (c : B → ℝ) (sets : O → Finset α)
    (block : O → B) (v : F) (r : O → Option α) : Matrix O O (MvPolynomial (BlockParameter B F α) ℝ) :=
  fun row col => MvPolynomial.pderiv (block col, v, r col) (booleanSamplerPolynomial c (sets row))

omit [DecidableEq B] [DecidableEq F] in
theorem booleanSamplerMap_formula (c : B → ℝ) (sets : O → Finset α)
    (a : BlockParameter B F α → ℝ) (o : O) :
    booleanSamplerMap c sets a o = booleanCoefficient
      (fun t => ∑ b : B, c b * ∏ k : F, ∑ r : Option α, (booleanFeature r t : ℝ) * a (b, k, r)) (sets o) := by
  simp only [booleanSamplerMap, booleanSamplerPolynomial, booleanCoefficient_map, map_sum,
    map_mul, MvPolynomial.eval_C, booleanBlockPolynomial, map_prod, booleanAffinePolynomial_eval]

omit [DecidableEq B] [DecidableEq F] in
theorem booleanSamplerMap_contDiff [Fintype O] (c : B → ℝ) (sets : O → Finset α) :
    ContDiff ℝ ∞ (booleanSamplerMap (F := F) c sets) :=
  contDiff_pi.mpr (fun o => mvPolynomial_contDiff_eval (booleanSamplerPolynomial c (sets o)))

theorem booleanSelectedMinor_degreeOf_le (c : B → ℝ) (sets : O → Finset α)
    (block : O → B) (v : F) (r : O → Option α) (row col : O) (j : BlockParameter B F α) :
    (booleanSelectedMinor c sets block v r row col).degreeOf j ≤ Fintype.card F - 1 := by
  unfold booleanSelectedMinor
  rw [booleanSamplerPolynomial_pderiv]
  exact booleanSelectedColumn_degreeOf_le c (block col) v (r col) (sets row) j

theorem booleanSelectedMinor_fderiv [Fintype O] [DecidableEq O]
    (c : B → ℝ) (sets : O → Finset α) (block : O → B) (v : F) (r : O → Option α)
    (a : BlockParameter B F α → ℝ) (row col : O) :
    (fderiv ℝ (booleanSamplerMap (F := F) c sets) a (Pi.single (block col, v, r col) 1)) row =
      MvPolynomial.eval a (booleanSelectedMinor c sets block v r row col) := by
  have hd := (booleanSamplerMap_contDiff (F := F) c sets).differentiable (by norm_num)
  have h := mvPolynomial_fderiv_coordinate (booleanSamplerPolynomial (F := F) c (sets row)) a
    (block col, v, r col)
  change fderiv ℝ (fun x => booleanSamplerMap c sets x row) a (Pi.single (block col, v, r col) 1) = _ at h
  rw [fderiv_apply (hd a) row] at h
  exact h

theorem booleanSelectedMinor_specialization [DecidableEq O]
    (c : B → ℝ) (sets : O → Finset α) (hsets : Function.Injective sets) (block : O → B) (v : F)
    (label : B → F → Option α)
    (hlabel : ∀ o a, (∃ k, label (block o) k = some a) ↔ a ∈ sets o) :
    (booleanSelectedMinor c sets block v (fun o => label (block o) v)).map
      (MvPolynomial.eval (blockSpecialization label)) = Matrix.diagonal (fun o => c (block o)) := by
  ext row col
  change MvPolynomial.eval (blockSpecialization label)
    (MvPolynomial.pderiv (block col, v, label (block col) v) (booleanSamplerPolynomial c (sets row))) = _
  rw [booleanSamplerPolynomial_pderiv, booleanSelectedColumn_specialization c label
    (block col) v (sets col) (sets row) (hlabel col)]
  by_cases h : row = col
  · subst row
    simp
  · have hs : sets row ≠ sets col := fun he => h (hsets he)
    simp [h, hs]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem booleanFeature_abs_le_one {α : Type*} [DecidableEq α]
    (r : Option α) (t : Finset α) : |(booleanFeature r t : ℝ)| ≤ 1 := by
  cases r with
  | none => norm_num [booleanFeature]
  | some a => simp only [booleanFeature]; split_ifs <;> norm_num

theorem booleanCoefficient_abs_le {α : Type*} [DecidableEq α]
    (f : Finset α → ℝ) (s : Finset α) {M : ℝ}
    (hf : ∀ t ∈ s.powerset, |f t| ≤ M) :
    |booleanCoefficient f s| ≤ (2 : ℝ) ^ s.card * M := by
  unfold booleanCoefficient
  calc
    _ ≤ ∑ t ∈ s.powerset, |(-1 : ℝ) ^ (s \ t).card * f t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t ∈ s.powerset, M := by
      apply Finset.sum_le_sum
      intro t ht
      simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using hf t ht
    _ = _ := by simp

theorem booleanAffinePolynomial_eval_abs_le {B F α : Type*} [Fintype α] [DecidableEq α]
    (a : BlockParameter B F α → ℝ) (b : B) (v : F) (t : Finset α) {R : ℝ}
    (ha : ∀ j, |a j| ≤ R) :
    |MvPolynomial.eval a (booleanAffinePolynomial b v t)| ≤ ((Fintype.card α : ℝ) + 1) * R := by
  rw [booleanAffinePolynomial_eval]
  calc
    _ ≤ ∑ r : Option α, |(booleanFeature r t : ℝ) * a (b, v, r)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r : Option α, R := by
      apply Finset.sum_le_sum
      intro r _
      rw [abs_mul]
      simpa only [one_mul] using mul_le_mul (booleanFeature_abs_le_one r t)
        (ha (b, v, r)) (abs_nonneg _) zero_le_one
    _ = _ := by simp

theorem booleanSelectedColumn_eval_abs_le {B F α : Type*}
    [Fintype F] [Fintype α] [DecidableEq F] [DecidableEq α]
    (c : B → ℝ) (b : B) (v : F) (r : Option α) (s : Finset α)
    (a : BlockParameter B F α → ℝ) {R : ℝ} (ha : ∀ j, |a j| ≤ R) :
    |MvPolynomial.eval a (booleanSelectedColumn c b v r s)| ≤
      |c b| * ((2 : ℝ) ^ s.card *
        (((Fintype.card α : ℝ) + 1) * R) ^ (Fintype.card F - 1)) := by
  rw [booleanSelectedColumn, map_mul, MvPolynomial.eval_C, abs_mul, booleanCoefficient_map]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply booleanCoefficient_abs_le
  intro t _
  simp only [map_mul, MvPolynomial.eval_C, map_prod, abs_mul, Finset.abs_prod]
  calc
    _ ≤ 1 * ∏ _k ∈ Finset.univ.erase v, (((Fintype.card α : ℝ) + 1) * R) := by
      apply mul_le_mul (booleanFeature_abs_le_one r t)
      · exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
          (fun k _ => booleanAffinePolynomial_eval_abs_le a b k t ha)
      · exact Finset.prod_nonneg (fun _ _ => abs_nonneg _)
      · exact zero_le_one
    _ = _ := by simp

def productMinorEntryBound (q h : ℕ) (C R : ℝ) : ℝ :=
  C * ((2 : ℝ) ^ h * (((q : ℝ) + 1) * R) ^ (h - 1))

theorem productMinorEntryBound_nonneg (q h : ℕ) {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R) :
    0 ≤ productMinorEntryBound q h C R := by
  unfold productMinorEntryBound
  positivity

theorem booleanSelectedMinor_entry_bound {B O α : Type*}
    [Fintype B] [Fintype α] [DecidableEq B] [DecidableEq α]
    (c : B → ℝ) (sets : O → Finset α) (block : O → B) {h : ℕ}
    (v : Fin h) (r : O → Option α) (hcard : ∀ o, (sets o).card ≤ h)
    (a : BlockParameter B (Fin h) α → ℝ) {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hc : ∀ o, |c (block o)| ≤ C) (ha : ∀ j, |a j| ≤ R) (row col : O) :
    |MvPolynomial.eval a (booleanSelectedMinor c sets block v r row col)| ≤
      productMinorEntryBound (Fintype.card α) h C R := by
  unfold booleanSelectedMinor
  rw [booleanSamplerPolynomial_pderiv]
  have hcol := booleanSelectedColumn_eval_abs_le c (block col) v (r col) (sets row) a ha
  simp only [Fintype.card_fin] at hcol
  have htwo : (2 : ℝ) ^ (sets row).card ≤ 2 ^ h :=
    pow_le_pow_right₀ (by norm_num) (hcard row)
  have hpower : 0 ≤ (((Fintype.card α : ℝ) + 1) * R) ^ (h - 1) := by positivity
  exact hcol.trans (mul_le_mul (hc col) (mul_le_mul_of_nonneg_right htwo hpower)
    (mul_nonneg (by positivity) hpower) hC)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def restrictBlockParameters {B O F α : Type*} (block : O → B)
    (a : BlockParameter B F α → ℝ) (j : BlockParameter O F α) : ℝ :=
  a (block j.1, j.2.1, j.2.2)

theorem booleanSelectedColumn_restrict_eval {B O F α : Type*}
    [Fintype F] [Fintype α] [DecidableEq F] [DecidableEq α]
    (c : B → ℝ) (block : O → B) (a : BlockParameter B F α → ℝ)
    (o : O) (v : F) (r : Option α) (s : Finset α) :
    MvPolynomial.eval a (booleanSelectedColumn c (block o) v r s) =
      MvPolynomial.eval (restrictBlockParameters block a)
        (booleanSelectedColumn (c ∘ block) o v r s) := by
  simp only [booleanSelectedColumn, map_mul, MvPolynomial.eval_C, booleanCoefficient_map,
    map_prod, booleanAffinePolynomial_eval, Function.comp_apply, restrictBlockParameters]

theorem booleanSelectedMinor_restrict_eval {B O F α : Type*}
    [Fintype B] [Fintype O] [Fintype F] [Fintype α]
    [DecidableEq B] [DecidableEq O] [DecidableEq F] [DecidableEq α]
    (c : B → ℝ) (sets : O → Finset α) (block : O → B) (v : F) (r : O → Option α)
    (a : BlockParameter B F α → ℝ) :
    (booleanSelectedMinor c sets block v r).map (MvPolynomial.eval a) =
      (booleanSelectedMinor (c ∘ block) sets id v r).map
        (MvPolynomial.eval (restrictBlockParameters block a)) := by
  ext row col
  change MvPolynomial.eval a (MvPolynomial.pderiv (block col, v, r col) _) =
    MvPolynomial.eval (restrictBlockParameters block a) (MvPolynomial.pderiv (col, v, r col) _)
  rw [booleanSamplerPolynomial_pderiv, booleanSamplerPolynomial_pderiv]
  exact booleanSelectedColumn_restrict_eval c block a col v (r col) (sets row)

end Erdos3

end

section

namespace Erdos3

theorem exists_allocated_boolean_labels {B O α : Type*} [DecidableEq α]
    (sets : O → Finset α) (h : ℕ) (hcard : ∀ o, (sets o).card ≤ h)
    (block : O → B) (hblock : Function.Injective block) :
    ∃ label : B → Fin h → Option α,
      ∀ o a, (∃ k, label (block o) k = some a) ↔ a ∈ sets o := by
  classical
  choose label hlabel using fun o => exists_padded_boolean_labels (sets o) h (hcard o)
  refine ⟨Function.extend block label (fun _ _ => none), ?_⟩
  intro o a
  simpa only [hblock.extend_apply] using hlabel o a

theorem exists_boolean_minor_specialization {B O α : Type*}
    [Fintype B] [Fintype α] [DecidableEq B] [DecidableEq O] [DecidableEq α]
    (c : B → ℝ) (sets : O → Finset α) (hsets : Function.Injective sets)
    (h : ℕ) (hh : 0 < h) (hcard : ∀ o, (sets o).card ≤ h)
    (block : O → B) (hblock : Function.Injective block) :
    ∃ (r : O → Option α) (a₀ : BlockParameter B (Fin h) α → ℝ),
      (∀ j, |a₀ j| ≤ 1) ∧
      (booleanSelectedMinor c sets block (⟨0, hh⟩ : Fin h) r).map (MvPolynomial.eval a₀) =
        Matrix.diagonal (fun o => c (block o)) := by
  obtain ⟨label, hlabel⟩ := exists_allocated_boolean_labels sets h hcard block hblock
  let v : Fin h := ⟨0, hh⟩
  have habs : ∀ j : BlockParameter B (Fin h) α, |blockSpecialization label j| ≤ 1 :=
    blockSpecialization_abs_le_one label
  have hdiag := booleanSelectedMinor_specialization c sets hsets block v label hlabel
  refine ⟨(fun o => label (block o) v), blockSpecialization label, ?_, ?_⟩
  · exact habs
  · exact hdiag

theorem blockParameter_card {B α : Type*} [Fintype B] [Fintype α] (h : ℕ) :
    Fintype.card (BlockParameter B (Fin h) α) = Fintype.card B * (h * (Fintype.card α + 1)) := by
  simp only [BlockParameter, Fintype.card_prod, Fintype.card_fin, Fintype.card_option]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem booleanAffinePolynomial_pderiv_eval_abs_le {B F α : Type*}
    [Fintype α] [DecidableEq B] [DecidableEq F] [DecidableEq α]
    (a : BlockParameter B F α → ℝ) (b : B) (v : F) (t : Finset α)
    (j : BlockParameter B F α) :
    |MvPolynomial.eval a (MvPolynomial.pderiv j (booleanAffinePolynomial b v t))| ≤ 1 := by
  rcases j with ⟨b₀, v₀, r⟩
  rw [booleanAffinePolynomial_pderiv]
  split_ifs
  · simpa only [MvPolynomial.eval_C] using booleanFeature_abs_le_one r t
  · simp

theorem booleanSelectedColumn_pderiv_eval_abs_le {B F α : Type*}
    [Fintype F] [Fintype α] [DecidableEq B] [DecidableEq F] [DecidableEq α]
    (c : B → ℝ) (b : B) (v : F) (r : Option α) (s : Finset α)
    (a : BlockParameter B F α → ℝ) {R : ℝ} (hR : 1 ≤ R) (ha : ∀ j, |a j| ≤ R)
    (j : BlockParameter B F α) :
    |MvPolynomial.eval a (MvPolynomial.pderiv j (booleanSelectedColumn c b v r s))| ≤
      |c b| * ((2 : ℝ) ^ s.card *
        (Fintype.card F * (((Fintype.card α : ℝ) + 1) * R) ^ Fintype.card F)) := by
  let L : ℝ := ((Fintype.card α : ℝ) + 1) * R
  have hL : 1 ≤ L := by
    dsimp [L]
    have hq : 0 ≤ (Fintype.card α : ℝ) := Nat.cast_nonneg _
    nlinarith [mul_nonneg hq (zero_le_one.trans hR)]
  rw [booleanSelectedColumn, MvPolynomial.pderiv_C_mul, map_mul, MvPolynomial.eval_C,
    abs_mul, pderiv_booleanCoefficient, booleanCoefficient_map]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply booleanCoefficient_abs_le
  intro t _
  rw [MvPolynomial.pderiv_C_mul, map_mul, MvPolynomial.eval_C, abs_mul]
  have hd := mvPolynomial_prod_pderiv_eval_abs_le (Finset.univ.erase v)
    (fun k => booleanAffinePolynomial b k t) j a hL
    (fun k _ => booleanAffinePolynomial_eval_abs_le a b k t ha)
    (fun k _ => booleanAffinePolynomial_pderiv_eval_abs_le a b k t j)
  have hn : (Finset.univ.erase v).card ≤ Fintype.card F :=
    (Finset.card_erase_le).trans_eq (Finset.card_univ)
  have hpow := pow_le_pow_right₀ hL hn
  calc
    _ ≤ 1 * ((Finset.univ.erase v).card * L ^ (Finset.univ.erase v).card) :=
      mul_le_mul (booleanFeature_abs_le_one r t) hd (abs_nonneg _) zero_le_one
    _ ≤ Fintype.card F * L ^ Fintype.card F := by
      rw [one_mul]
      exact mul_le_mul (Nat.cast_le.mpr hn) hpow (pow_nonneg (zero_le_one.trans hL) _) (by positivity)

def productMinorPartialBound (q h : ℕ) (C R : ℝ) : ℝ :=
  C * ((2 : ℝ) ^ h * (h * (((q : ℝ) + 1) * R) ^ h))

theorem productMinorPartialBound_nonneg (q h : ℕ) {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R) :
    0 ≤ productMinorPartialBound q h C R := by
  unfold productMinorPartialBound
  positivity

theorem booleanSelectedMinor_partial_bound {B O α : Type*}
    [Fintype B] [Fintype α] [DecidableEq B] [DecidableEq α]
    (c : B → ℝ) (sets : O → Finset α) (block : O → B) {h : ℕ}
    (v : Fin h) (r : O → Option α) (hcard : ∀ o, (sets o).card ≤ h)
    (a : BlockParameter B (Fin h) α → ℝ) {C R : ℝ} (hC : 0 ≤ C) (hR : 1 ≤ R)
    (hc : ∀ o, |c (block o)| ≤ C) (ha : ∀ j, |a j| ≤ R)
    (row col : O) (j : BlockParameter B (Fin h) α) :
    |MvPolynomial.eval a (MvPolynomial.pderiv j (booleanSelectedMinor c sets block v r row col))| ≤
      productMinorPartialBound (Fintype.card α) h C R := by
  unfold booleanSelectedMinor
  rw [booleanSamplerPolynomial_pderiv]
  have hd := booleanSelectedColumn_pderiv_eval_abs_le c (block col) v (r col) (sets row) a hR ha j
  simp only [Fintype.card_fin] at hd
  have htwo : (2 : ℝ) ^ (sets row).card ≤ 2 ^ h :=
    pow_le_pow_right₀ (by norm_num) (hcard row)
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hpos : 0 ≤ (h : ℝ) * (((Fintype.card α : ℝ) + 1) * R) ^ h := by positivity
  exact hd.trans (mul_le_mul (hc col) (mul_le_mul_of_nonneg_right htwo hpos)
    (mul_nonneg (by positivity) hpos) hC)

end Erdos3

end

section

namespace Erdos3

theorem mvPolynomial_eq_constant_of_degreeOf_zero {I : Type*}
    (p : MvPolynomial I ℝ) (hp : ∀ i, p.degreeOf i = 0) :
    p = MvPolynomial.C (p.coeff 0) := by
  classical
  apply MvPolynomial.vars_eq_empty_iff_eq_C.mp
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  exact (MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp hi) (hp i)

theorem booleanLinearMinor_eval_eq {B O α : Type*}
    [Fintype B] [Fintype α] [DecidableEq B] [DecidableEq α]
    (c : B → ℝ) (sets : O → Finset α) (block : O → B) (r : O → Option α)
    (a a₀ : BlockParameter B (Fin 1) α → ℝ) :
    (booleanSelectedMinor c sets block (0 : Fin 1) r).map (MvPolynomial.eval a) =
      (booleanSelectedMinor c sets block (0 : Fin 1) r).map (MvPolynomial.eval a₀) := by
  ext row col
  have hdeg (i : BlockParameter B (Fin 1) α) :
      (booleanSelectedMinor c sets block (0 : Fin 1) r row col).degreeOf i = 0 := by
    have h := booleanSelectedMinor_degreeOf_le c sets block (0 : Fin 1) r row col i
    simp only [Fintype.card_fin, Nat.sub_self] at h
    exact Nat.eq_zero_of_le_zero h
  have hconst := mvPolynomial_eq_constant_of_degreeOf_zero
    (booleanSelectedMinor c sets block (0 : Fin 1) r row col) hdeg
  change MvPolynomial.eval a _ = MvPolynomial.eval a₀ _
  rw [hconst]
  simp only [MvPolynomial.eval_C]

theorem exists_boolean_linear_minor_uniform_lower {B O α : Type*}
    [Fintype B] [Fintype O] [Fintype α]
    [DecidableEq B] [DecidableEq O] [DecidableEq α]
    (c : B → ℝ) (sets : O → Finset α) (hsets : Function.Injective sets)
    (hcard : ∀ o, (sets o).card ≤ 1) (block : O → B) (hblock : Function.Injective block)
    {c₀ : ℝ} (hc₀ : 0 ≤ c₀) (hc : ∀ o, c₀ ≤ |c (block o)|) :
    ∃ r : O → Option α, ∀ a : BlockParameter B (Fin 1) α → ℝ,
      c₀ ^ Fintype.card O ≤
        |((booleanSelectedMinor c sets block (0 : Fin 1) r).map (MvPolynomial.eval a)).det| := by
  obtain ⟨r, a₀, _, hdiag⟩ :=
    exists_boolean_minor_specialization c sets hsets 1 Nat.zero_lt_one hcard block hblock
  refine ⟨r, ?_⟩
  intro a
  have hdiag' : (booleanSelectedMinor c sets block (0 : Fin 1) r).map (MvPolynomial.eval a) =
      Matrix.diagonal (fun o => c (block o)) :=
    (booleanLinearMinor_eval_eq c sets block r a a₀).trans hdiag
  have h := polynomial_det_value_abs_lower
    (booleanSelectedMinor c sets block (0 : Fin 1) r) a (fun o => c (block o)) hdiag' hc₀ hc
  simp only [RingHom.map_det, RingHom.mapMatrix_apply] at h
  exact h

end Erdos3

end

section

namespace Erdos3

open scoped ContDiff

noncomputable def booleanMinorDeterminant {B O F α : Type*}
    [Fintype B] [Fintype O] [Fintype F] [Fintype α]
    [DecidableEq B] [DecidableEq O] [DecidableEq F] [DecidableEq α]
    (c : B → ℝ) (sets : O → Finset α) (block : O → B) (v : F) (r : O → Option α)
    (a : BlockParameter B F α → ℝ) : ℝ :=
  ((booleanSelectedMinor c sets block v r).map (MvPolynomial.eval a)).det

theorem booleanMinorDeterminant_contDiff {B O F α : Type*}
    [Fintype B] [Fintype O] [Fintype F] [Fintype α]
    [DecidableEq B] [DecidableEq O] [DecidableEq F] [DecidableEq α]
    (c : B → ℝ) (sets : O → Finset α) (block : O → B) (v : F) (r : O → Option α) :
    ContDiff ℝ ∞ (booleanMinorDeterminant c sets block v r) := by
  change ContDiff ℝ ∞ (fun a => ((booleanSelectedMinor c sets block v r).map (MvPolynomial.eval a)).det)
  rw [polynomial_det_eval_function]
  exact mvPolynomial_contDiff_eval _

def productMinorDeterminantDerivativeBound (n j q h : ℕ) (C R : ℝ) : ℝ :=
  n * (j.factorial * (j * productMinorPartialBound q h C R *
    (1 + productMinorEntryBound q h C R) ^ j))

theorem productMinorDeterminantDerivativeBound_nonneg (n j q h : ℕ) {C R : ℝ}
    (hC : 0 ≤ C) (hR : 0 ≤ R) :
    0 ≤ productMinorDeterminantDerivativeBound n j q h C R := by
  have he := productMinorEntryBound_nonneg q h hC hR
  have hd := productMinorPartialBound_nonneg q h hC hR
  unfold productMinorDeterminantDerivativeBound
  positivity

theorem booleanMinorDeterminant_fderiv_norm_le {B O α : Type*}
    [Fintype B] [Fintype O] [Fintype α]
    [DecidableEq B] [DecidableEq O] [DecidableEq α]
    (c : B → ℝ) (sets : O → Finset α) (block : O → B) {h : ℕ}
    (v : Fin h) (r : O → Option α) (hcard : ∀ o, (sets o).card ≤ h)
    (a : BlockParameter B (Fin h) α → ℝ) {C R : ℝ} (hC : 0 ≤ C) (hR : 1 ≤ R)
    (hc : ∀ o, |c (block o)| ≤ C) (ha : ∀ j, |a j| ≤ R) :
    ‖fderiv ℝ (booleanMinorDeterminant c sets block v r) a‖ ≤
      productMinorDeterminantDerivativeBound (Fintype.card (BlockParameter B (Fin h) α))
        (Fintype.card O) (Fintype.card α) h C R := by
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have he := productMinorEntryBound_nonneg (Fintype.card α) h hC hR0
  have hL : 1 ≤ 1 + productMinorEntryBound (Fintype.card α) h C R := by linarith
  have hentry (row col : O) :
      |MvPolynomial.eval a (booleanSelectedMinor c sets block v r row col)| ≤
        1 + productMinorEntryBound (Fintype.card α) h C R := by
    have hbound := booleanSelectedMinor_entry_bound c sets block v r hcard a hC hR0 hc ha row col
    linarith
  exact polynomial_det_fderiv_norm_le (booleanSelectedMinor c sets block v r) a hL
    (productMinorPartialBound_nonneg _ _ hC hR0) hentry
    (booleanSelectedMinor_partial_bound c sets block v r hcard a hC hR hc ha)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem realAffineCube_abs_le {α K : Type*} [Fintype α]
    (root : K → ℝ) (difference : α → K → ℝ)
    (hroot : ∀ k, |root k| ≤ 1) (hd : ∀ r k, |difference r k| ≤ 1)
    (t : Finset α) (k : K) :
    |realAffineCube root difference t k| ≤ (Fintype.card α : ℝ) + 1 := by
  unfold realAffineCube
  calc
    _ ≤ |root k| + |∑ r ∈ t, difference r k| := abs_add_le _ _
    _ ≤ 1 + ∑ r ∈ t, |difference r k| :=
      add_le_add (hroot k) (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ 1 + ∑ _r ∈ t, (1 : ℝ) :=
      add_le_add le_rfl (Finset.sum_le_sum (fun r _ => hd r k))
    _ = 1 + t.card := by simp
    _ ≤ (Fintype.card α : ℝ) + 1 := by
      have hc : (t.card : ℝ) ≤ Fintype.card α := by exact_mod_cast Finset.card_le_univ t
      linarith

theorem real_monomial_eval_abs_le {K : Type*} (e : K →₀ ℕ) (x : K → ℝ)
    {C : ℝ} (hC : 1 ≤ C) (hx : ∀ k, |x k| ≤ C) {h : ℕ}
    (he : e.sum (fun _ n => n) ≤ h) :
    |MvPolynomial.eval x (MvPolynomial.monomial e (1 : ℝ))| ≤ C ^ h := by
  classical
  rw [MvPolynomial.eval_monomial, one_mul]
  change |∏ k ∈ e.support, x k ^ e k| ≤ _
  rw [Finset.abs_prod]
  calc
    _ ≤ ∏ k ∈ e.support, C ^ e k := by
      apply Finset.prod_le_prod₀ (fun k _ => abs_nonneg _)
      intro k _
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hx k) _
    _ = C ^ e.sum (fun _ n => n) := by rw [Finset.prod_pow_eq_pow_sum]; rfl
    _ ≤ C ^ h := pow_le_pow_right₀ hC he

theorem boundedDegreeRealJetMatrix_entry_bound {α K O : Type*}
    [Fintype α] [DecidableEq α]
    (root : K → ℝ) (difference : α → K → ℝ)
    (hroot : ∀ k, |root k| ≤ 1) (hd : ∀ r k, |difference r k| ≤ 1)
    (h : ℕ) (rows : O → Finset α) (o : O) (e : BoundedIntegerExponent K h) :
    |boundedDegreeRealJetMatrix root difference h rows o e| ≤
      (2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ h := by
  have hb := booleanCoefficient_abs_le
    (fun t => MvPolynomial.eval (realAffineCube root difference t)
      (MvPolynomial.monomial e.val (1 : ℝ))) (rows o)
    (fun t _ => real_monomial_eval_abs_le e.val _ (le_add_of_nonneg_left (Nat.cast_nonneg _))
      (realAffineCube_abs_le root difference hroot hd t) e.property)
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact pow_le_pow_right₀ (by norm_num) (Finset.card_le_univ _)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem exists_boolean_minor_sublevel_bound {O α : Type*}
    [Fintype O] [Fintype α] [DecidableEq O] [DecidableEq α]
    (c : O → ℝ) (sets : O → Finset α) (hsets : Function.Injective sets)
    (h : ℕ) (hh : 0 < h) (hcard : ∀ o, (sets o).card ≤ h)
    {N : ℕ} (e : BlockParameter O (Fin h) α ≃ Fin N) (hN : 0 < N)
    {c₀ : ℝ} (hc₀ : 0 < c₀) (hc : ∀ o, c₀ ≤ |c o|) :
    ∃ r : O → Option α, ∀ (d : ℕ), 0 < d → Fintype.card O * (h - 1) ≤ d →
      ∀ (Ω : Set (Fin N → ℝ)) (R u : ℝ), 1 ≤ R →
      (∀ x ∈ Ω, ∀ j, |x j| ≤ R) → 0 < u →
      volume.real (Ω ∩ {x | |((booleanSelectedMinor c sets id (⟨0, hh⟩ : Fin h) r).map
        (MvPolynomial.eval (x ∘ e))).det| ≤ u}) ≤
        R ^ N * multivariateSublevelConstant N d *
          (u * (d + 1 : ℝ) ^ N / c₀ ^ Fintype.card O) ^ (((N * d : ℕ) : ℝ)⁻¹) := by
  obtain ⟨r, a₀, ha₀, hdiag⟩ :=
    exists_boolean_minor_specialization c sets hsets h hh hcard id Function.injective_id
  refine ⟨r, ?_⟩
  intro d hd hdeg Ω R u hR hΩ hu
  have hM : ∀ a b j, (booleanSelectedMinor c sets id (⟨0, hh⟩ : Fin h) r a b).degreeOf j ≤
      h - 1 := by
    intro a b j
    simpa only [Fintype.card_fin] using
      booleanSelectedMinor_degreeOf_le c sets id (⟨0, hh⟩ : Fin h) r a b j
  exact reindexed_polynomial_det_sublevel_bound e hN hd hdeg
    (booleanSelectedMinor c sets id (⟨0, hh⟩ : Fin h) r) hM a₀ ha₀ c hdiag hc₀ hc Ω hR hΩ hu

theorem exists_weighted_boolean_minor_sublevel_bound {O α : Type*}
    [Fintype O] [Fintype α] [DecidableEq O] [DecidableEq α]
    (c : O → ℝ) (sets : O → Finset α) (hsets : Function.Injective sets)
    (h : ℕ) (hh : 0 < h) (hcard : ∀ o, (sets o).card ≤ h)
    {N : ℕ} (e : BlockParameter O (Fin h) α ≃ Fin N) (hN : 0 < N)
    {c₀ : ℝ} (hc₀ : 0 < c₀) (hc : ∀ o, c₀ ≤ |c o|) :
    ∃ r : O → Option α, ∀ (d : ℕ), 0 < d → Fintype.card O * (h - 1) ≤ d →
      ∀ (Ω : Set (Fin N → ℝ)), MeasurableSet Ω →
      ∀ (R u : ℝ), 1 ≤ R → (∀ x ∈ Ω, ∀ j, |x j| ≤ R) →
      ∀ (ρ : (Fin N → ℝ) → ℝ), IntegrableOn ρ Ω →
      ∀ (H : ℝ), 0 ≤ H → (∀ x ∈ Ω, ρ x ≤ H) → 0 < u →
      (∫ x in Ω ∩ {x | |((booleanSelectedMinor c sets id (⟨0, hh⟩ : Fin h) r).map
        (MvPolynomial.eval (x ∘ e))).det| ≤ u}, ρ x) ≤
        H * (R ^ N * multivariateSublevelConstant N d) *
          (u * (d + 1 : ℝ) ^ N / c₀ ^ Fintype.card O) ^ (((N * d : ℕ) : ℝ)⁻¹) := by
  obtain ⟨r, a₀, ha₀, hdiag⟩ :=
    exists_boolean_minor_specialization c sets hsets h hh hcard id Function.injective_id
  refine ⟨r, ?_⟩
  intro d hd hdeg Ω hΩm R u hR hΩ ρ hρ H hH hbound hu
  have hM : ∀ a b j, (booleanSelectedMinor c sets id (⟨0, hh⟩ : Fin h) r a b).degreeOf j ≤
      h - 1 := by
    intro a b j
    simpa only [Fintype.card_fin] using
      booleanSelectedMinor_degreeOf_le c sets id (⟨0, hh⟩ : Fin h) r a b j
  exact weighted_reindexed_polynomial_det_sublevel_bound e hN hd hdeg
    (booleanSelectedMinor c sets id (⟨0, hh⟩ : Fin h) r) hM a₀ ha₀ c hdiag hc₀ hc
    Ω hΩm hR hΩ ρ hρ hH hbound hu

end Erdos3

end

section

namespace Erdos3

noncomputable def booleanBlockParameterEquiv (O α : Type*) [Fintype O] [Fintype α] (h : ℕ) :
    BlockParameter O (Fin h) α ≃ Fin (Fintype.card O * (h * (Fintype.card α + 1))) :=
  Fintype.equivFinOfCardEq (blockParameter_card h)

theorem boolean_minor_parameter_count_pos (O α : Type*) [Fintype O] [Nonempty O]
    [Fintype α] {h : ℕ} (hh : 0 < h) :
    0 < Fintype.card O * (h * (Fintype.card α + 1)) :=
  Nat.mul_pos Fintype.card_pos (Nat.mul_pos hh (Nat.succ_pos _))

theorem boolean_minor_degree_bound_pos (O : Type*) [Fintype O] [Nonempty O]
    {h : ℕ} (hh : 1 < h) : 0 < Fintype.card O * (h - 1) :=
  Nat.mul_pos Fintype.card_pos (Nat.sub_pos_of_lt hh)

abbrev BoundedBooleanMonomial (α : Type*) (h : ℕ) := {s : Finset α // s.card ≤ h}

instance boundedBooleanMonomialNonempty (α : Type*) (h : ℕ) :
    Nonempty (BoundedBooleanMonomial α h) :=
  ⟨⟨∅, by simp⟩⟩

theorem boundedBooleanMonomial_injective (α : Type*) (h : ℕ) :
    Function.Injective (fun s : BoundedBooleanMonomial α h => s.val) :=
  Subtype.val_injective

theorem boundedBooleanMonomial_card_le (α : Type*) (h : ℕ)
    (s : BoundedBooleanMonomial α h) : s.val.card ≤ h := s.property

theorem boundedBooleanMonomial_parameter_count_pos (α : Type*) [Fintype α]
    [DecidableEq α] {h : ℕ} (hh : 0 < h) :
    0 < Fintype.card (BoundedBooleanMonomial α h) * (h * (Fintype.card α + 1)) :=
  boolean_minor_parameter_count_pos (BoundedBooleanMonomial α h) α hh

end Erdos3

end

end OAI
