/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.FiniteMixedPermutation
import OAI.Combinatorics.Progressions.Probability.FinitePointMassLp
import OAI.Combinatorics.Progressions.Probability.FiniteProductMass
import OAI.Combinatorics.Progressions.Probability.FiniteSectionWeightMass

namespace OAI

section

namespace Erdos3

theorem exists_antitone_permutation {n : ℕ} (d : Fin n → ℕ) :
    ∃ e : Equiv.Perm (Fin n), Antitone (fun i => d (e i)) := by
  exact ⟨Tuple.sort (fun i => OrderDual.toDual (d i)),
    Tuple.monotone_sort (fun i => OrderDual.toDual (d i))⟩

end Erdos3

end

section

namespace Erdos3

variable {X : Type*}

def FiniteTupleDependsOn (s : ℕ → Bool) (n : ℕ) (f : (Fin n → X) → ℝ) : Prop :=
  ∀ v u, (∀ i : Fin n, s i = true → v i = u i) → f v = f u

theorem FiniteTupleDependsOn.snoc {s : ℕ → Bool} {n : ℕ}
    {f : (Fin (n + 1) → X) → ℝ} (hf : FiniteTupleDependsOn s (n + 1) f)
    {v u : Fin n → X} {a b : X}
    (hvu : ∀ i : Fin n, s i = true → v i = u i) (hab : s n = true → a = b) :
    f (Fin.snoc v a) = f (Fin.snoc u b) := by
  apply hf
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · intro hs
    simpa only [Fin.snoc_last] using hab hs
  · intro hs
    simpa only [Fin.snoc_castSucc] using hvu j hs

theorem FiniteTupleDependsOn.last_inactive {s : ℕ → Bool} {n : ℕ}
    {f : (Fin (n + 1) → X) → ℝ} (hf : FiniteTupleDependsOn s (n + 1) f)
    (hs : s n = false) (v : Fin n → X) (a b : X) :
    f (Fin.snoc v a) = f (Fin.snoc v b) := by
  apply hf.snoc (fun _ _ => rfl)
  intro h
  simp only [hs, Bool.false_eq_true] at h

end Erdos3

end

section

namespace Erdos3

variable {n k : ℕ}

noncomputable def finiteSlotMask (a : Fin k → Fin n) (i : ℕ) : Bool := by
  classical
  exact decide (∃ j, (a j).val = i)

theorem finiteSlotMask_active (a : Fin k → Fin n) (j : Fin k) :
    finiteSlotMask a (a j) = true := by
  classical
  simp only [finiteSlotMask, decide_eq_true_eq]
  exact ⟨j, rfl⟩

theorem finiteSlotMask_inactive (a : Fin k → Fin n) (i : Fin n)
    (hi : ¬∃ j, a j = i) : finiteSlotMask a i = false := by
  classical
  simp only [finiteSlotMask, decide_eq_false_iff_not]
  rintro ⟨j, hj⟩
  exact hi ⟨j, Fin.ext hj⟩

theorem finiteSlotMask_depends {X : Type*} (a : Fin k → Fin n) (f : (Fin k → X) → ℝ) :
    FiniteTupleDependsOn (finiteSlotMask a) n (fun v => f (fun j => v (a j))) := by
  intro v u h
  apply congrArg f
  funext j
  exact h (a j) (finiteSlotMask_active a j)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]

theorem finiteProductIntegral_restrict (p : I → Prop) [DecidablePred p]
    (w : I → X → ℝ) (hw : ∀ i, ¬p i → ∑ x, w i x = 1)
    (g : ({i // p i} → X) → ℝ) :
    finiteProductIntegral w (fun x => g (fun i => x i)) =
      finiteProductIntegral (fun i : {i // p i} => w i) g := by
  rw [finiteProductIntegral_split p]
  congr 1
  funext u
  have he : (fun v => g (fun i => finiteSplitPoint p u v i)) = fun _ => g u := by
    funext v
    congr 1
    funext i
    exact finiteSplitPoint_fixed p u v i
  rw [he]
  exact finiteProductIntegral_const_of_mass_one (fun i : {i // ¬p i} => w i)
    (fun i => hw i i.property) (g u)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I X : Type*} [Fintype I] [Fintype X]

theorem finiteWeightedHolder_normalized (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (p : I → ℝ) (hp : ∀ i, 0 < p i) (hsum : (∑ i, 1 / p i) = 1)
    (f : I → X → ℝ) (hnorm : ∀ i, (∑ x, w x * |f i x| ^ p i) ≤ 1) :
    (∑ x, w x * ∏ i, |f i x|) ≤ 1 := by
  have hpoint (x : X) : (∏ i, |f i x|) ≤ ∑ i, (1 / p i) * |f i x| ^ p i := by
    have h := Real.geom_mean_le_arith_mean_weighted Finset.univ (fun i => 1 / p i)
      (fun i => |f i x| ^ p i) (fun i _ => le_of_lt (one_div_pos.mpr (hp i))) hsum
      (fun i _ => Real.rpow_nonneg (abs_nonneg _) _)
    have he (i : I) : (|f i x| ^ p i) ^ (1 / p i) = |f i x| := by
      rw [← Real.rpow_mul (abs_nonneg _)]
      have hc : p i * (1 / p i) = 1 := by field_simp [(hp i).ne' ]
      rw [hc, Real.rpow_one]
    simpa only [he] using h
  calc
    (∑ x, w x * ∏ i, |f i x|) ≤ ∑ x, w x * ∑ i, (1 / p i) * |f i x| ^ p i :=
      Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hpoint x) (hw x))
    _ = ∑ i, (1 / p i) * ∑ x, w x * |f i x| ^ p i := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ ≤ ∑ i, 1 / p i := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (hnorm i) (le_of_lt (one_div_pos.mpr (hp i)))
    _ = 1 := hsum

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I J X : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype X]

theorem finiteProductIntegral_pullback (a : J → I) (ha : Function.Injective a)
    (w : I → X → ℝ) (hw : ∀ i, (¬∃ j, a j = i) → ∑ x, w i x = 1)
    (g : (J → X) → ℝ) :
    finiteProductIntegral w (fun x => g (fun j => x (a j))) =
      finiteProductIntegral (fun j => w (a j)) g := by
  classical
  let : Fintype (Set.range a) := Subtype.fintype (fun i => ∃ j, a j = i)
  let e := Equiv.ofInjective a ha
  have h := finiteProductIntegral_restrict (fun i => ∃ j, a j = i) w hw
    (fun u => g (fun j => u (e j)))
  exact h.trans (finiteProductIntegral_pullback_equiv e (fun i => w i) g)

end Erdos3

end

section

namespace Erdos3

variable {X : Type*} [Fintype X]

theorem finiteMaskedLpStep_depends (w : X → ℝ) (p : ℝ) (s : ℕ → Bool)
    (x₀ : X) (n : ℕ) (f : (Fin (n + 1) → X) → ℝ)
    (hf : FiniteTupleDependsOn s (n + 1) f) :
    FiniteTupleDependsOn s n (finiteMaskedLpStep w p (s n) x₀ n f) := by
  intro v u hvu
  have he (a : X) : f (Fin.snoc v a) = f (Fin.snoc u a) :=
    hf.snoc hvu (fun _ => rfl)
  cases hs : s n with
  | false =>
    simp only [finiteMaskedLpStep, Bool.false_eq_true, ite_false]
    exact he x₀
  | true =>
    simp only [finiteMaskedLpStep, ite_true]
    apply congrArg (finiteWeightedLp w p)
    funext a
    exact he a

theorem finiteMaskedMixedLp_basepoint (w : ℕ → X → ℝ) (p : ℕ → ℝ) (s : ℕ → Bool)
    (x₀ y₀ : X) (n : ℕ) (f : (Fin n → X) → ℝ) (hf : FiniteTupleDependsOn s n f) :
    finiteMaskedMixedLp w p s x₀ n f = finiteMaskedMixedLp w p s y₀ n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have he : finiteMaskedLpStep (w n) (p n) (s n) x₀ n f =
        finiteMaskedLpStep (w n) (p n) (s n) y₀ n f := by
      funext v
      cases hs : s n with
      | false =>
        simp only [finiteMaskedLpStep, Bool.false_eq_true, ite_false]
        exact hf.last_inactive hs v x₀ y₀
      | true => simp only [finiteMaskedLpStep, ite_true]
    calc
      finiteMaskedMixedLp w p s x₀ (n + 1) f =
          finiteMaskedMixedLp w p s x₀ n (finiteMaskedLpStep (w n) (p n) (s n) y₀ n f) :=
        congrArg (finiteMaskedMixedLp w p s x₀ n) he
      _ = finiteMaskedMixedLp w p s y₀ n (finiteMaskedLpStep (w n) (p n) (s n) y₀ n f) :=
        ih _ (finiteMaskedLpStep_depends (w n) (p n) s y₀ n f hf)
      _ = finiteMaskedMixedLp w p s y₀ (n + 1) f := rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I X : Type*} [Fintype I] [Fintype X]

theorem finiteWeightedHolder (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (p : I → ℝ) (hp : ∀ i, 0 < p i) (hsum : (∑ i, 1 / p i) = 1)
    (f : I → X → ℝ) :
    (∑ x, w x * ∏ i, |f i x|) ≤ ∏ i, finiteWeightedLp w (p i) (f i) := by
  classical
  by_cases hz : ∃ i, finiteWeightedLp w (p i) (f i) = 0
  · obtain ⟨i, hi⟩ := hz
    have hleft : (∑ x, w x * ∏ j, |f j x|) = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      by_cases hx : w x = 0
      · rw [hx, zero_mul]
      · have hix := finiteWeightedLp_zero_support w hw (hp i) (f i) hi x hx
        have hprod : (∏ j, |f j x|) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hix, abs_zero])
        rw [hprod, mul_zero]
    rw [hleft]
    exact Finset.prod_nonneg (fun j _ => finiteWeightedLp_nonneg w hw (p j) (f j))
  · push Not at hz
    let M : I → ℝ := fun i => finiteWeightedLp w (p i) (f i)
    have hM : ∀ i, 0 < M i := fun i =>
      lt_of_le_of_ne (finiteWeightedLp_nonneg w hw (p i) (f i)) (Ne.symm (hz i))
    let g : I → X → ℝ := fun i x => (M i)⁻¹ * f i x
    have hg (i : I) : finiteWeightedLp w (p i) (g i) = 1 := by
      change finiteWeightedLp w (p i) (fun x => (M i)⁻¹ * f i x) = 1
      rw [finiteWeightedLp_smul w hw (hp i) (inv_nonneg.mpr (hM i).le)]
      exact inv_mul_cancel₀ (hM i).ne'
    have hnorm (i : I) : (∑ x, w x * |g i x| ^ p i) ≤ 1 := by
      rw [← finiteWeightedLp_rpow_self w hw (hp i) (g i), hg, Real.one_rpow]
    have hnormal := finiteWeightedHolder_normalized w hw p hp hsum g hnorm
    have hpoint (i : I) (x : X) : |f i x| = M i * |g i x| := by
      dsimp [g]
      rw [abs_mul, abs_inv, abs_of_pos (hM i), ← mul_assoc,
        mul_inv_cancel₀ (hM i).ne', one_mul]
    have hprod (x : X) : (∏ i, |f i x|) = (∏ i, M i) * ∏ i, |g i x| := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun i _ => hpoint i x)
    calc
      (∑ x, w x * ∏ i, |f i x|) = (∏ i, M i) * ∑ x, w x * ∏ i, |g i x| := by
        simp_rw [hprod]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ ≤ ∏ i, M i := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hnormal
          (Finset.prod_nonneg (fun i _ => (hM i).le))
      _ = _ := rfl

theorem finiteWeightedHolder_card (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hI : 0 < Fintype.card I) (f : I → X → ℝ) :
    (∑ x, w x * ∏ i, |f i x|) ≤ ∏ i, finiteWeightedLp w (Fintype.card I : ℝ) (f i) := by
  have hp : 0 < (Fintype.card I : ℝ) := Nat.cast_pos.mpr hI
  apply finiteWeightedHolder w hw (fun _ : I => (Fintype.card I : ℝ)) (fun _ => hp) _ f
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

theorem finiteWeightedHolder_abs (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (p : I → ℝ) (hp : ∀ i, 0 < p i) (hsum : (∑ i, 1 / p i) = 1)
    (f : I → X → ℝ) :
    |∑ x, w x * ∏ i, f i x| ≤ ∏ i, finiteWeightedLp w (p i) (f i) := by
  calc
    |∑ x, w x * ∏ i, f i x| ≤ ∑ x, |w x * ∏ i, f i x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, w x * ∏ i, |f i x| := by
      apply Finset.sum_congr rfl
      intro x _
      rw [abs_mul, abs_of_nonneg (hw x), Finset.abs_prod]
    _ ≤ _ := finiteWeightedHolder w hw p hp hsum f

end Erdos3

end

section

namespace Erdos3

variable {X : Type*} [Fintype X]

noncomputable def finiteMaskedWeights (w : ℕ → X → ℝ) (s : ℕ → Bool)
    (x₀ : X) (i : ℕ) : X → ℝ :=
  finiteSectionWeight (w i) (!(s i)) x₀

omit [Fintype X] in
theorem finiteMaskedWeights_active (w : ℕ → X → ℝ) (s : ℕ → Bool)
    (x₀ : X) (i : ℕ) (hi : s i = true) : finiteMaskedWeights w s x₀ i = w i := by
  funext x
  simp only [finiteMaskedWeights, hi, Bool.not_true, finiteSectionWeight_false]

omit [Fintype X] in
theorem finiteMaskedWeights_inactive (w : ℕ → X → ℝ) (s : ℕ → Bool)
    (x₀ : X) (i : ℕ) (hi : s i = false) :
    finiteMaskedWeights w s x₀ i = finiteSectionWeight (w i) true x₀ := by
  simp only [finiteMaskedWeights, hi, Bool.not_false]

omit [Fintype X] in
theorem finiteMaskedWeights_nonneg (w : ℕ → X → ℝ) (s : ℕ → Bool)
    (x₀ : X) (i : ℕ) (hw : ∀ x, 0 ≤ w i x) (x : X) :
    0 ≤ finiteMaskedWeights w s x₀ i x :=
  finiteSectionWeight_nonneg (w i) hw (!(s i)) x₀ x

theorem finiteMaskedMixedLp_eq_mixed (w : ℕ → X → ℝ) (p : ℕ → ℝ) (s : ℕ → Bool)
    (x₀ : X) (n : ℕ) (hp : ∀ i < n, 0 < p i) (f : (Fin n → X) → ℝ) :
    finiteMaskedMixedLp w p s x₀ n f = finiteMixedLp (finiteMaskedWeights w s x₀) p n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases hs : s n with
    | false =>
      simp only [finiteMaskedMixedLp, hs, finiteMixedLp]
      rw [ih (fun i hi => hp i (by omega)), finiteMaskedWeights_inactive w s x₀ n hs]
      simp_rw [finiteWeightedLp_pointMass (w n) x₀ (hp n (by omega))]
      exact (finiteMixedLp_abs (finiteMaskedWeights w s x₀) p n (fun v => f (Fin.snoc v x₀))).symm
    | true =>
      simp only [finiteMaskedMixedLp, hs, finiteMixedLp]
      rw [ih (fun i hi => hp i (by omega)), finiteMaskedWeights_active w s x₀ n hs]
      rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

theorem finiteWeightedHolder_pair (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (hpq : 1 / p + 1 / q = 1)
    (f g : X → ℝ) :
    |∑ x, w x * (f x * g x)| ≤ finiteWeightedLp w p f * finiteWeightedLp w q g := by
  have h := finiteWeightedHolder_abs w hw (fun b : Bool => cond b p q)
    (fun b => by cases b <;> assumption) (by simpa [add_comm] using hpq)
    (fun b x => cond b (f x) (g x))
  simpa [mul_comm] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem finiteWeightedHolder_finset {J X : Type*} [Fintype X]
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (D : Finset J) (hD : 0 < D.card)
    (f : J → X → ℝ) :
    (∑ x, w x * ∏ j ∈ D, |f j x|) ≤ ∏ j ∈ D, finiteWeightedLp w (D.card : ℝ) (f j) := by
  have h := finiteWeightedHolder_card (I := D) w hw (by simpa only [Fintype.card_coe] using hD)
    (fun j => f j.1)
  calc
    (∑ x, w x * ∏ j ∈ D, |f j x|) = ∑ x, w x * ∏ j : D, |f j.1 x| := by
      apply Finset.sum_congr rfl
      intro x _
      exact congrArg (fun t => w x * t) (Finset.prod_coe_sort D (fun j => |f j x|)).symm
    _ ≤ ∏ j : D, finiteWeightedLp w (D.card : ℝ) (f j.1) := by
      simpa only [Fintype.card_coe] using h
    _ = ∏ j ∈ D, finiteWeightedLp w (D.card : ℝ) (f j) :=
      Finset.prod_coe_sort D (fun j => finiteWeightedLp w (D.card : ℝ) (f j))

theorem finiteWeightedHolder_with_constants {J X : Type*}
    [Fintype J] [DecidableEq J] [Fintype X]
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (D : Finset J) (hD : 0 < D.card)
    (x₀ : X) (f : J → X → ℝ) (hf : ∀ j, j ∉ D → ∀ x, f j x = f j x₀) :
    (∑ x, w x * ∏ j, |f j x|) ≤
      (∏ j ∈ Dᶜ, |f j x₀|) * ∏ j ∈ D, finiteWeightedLp w (D.card : ℝ) (f j) := by
  have hpoint (x : X) : (∏ j, |f j x|) =
      (∏ j ∈ Dᶜ, |f j x₀|) * ∏ j ∈ D, |f j x| := by
    rw [← Finset.prod_compl_mul_prod D]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    rw [hf j (Finset.mem_compl.mp hj) x]
  calc
    (∑ x, w x * ∏ j, |f j x|) =
        (∏ j ∈ Dᶜ, |f j x₀|) * ∑ x, w x * ∏ j ∈ D, |f j x| := by
      simp_rw [hpoint]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (finiteWeightedHolder_finset w hw D hD f)
      (Finset.prod_nonneg (fun j _ => abs_nonneg _))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

theorem finiteSectionL2Norm_masked_pullback (w : X → ℝ) (s : ℕ → Bool) (x₀ : X)
    (n k : ℕ) (a : Fin k → Fin n) (ha : Function.Injective a)
    (hs : ∀ j, s (a j) = true) (hn : ∀ i : Fin n, (¬∃ j, a j = i) → s i = false)
    (t : Fin n → Bool) (f : (Fin k → X) → ℝ) (z : Fin n → X) :
    finiteSectionL2Norm (finiteMaskedWeights (fun _ => w) s x₀) n t
      (fun v => f (fun j => v (a j))) z =
        finiteSectionL2Norm (fun _ => w) k (fun j => t (a j)) f (fun j => z (a j)) := by
  simp only [finiteSectionL2Norm, finiteSectionIntegral_eq_product]
  apply congrArg Real.sqrt
  calc
    _ = finiteProductIntegral
        (fun j => finiteSectionWeight (finiteMaskedWeights (fun _ => w) s x₀ (a j)) (t (a j)) (z (a j)))
        (fun v => f v ^ 2) := by
      refine finiteProductIntegral_pullback a ha
        (fun i : Fin n => finiteSectionWeight (finiteMaskedWeights (fun _ => w) s x₀ i) (t i) (z i))
        ?_ (fun v => f v ^ 2)
      intro i hi
      rw [finiteMaskedWeights_inactive (fun _ => w) s x₀ i (hn i hi)]
      exact finiteSectionWeight_mass_one _ (finiteSectionWeight_mass_true w x₀) (t i) (z i)
    _ = _ := by
      congr 1
      funext j x
      rw [finiteMaskedWeights_active (fun _ => w) s x₀ (a j) (hs j)]

theorem finiteSectionL2Norm_slot_pullback (w : X → ℝ) (x₀ : X)
    (n k : ℕ) (a : Fin k → Fin n) (ha : Function.Injective a)
    (t : Fin n → Bool) (f : (Fin k → X) → ℝ) (z : Fin n → X) :
    finiteSectionL2Norm (finiteMaskedWeights (fun _ => w) (finiteSlotMask a) x₀) n t
      (fun v => f (fun j => v (a j))) z =
        finiteSectionL2Norm (fun _ => w) k (fun j => t (a j)) f (fun j => z (a j)) :=
  finiteSectionL2Norm_masked_pullback w (finiteSlotMask a) x₀ n k a ha
    (finiteSlotMask_active a) (finiteSlotMask_inactive a) t f z

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {J X : Type*} [Fintype J] [Fintype X]

def finiteFactorMultiplicity (b : J → Bool) : ℕ :=
  (Finset.univ.filter (fun j => b j = true)).card

theorem finiteHypergraph_step [DecidableEq J] (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (s : J → ℕ → Bool) (x₀ : X) (n : ℕ) (f : J → (Fin (n + 1) → X) → ℝ)
    (hf : ∀ j, FiniteTupleDependsOn (s j) (n + 1) (f j))
    (hdeg : 0 < finiteFactorMultiplicity (fun j => s j n)) (v : Fin n → X) :
    (∑ a, w a * ∏ j, |f j (Fin.snoc v a)|) ≤
      ∏ j, |finiteMaskedLpStep w (finiteFactorMultiplicity (fun j => s j n) : ℝ)
        (s j n) x₀ n (f j) v| := by
  let D : Finset J := Finset.univ.filter (fun j => s j n = true)
  have hinactive (j : J) (hj : j ∉ D) : s j n = false := by
    cases h : s j n <;> simp_all [D]
  have hactive (j : J) (hj : j ∈ D) : s j n = true := (Finset.mem_filter.mp hj).2
  have hbound := finiteWeightedHolder_with_constants w hw D hdeg x₀
    (fun j a => f j (Fin.snoc v a))
    (fun j hj a => (hf j).last_inactive (hinactive j hj) v a x₀)
  have hprod : (∏ j, |finiteMaskedLpStep w (D.card : ℝ) (s j n) x₀ n (f j) v|) =
      (∏ j ∈ Dᶜ, |f j (Fin.snoc v x₀)|) *
        ∏ j ∈ D, finiteWeightedLp w (D.card : ℝ) (fun a => f j (Fin.snoc v a)) := by
    rw [← Finset.prod_compl_mul_prod D]
    congr 1
    · apply Finset.prod_congr rfl
      intro j hj
      simp only [finiteMaskedLpStep, hinactive j (Finset.mem_compl.mp hj), Bool.false_eq_true,
        ite_false]
    · apply Finset.prod_congr rfl
      intro j hj
      simp only [finiteMaskedLpStep, hactive j hj, ite_true,
        abs_of_nonneg (finiteWeightedLp_nonneg w hw _ _)]
  change (∑ a, w a * ∏ j, |f j (Fin.snoc v a)|) ≤
    ∏ j, |finiteMaskedLpStep w (D.card : ℝ) (s j n) x₀ n (f j) v|
  rw [hprod]
  exact hbound

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {J X : Type*} [Fintype J] [DecidableEq J] [Fintype X]

theorem finiteHypergraph_holder (w : ℕ → X → ℝ) (s : J → ℕ → Bool) (x₀ : X) (n : ℕ)
    (hw : ∀ i < n, ∀ x, 0 ≤ w i x)
    (hdeg : ∀ i < n, 0 < finiteFactorMultiplicity (fun j => s j i))
    (f : J → (Fin n → X) → ℝ) (hf : ∀ j, FiniteTupleDependsOn (s j) n (f j)) :
    finiteProductIntegral (fun i : Fin n => w i) (fun v => ∏ j, |f j v|) ≤
      ∏ j, finiteMaskedMixedLp w (fun i => (finiteFactorMultiplicity (fun j => s j i) : ℝ))
        (s j) x₀ n (f j) := by
  induction n with
  | zero =>
    simp only [finiteProductIntegral_zero, finiteMaskedMixedLp]
    exact le_rfl
  | succ n ih =>
    let g := fun j => finiteMaskedLpStep (w n)
      (finiteFactorMultiplicity (fun j => s j n) : ℝ) (s j n) x₀ n (f j)
    have hg : ∀ j, FiniteTupleDependsOn (s j) n (g j) :=
      fun j => finiteMaskedLpStep_depends (w n) _ (s j) x₀ n (f j) (hf j)
    rw [finiteProductIntegral_snoc]
    calc
      finiteProductIntegral (fun i : Fin n => w i.castSucc)
          (fun v => ∑ a, w (Fin.last n) a * ∏ j, |f j (Fin.snoc v a)|) ≤
          finiteProductIntegral (fun i : Fin n => w i) (fun v => ∏ j, |g j v|) := by
        apply finiteProductIntegral_mono (fun i : Fin n => w i)
          (fun i x => hw i (by omega) x)
        intro v
        exact finiteHypergraph_step (w n) (hw n (by omega)) s x₀ n f hf (hdeg n (by omega)) v
      _ ≤ ∏ j, finiteMaskedMixedLp w
          (fun i => (finiteFactorMultiplicity (fun j => s j i) : ℝ)) (s j) x₀ n (g j) :=
        ih (fun i hi => hw i (by omega)) (fun i hi => hdeg i (by omega)) g hg
      _ = _ := rfl

end Erdos3

end

section

namespace Erdos3

theorem finiteSlotMask_reindex {n k : ℕ} (e : Equiv.Perm (Fin n)) (a : Fin k → Fin n) (i : Fin n) :
    finiteSlotMask (fun j => e.symm (a j)) i = finiteSlotMask a (e i) := by
  classical
  simp only [finiteSlotMask, ← Fin.ext_iff, Equiv.symm_apply_eq]

theorem finiteSlotMultiplicity_reindex {J : Type*} [Fintype J]
    {n k : ℕ} (e : Equiv.Perm (Fin n)) (a : J → Fin k → Fin n) (i : Fin n) :
    finiteFactorMultiplicity (fun j => finiteSlotMask (fun l => e.symm (a j l)) i) =
      finiteFactorMultiplicity (fun j => finiteSlotMask (a j) (e i)) := by
  congr 1
  funext j
  exact finiteSlotMask_reindex e (a j) i

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {J X : Type*} [Fintype J] [DecidableEq J] [Fintype X] [Nonempty X]

theorem finiteHypergraph_section_bound (w : ℕ → X → ℝ) (s : J → ℕ → Bool)
    (x₀ : X) (n : ℕ) (hw : ∀ i < n, ∀ x, 0 ≤ w i x)
    (hdeg : ∀ i < n, 2 ≤ finiteFactorMultiplicity (fun j => s j i))
    (hmono : ∀ i k, i ≤ k → k < n →
      finiteFactorMultiplicity (fun j => s j k) ≤ finiteFactorMultiplicity (fun j => s j i))
    (f : J → (Fin n → X) → ℝ) (hf : ∀ j, FiniteTupleDependsOn (s j) n (f j))
    (C : J → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hsection : ∀ j t z, finiteSectionL2Norm (finiteMaskedWeights w (s j) x₀) n t (f j) z ≤ C j) :
    finiteProductIntegral (fun i : Fin n => w i) (fun v => ∏ j, |f j v|) ≤ ∏ j, C j := by
  have hp : ∀ i < n, (2 : ℝ) ≤ (finiteFactorMultiplicity (fun j => s j i) : ℝ) := by
    intro i hi
    exact_mod_cast hdeg i hi
  have hp0 : ∀ i < n, (0 : ℝ) < (finiteFactorMultiplicity (fun j => s j i) : ℝ) :=
    fun i hi => lt_of_lt_of_le (by norm_num) (hp i hi)
  apply (finiteHypergraph_holder w s x₀ n hw (fun i hi => by have := hdeg i hi; omega) f hf).trans
  apply Finset.prod_le_prod₀
  · intro j _
    exact finiteMaskedMixedLp_nonneg _ _ _ _ _ _
  · intro j _
    rw [finiteMaskedMixedLp_eq_mixed w _ (s j) x₀ n hp0]
    apply finiteMixedLp_le_constant_of_sections (finiteMaskedWeights w (s j) x₀) _ n
      (fun i hi x => finiteMaskedWeights_nonneg w (s j) x₀ i (hw i hi) x) hp
      (fun i k hik hk => by exact_mod_cast hmono i k hik hk)
      (fun _ => C j) (fun _ => hC j) (f j) (hsection j) (hC j)
    intro i _
    exact le_rfl

theorem finiteHypergraph_abs_section_bound (w : ℕ → X → ℝ) (s : J → ℕ → Bool)
    (x₀ : X) (n : ℕ) (hw : ∀ i < n, ∀ x, 0 ≤ w i x)
    (hdeg : ∀ i < n, 2 ≤ finiteFactorMultiplicity (fun j => s j i))
    (hmono : ∀ i k, i ≤ k → k < n →
      finiteFactorMultiplicity (fun j => s j k) ≤ finiteFactorMultiplicity (fun j => s j i))
    (f : J → (Fin n → X) → ℝ) (hf : ∀ j, FiniteTupleDependsOn (s j) n (f j))
    (C : J → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hsection : ∀ j t z, finiteSectionL2Norm (finiteMaskedWeights w (s j) x₀) n t (f j) z ≤ C j) :
    |finiteProductIntegral (fun i : Fin n => w i) (fun v => ∏ j, f j v)| ≤ ∏ j, C j := by
  calc
    |finiteProductIntegral (fun i : Fin n => w i) (fun v => ∏ j, f j v)| ≤
        finiteProductIntegral (fun i : Fin n => w i) (fun v => ∏ j, |f j v|) := by
      unfold finiteProductIntegral
      apply (Finset.abs_sum_le_sum_abs _ _).trans_eq
      apply Finset.sum_congr rfl
      intro v _
      dsimp only
      have hweight : 0 ≤ ∏ i : Fin n, w i (v i) :=
        Finset.prod_nonneg (fun i _ => hw i i.isLt (v i))
      rw [abs_mul, abs_of_nonneg hweight, Finset.abs_prod]
    _ ≤ _ := finiteHypergraph_section_bound w s x₀ n hw hdeg hmono f hf C hC hsection

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {J X : Type*} [Fintype J] [DecidableEq J] [Fintype X]

theorem finiteHypergraph_pullback_bound (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (x₀ : X)
    (n k : ℕ) (a : J → Fin k → Fin n) (ha : ∀ j, Function.Injective (a j))
    (hdeg : ∀ i < n, 2 ≤ finiteFactorMultiplicity (fun j => finiteSlotMask (a j) i))
    (hmono : ∀ i l, i ≤ l → l < n →
      finiteFactorMultiplicity (fun j => finiteSlotMask (a j) l) ≤
        finiteFactorMultiplicity (fun j => finiteSlotMask (a j) i))
    (f : J → (Fin k → X) → ℝ) (C : J → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hsection : ∀ j t z, finiteSectionL2Norm (fun _ => w) k t (f j) z ≤ C j) :
    finiteProductIntegral (fun _ : Fin n => w)
      (fun v => ∏ j, |f j (fun l => v (a j l))|) ≤ ∏ j, C j := by
  let : Nonempty X := ⟨x₀⟩
  apply finiteHypergraph_section_bound (fun _ => w) (fun j => finiteSlotMask (a j)) x₀ n
    (fun _ _ => hw) hdeg hmono (fun j v => f j (fun l => v (a j l)))
    (fun j => finiteSlotMask_depends (a j) (f j)) C hC
  intro j t z
  rw [finiteSectionL2Norm_slot_pullback w x₀ n k (a j) (ha j)]
  exact hsection j _ _

theorem finiteHypergraph_abs_pullback_bound (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (x₀ : X)
    (n k : ℕ) (a : J → Fin k → Fin n) (ha : ∀ j, Function.Injective (a j))
    (hdeg : ∀ i < n, 2 ≤ finiteFactorMultiplicity (fun j => finiteSlotMask (a j) i))
    (hmono : ∀ i l, i ≤ l → l < n →
      finiteFactorMultiplicity (fun j => finiteSlotMask (a j) l) ≤
        finiteFactorMultiplicity (fun j => finiteSlotMask (a j) i))
    (f : J → (Fin k → X) → ℝ) (C : J → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hsection : ∀ j t z, finiteSectionL2Norm (fun _ => w) k t (f j) z ≤ C j) :
    |finiteProductIntegral (fun _ : Fin n => w)
      (fun v => ∏ j, f j (fun l => v (a j l)))| ≤ ∏ j, C j := by
  let : Nonempty X := ⟨x₀⟩
  apply finiteHypergraph_abs_section_bound (fun _ => w) (fun j => finiteSlotMask (a j)) x₀ n
    (fun _ _ => hw) hdeg hmono (fun j v => f j (fun l => v (a j l)))
    (fun j => finiteSlotMask_depends (a j) (f j)) C hC
  intro j t z
  rw [finiteSectionL2Norm_slot_pullback w x₀ n k (a j) (ha j)]
  exact hsection j _ _

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {J X : Type*} [Fintype J] [DecidableEq J] [Fintype X]

theorem finiteHypergraph_unordered_bound (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (x₀ : X)
    (n k : ℕ) (a : J → Fin k → Fin n) (ha : ∀ j, Function.Injective (a j))
    (hdeg : ∀ i : Fin n, 2 ≤ finiteFactorMultiplicity (fun j => finiteSlotMask (a j) i))
    (f : J → (Fin k → X) → ℝ) (C : J → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hsection : ∀ j t z, finiteSectionL2Norm (fun _ => w) k t (f j) z ≤ C j) :
    finiteProductIntegral (fun _ : Fin n => w)
      (fun v => ∏ j, |f j (fun l => v (a j l))|) ≤ ∏ j, C j := by
  let d : Fin n → ℕ := fun i => finiteFactorMultiplicity (fun j => finiteSlotMask (a j) i)
  obtain ⟨e, he⟩ := exists_antitone_permutation d
  have hd : ∀ i < n, 2 ≤ finiteFactorMultiplicity (fun j => finiteSlotMask (fun l => e.symm (a j l)) i) := by
    intro i hi
    change 2 ≤ finiteFactorMultiplicity (fun j => finiteSlotMask (fun l => e.symm (a j l)) (⟨i, hi⟩ : Fin n))
    rw [finiteSlotMultiplicity_reindex]
    exact hdeg _
  have hm : ∀ i l, i ≤ l → l < n →
      finiteFactorMultiplicity (fun j => finiteSlotMask (fun b => e.symm (a j b)) l) ≤
        finiteFactorMultiplicity (fun j => finiteSlotMask (fun b => e.symm (a j b)) i) := by
    intro i l hil hl
    have hi : i < n := lt_of_le_of_lt hil hl
    change finiteFactorMultiplicity (fun j => finiteSlotMask (fun b => e.symm (a j b)) (⟨l, hl⟩ : Fin n)) ≤
      finiteFactorMultiplicity (fun j => finiteSlotMask (fun b => e.symm (a j b)) (⟨i, hi⟩ : Fin n))
    rw [finiteSlotMultiplicity_reindex, finiteSlotMultiplicity_reindex]
    exact he (show (⟨i, hi⟩ : Fin n) ≤ ⟨l, hl⟩ from hil)
  have h := finiteHypergraph_pullback_bound w hw x₀ n k (fun j l => e.symm (a j l))
    (fun j => e.symm.injective.comp (ha j)) hd hm f C hC hsection
  exact (finiteProductIntegral_reindex e (fun _ : Fin n => w)
    (fun v => ∏ j, |f j (fun l => v (a j l))|)).symm.trans_le h

theorem finiteHypergraph_abs_unordered_bound (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (x₀ : X)
    (n k : ℕ) (a : J → Fin k → Fin n) (ha : ∀ j, Function.Injective (a j))
    (hdeg : ∀ i : Fin n, 2 ≤ finiteFactorMultiplicity (fun j => finiteSlotMask (a j) i))
    (f : J → (Fin k → X) → ℝ) (C : J → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hsection : ∀ j t z, finiteSectionL2Norm (fun _ => w) k t (f j) z ≤ C j) :
    |finiteProductIntegral (fun _ : Fin n => w)
      (fun v => ∏ j, f j (fun l => v (a j l)))| ≤ ∏ j, C j := by
  calc
    |finiteProductIntegral (fun _ : Fin n => w) (fun v => ∏ j, f j (fun l => v (a j l)))| ≤
        finiteProductIntegral (fun _ : Fin n => w) (fun v => ∏ j, |f j (fun l => v (a j l))|) := by
      unfold finiteProductIntegral
      apply (Finset.abs_sum_le_sum_abs _ _).trans_eq
      apply Finset.sum_congr rfl
      intro v _
      dsimp only
      have hp : 0 ≤ ∏ i : Fin n, w (v i) := Finset.prod_nonneg (fun i _ => hw (v i))
      rw [abs_mul, abs_of_nonneg hp, Finset.abs_prod]
    _ ≤ _ := finiteHypergraph_unordered_bound w hw x₀ n k a ha hdeg f C hC hsection

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {J B X : Type*} [Fintype J] [DecidableEq J]
  [Fintype B] [DecidableEq B] [Fintype X]

theorem finiteHypergraph_abstract_bound (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (x₀ : X)
    (k : ℕ) (a : J → Fin k → B) (ha : ∀ j, Function.Injective (a j))
    (hdeg : ∀ b, 2 ≤ (Finset.univ.filter (fun j => ∃ l, a j l = b)).card)
    (f : J → (Fin k → X) → ℝ) (C : J → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hsection : ∀ j t z, finiteSectionL2Norm (fun _ => w) k t (f j) z ≤ C j) :
    finiteProductIntegral (fun _ : B => w)
      (fun v => ∏ j, |f j (fun l => v (a j l))|) ≤ ∏ j, C j := by
  classical
  let e := (Fintype.equivFin B).symm
  have hd : ∀ i : Fin (Fintype.card B),
      2 ≤ finiteFactorMultiplicity (fun j => finiteSlotMask (fun l => e.symm (a j l)) i) := by
    intro i
    have he : (Finset.univ.filter (fun j => finiteSlotMask (fun l => e.symm (a j l)) i = true)) =
        Finset.univ.filter (fun j => ∃ l, a j l = e i) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, finiteSlotMask,
        decide_eq_true_eq, ← Fin.ext_iff, Equiv.symm_apply_eq]
    change 2 ≤ (Finset.univ.filter (fun j => finiteSlotMask (fun l => e.symm (a j l)) i = true)).card
    rw [he]
    exact hdeg (e i)
  have h := finiteHypergraph_unordered_bound w hw x₀ (Fintype.card B) k
    (fun j l => e.symm (a j l)) (fun j => e.symm.injective.comp (ha j)) hd f C hC hsection
  exact (finiteProductIntegral_reindex e (fun _ : B => w)
    (fun v => ∏ j, |f j (fun l => v (a j l))|)).symm.trans_le h

end Erdos3

end

end OAI
