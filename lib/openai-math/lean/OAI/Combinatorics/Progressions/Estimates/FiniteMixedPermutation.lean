import OAI.Combinatorics.Progressions.Estimates.FiniteSectionPermutation

namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def finiteMixedLpCore (p E : ℕ → ℝ) : ℕ → ℝ
  | 0 => E 0 ^ (2 / p 0)
  | n + 1 => finiteMixedLpCore p E n * E (n + 1) ^ (2 / p (n + 1) - 2 / p n)

noncomputable def finiteMixedLpBound (p E : ℕ → ℝ) : ℕ → ℝ
  | 0 => E 0
  | n + 1 => finiteMixedLpCore p E n * E (n + 1) ^ (1 - 2 / p n)

theorem finiteMixedLpCore_nonneg (p E : ℕ → ℝ) (hE : ∀ i, 0 ≤ E i) (n : ℕ) :
    0 ≤ finiteMixedLpCore p E n := by
  induction n with
  | zero => exact Real.rpow_nonneg (hE _) _
  | succ n ih => exact mul_nonneg ih (Real.rpow_nonneg (hE _) _)

theorem finiteMixedLpBound_nonneg (p E : ℕ → ℝ) (hE : ∀ i, 0 ≤ E i) (n : ℕ) :
    0 ≤ finiteMixedLpBound p E n := by
  cases n with
  | zero => exact hE 0
  | succ n =>
    exact mul_nonneg (finiteMixedLpCore_nonneg p E hE n)
      (Real.rpow_nonneg (hE _) _)

theorem finiteMixedLpCore_eq_product (p E : ℕ → ℝ) (n : ℕ) :
    finiteMixedLpCore p E n = E 0 ^ (2 / p 0) *
      ∏ j ∈ Finset.range n, E (j + 1) ^ (2 / p (j + 1) - 2 / p j) := by
  induction n with
  | zero => simp [finiteMixedLpCore]
  | succ n ih => simp only [finiteMixedLpCore, ih, Finset.prod_range_succ, mul_assoc]

theorem scaled_reciprocal_exponent {a p : ℝ} (ha : a ≠ 0) (hp : p ≠ 0) :
    (2 / (a * p)) * a = 2 / p := by
  field_simp

theorem finiteMixedLpCore_scale (p E : ℕ → ℝ) (hE : ∀ i, 0 ≤ E i)
    (n : ℕ) (hp : ∀ i ≤ n, 0 < p i) {a : ℝ} (ha : 0 < a) :
    finiteMixedLpCore (fun i => a * p i) E n ^ a = finiteMixedLpCore p E n := by
  induction n with
  | zero =>
    simp only [finiteMixedLpCore, ← Real.rpow_mul (hE 0)]
    rw [scaled_reciprocal_exponent ha.ne' (hp 0 (by omega)).ne']
  | succ n ih =>
    rw [finiteMixedLpCore, finiteMixedLpCore,
      Real.mul_rpow (finiteMixedLpCore_nonneg _ E hE n) (Real.rpow_nonneg (hE _) _),
      ih (fun i hi => hp i (by omega)), ← Real.rpow_mul (hE (n + 1))]
    congr 2
    rw [sub_mul, scaled_reciprocal_exponent ha.ne' (hp (n + 1) (by omega)).ne',
      scaled_reciprocal_exponent ha.ne' (hp n (by omega)).ne']

theorem finiteMixedLpBound_step (p E : ℕ → ℝ) (hE : ∀ i, 0 ≤ E i)
    (n : ℕ) (hp : ∀ i ≤ n, 0 < p i) :
    finiteMixedLpBound p E (n + 1) =
      E (n + 1) ^ (1 - 2 / p n) *
        finiteMixedLpBound (fun i => (2 / p n) * p i) E n ^ (2 / p n) := by
  cases n with
  | zero => simp only [finiteMixedLpBound, finiteMixedLpCore, mul_comm]
  | succ n =>
    have ha : 0 < 2 / p (n + 1) := div_pos (by norm_num) (hp (n + 1) (by omega))
    simp only [finiteMixedLpBound]
    rw [finiteMixedLpCore,
      Real.mul_rpow (finiteMixedLpCore_nonneg _ E hE n) (Real.rpow_nonneg (hE _) _),
      finiteMixedLpCore_scale p E hE n (fun i hi => hp i (by omega)) ha,
      ← Real.rpow_mul (hE (n + 1))]
    have he : (1 - 2 / ((2 / p (n + 1)) * p n)) * (2 / p (n + 1)) =
        2 / p (n + 1) - 2 / p n := by
      rw [sub_mul, one_mul, scaled_reciprocal_exponent ha.ne' (hp n (by omega)).ne']
    rw [he]
    ring

end Erdos3

end

section

namespace Erdos3

theorem finiteMixedLpCore_le_constant (p E : ℕ → ℝ) (hE : ∀ i, 0 ≤ E i)
    (n : ℕ) (hp : ∀ i ≤ n, 0 < p i)
    (hmono : ∀ i j, i ≤ j → j ≤ n → p j ≤ p i)
    {C : ℝ} (hC : 0 ≤ C) (hEC : ∀ i ≤ n, E i ≤ C) :
    finiteMixedLpCore p E n ≤ C ^ (2 / p n) := by
  induction n with
  | zero =>
    exact Real.rpow_le_rpow (hE 0) (hEC 0 (by omega))
      (le_of_lt (div_pos (by norm_num) (hp 0 (by omega))))
  | succ n ih =>
    have hd : 0 ≤ 2 / p (n + 1) - 2 / p n := by
      apply sub_nonneg.mpr
      apply (div_le_div_iff₀ (hp n (by omega)) (hp (n + 1) (by omega))).2
      nlinarith [hmono n (n + 1) (by omega) (by omega)]
    have hi := ih (fun i hi => hp i (by omega))
      (fun i j hij hj => hmono i j hij (by omega)) (fun i hi => hEC i (by omega))
    calc
      finiteMixedLpCore p E (n + 1) =
          finiteMixedLpCore p E n * E (n + 1) ^ (2 / p (n + 1) - 2 / p n) := rfl
      _ ≤ C ^ (2 / p n) * C ^ (2 / p (n + 1) - 2 / p n) :=
        mul_le_mul hi (Real.rpow_le_rpow (hE _) (hEC _ (by omega)) hd)
          (Real.rpow_nonneg (hE _) _) (Real.rpow_nonneg hC _)
      _ = C ^ (2 / p (n + 1)) := by
        rw [← Real.rpow_add_of_nonneg hC (le_of_lt (div_pos (by norm_num) (hp n (by omega)))) hd]
        congr 1
        ring

theorem finiteMixedLpBound_le_constant (p E : ℕ → ℝ) (hE : ∀ i, 0 ≤ E i)
    (n : ℕ) (hp : ∀ i < n, 2 ≤ p i)
    (hmono : ∀ i j, i ≤ j → j < n → p j ≤ p i)
    {C : ℝ} (hC : 0 ≤ C) (hEC : ∀ i ≤ n, E i ≤ C) :
    finiteMixedLpBound p E n ≤ C := by
  cases n with
  | zero => exact hEC 0 (by omega)
  | succ n =>
    have hp0 : ∀ i ≤ n, 0 < p i := fun i hi => lt_of_lt_of_le (by norm_num) (hp i (by omega))
    have hd : 0 ≤ 1 - 2 / p n := by
      apply sub_nonneg.mpr
      apply (div_le_one (hp0 n (by omega))).2
      exact hp n (by omega)
    have hi := finiteMixedLpCore_le_constant p E hE n hp0
      (fun i j hij hj => hmono i j hij (by omega)) hC (fun i hi => hEC i (by omega))
    calc
      finiteMixedLpBound p E (n + 1) =
          finiteMixedLpCore p E n * E (n + 1) ^ (1 - 2 / p n) := rfl
      _ ≤ C ^ (2 / p n) * C ^ (1 - 2 / p n) :=
        mul_le_mul hi (Real.rpow_le_rpow (hE _) (hEC _ (by omega)) hd)
          (Real.rpow_nonneg (hE _) _) (Real.rpow_nonneg hC _)
      _ = C := by
        rw [← Real.rpow_add_of_nonneg hC (le_of_lt (div_pos (by norm_num) (hp0 n (by omega)))) hd]
        have he : 2 / p n + (1 - 2 / p n) = 1 := by ring
        rw [he, Real.rpow_one]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

theorem finiteMixedLp_le_bound (w : ℕ → X → ℝ) (p : ℕ → ℝ) (n : ℕ)
    (hw : ∀ i < n, ∀ x, 0 ≤ w i x) (hp : ∀ i < n, 2 ≤ p i)
    (hmono : ∀ i j, i ≤ j → j < n → p j ≤ p i)
    (E : ℕ → ℝ) (hE : ∀ i, 0 ≤ E i) (f : (Fin n → X) → ℝ)
    (h : finiteSectionL2Control w n f E) :
    finiteMixedLp w p n f ≤ finiteMixedLpBound p E n := by
  induction n generalizing p with
  | zero => exact h
  | succ n ih =>
    have hp0 : ∀ i < n + 1, 0 < p i := fun i hi => lt_of_lt_of_le (by norm_num) (hp i hi)
    have hpn : 0 < p n := hp0 n (by omega)
    let a := 2 / p n
    have ha : 0 < a := div_pos (by norm_num) hpn
    let B := fun v : Fin n → X => finiteWeightedLp (w n) 2 (fun x => f (Fin.snoc v x))
    have hB : ∀ v, 0 ≤ B v := fun v => finiteWeightedLp_nonneg _ (hw n (by omega)) _ _
    have hscaled : ∀ i < n, 2 ≤ a * p i := by
      intro i hi
      dsimp [a]
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hpn).2
      nlinarith [hmono i n (by omega) (by omega)]
    have hscaledmono : ∀ i j, i ≤ j → j < n → a * p j ≤ a * p i := by
      intro i j hij hj
      exact mul_le_mul_of_nonneg_left (hmono i j hij (by omega)) ha.le
    have hih := ih (fun i => a * p i) (fun i hi => hw i (by omega)) hscaled
      hscaledmono B h.2
    have hpoint (v : Fin n → X) :
        finiteWeightedLp (w n) (p n) (fun x => f (Fin.snoc v x)) ≤
          E (n + 1) ^ (1 - a) * B v ^ a := by
      exact finiteWeightedLp_interpolate_two (w n) (hw n (by omega)) (hp n (by omega))
        (hE (n + 1)) _ (fun x => finiteSectionL2Control_pointwise w (n + 1) f E h _)
    have hC : 0 ≤ E (n + 1) ^ (1 - a) := Real.rpow_nonneg (hE _) _
    calc
      finiteMixedLp w p (n + 1) f ≤
          finiteMixedLp w p n (fun v => E (n + 1) ^ (1 - a) * B v ^ a) := by
        apply finiteMixedLp_mono w p n (fun i hi => hw i (by omega))
          (fun i hi => hp0 i (by omega))
        intro v
        rw [abs_of_nonneg (finiteWeightedLp_nonneg _ (hw n (by omega)) _ _),
          abs_of_nonneg (mul_nonneg hC (Real.rpow_nonneg (hB v) _))]
        exact hpoint v
      _ = E (n + 1) ^ (1 - a) *
          (finiteMixedLp w (fun i => a * p i) n B) ^ a := by
        rw [finiteMixedLp_smul w p n (fun i hi => hw i (by omega))
          (fun i hi => hp0 i (by omega)) hC]
        rw [finiteMixedLp_rpow w p n (fun i hi => hw i (by omega))
          (fun i hi => hp0 i (by omega)) ha B hB]
      _ ≤ E (n + 1) ^ (1 - a) * finiteMixedLpBound (fun i => a * p i) E n ^ a :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (finiteMixedLp_nonneg _ _ _ _) hih ha.le) hC
      _ = finiteMixedLpBound p E (n + 1) :=
        (finiteMixedLpBound_step p E hE n (fun i hi => hp0 i (by omega))).symm

theorem finiteMixedLp_interpolation (w : ℕ → X → ℝ) (p : ℕ → ℝ) (n : ℕ)
    (hw : ∀ i < n + 1, ∀ x, 0 ≤ w i x) (hp : ∀ i < n + 1, 2 ≤ p i)
    (hmono : ∀ i j, i ≤ j → j < n + 1 → p j ≤ p i)
    (E : ℕ → ℝ) (hE : ∀ i, 0 ≤ E i) (f : (Fin (n + 1) → X) → ℝ)
    (h : finiteSectionL2Control w (n + 1) f E) :
    finiteMixedLp w p (n + 1) f ≤ E 0 ^ (2 / p 0) *
      (∏ j ∈ Finset.range n, E (j + 1) ^ (2 / p (j + 1) - 2 / p j)) *
      E (n + 1) ^ (1 - 2 / p n) := by
  simpa only [finiteMixedLpBound, finiteMixedLpCore_eq_product] using
    finiteMixedLp_le_bound w p (n + 1) hw hp hmono E hE f h

end Erdos3

end

section

namespace Erdos3

variable {X : Type*} [Fintype X]

theorem finiteSectionCount_snoc {n : ℕ} (s : Fin n → Bool) (b : Bool) :
    finiteSectionCount (Fin.snoc s b) = finiteSectionCount s + (if b then 1 else 0) := by
  simp only [finiteSectionCount_succ, Fin.init_snoc, Fin.snoc_last]

theorem finiteSectionL2Control_sections (w : ℕ → X → ℝ) (n : ℕ)
    (hw : ∀ i < n, ∀ x, 0 ≤ w i x) (f : (Fin n → X) → ℝ) (E : ℕ → ℝ)
    (h : finiteSectionL2Control w n f E) (s : Fin n → Bool) (z : Fin n → X) :
    finiteSectionL2Norm w n s f z ≤ E (finiteSectionCount s) := by
  induction n generalizing E with
  | zero => simpa only [finiteSectionL2Control, finiteSectionL2Norm_zero, finiteSectionCount, Fin.sum_univ_zero] using h
  | succ n ih =>
    cases hs : s (Fin.last n) with
    | false =>
      rw [finiteSectionL2Norm_integrate w n (hw n (by omega)) s hs]
      have hi := ih (fun i hi => hw i (by omega)) _ E h.2 (Fin.init s) (Fin.init z)
      simpa only [finiteSectionCount_succ, hs, Bool.false_eq_true, ite_false, Nat.add_zero] using hi
    | true =>
      rw [finiteSectionL2Norm_fix w n s hs]
      have hi := ih (fun i hi => hw i (by omega)) _ (fun j => E (j + 1))
        (h.1 (z (Fin.last n))) (Fin.init s) (Fin.init z)
      simpa only [finiteSectionCount_succ, hs, ite_true] using hi

theorem finiteSectionL2Control_of_sections [Nonempty X] (w : ℕ → X → ℝ) (n : ℕ)
    (hw : ∀ i < n, ∀ x, 0 ≤ w i x) (f : (Fin n → X) → ℝ) (E : ℕ → ℝ)
    (h : ∀ s z, finiteSectionL2Norm w n s f z ≤ E (finiteSectionCount s)) :
    finiteSectionL2Control w n f E := by
  induction n generalizing E with
  | zero =>
    have hh := h (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
    simpa only [finiteSectionL2Control, finiteSectionL2Norm_zero, finiteSectionCount, Fin.sum_univ_zero] using hh
  | succ n ih =>
    constructor
    · intro a
      apply ih (fun i hi => hw i (by omega))
      intro s z
      have hh := h (Fin.snoc s true) (Fin.snoc z a)
      rw [finiteSectionL2Norm_fix w n _ (by simp only [Fin.snoc_last])] at hh
      simpa only [Fin.init_snoc, Fin.snoc_last, finiteSectionCount_snoc, ite_true] using hh
    · apply ih (fun i hi => hw i (by omega))
      intro s z
      let a : X := Classical.choice inferInstance
      have hh := h (Fin.snoc s false) (Fin.snoc z a)
      rw [finiteSectionL2Norm_integrate w n (hw n (by omega)) _
        (by simp only [Fin.snoc_last])] at hh
      simpa only [Fin.init_snoc, finiteSectionCount_snoc, Bool.false_eq_true, ite_false,
        Nat.add_zero] using hh

theorem finiteSectionL2Control_iff_sections [Nonempty X] (w : ℕ → X → ℝ) (n : ℕ)
    (hw : ∀ i < n, ∀ x, 0 ≤ w i x) (f : (Fin n → X) → ℝ) (E : ℕ → ℝ) :
    finiteSectionL2Control w n f E ↔
      ∀ s z, finiteSectionL2Norm w n s f z ≤ E (finiteSectionCount s) :=
  ⟨fun h => finiteSectionL2Control_sections w n hw f E h,
    finiteSectionL2Control_of_sections w n hw f E⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X] [Nonempty X]

theorem finiteMixedLp_interpolation_of_sections (w : ℕ → X → ℝ) (p : ℕ → ℝ) (n : ℕ)
    (hw : ∀ i < n + 1, ∀ x, 0 ≤ w i x) (hp : ∀ i < n + 1, 2 ≤ p i)
    (hmono : ∀ i j, i ≤ j → j < n + 1 → p j ≤ p i)
    (E : ℕ → ℝ) (hE : ∀ i, 0 ≤ E i) (f : (Fin (n + 1) → X) → ℝ)
    (h : ∀ s z, finiteSectionL2Norm w (n + 1) s f z ≤ E (finiteSectionCount s)) :
    finiteMixedLp w p (n + 1) f ≤ E 0 ^ (2 / p 0) *
      (∏ j ∈ Finset.range n, E (j + 1) ^ (2 / p (j + 1) - 2 / p j)) *
      E (n + 1) ^ (1 - 2 / p n) :=
  finiteMixedLp_interpolation w p n hw hp hmono E hE f
    (finiteSectionL2Control_of_sections w (n + 1) hw f E h)

theorem finiteMixedLp_le_constant_of_sections (w : ℕ → X → ℝ) (p : ℕ → ℝ) (n : ℕ)
    (hw : ∀ i < n, ∀ x, 0 ≤ w i x) (hp : ∀ i < n, 2 ≤ p i)
    (hmono : ∀ i j, i ≤ j → j < n → p j ≤ p i)
    (E : ℕ → ℝ) (hE : ∀ i, 0 ≤ E i) (f : (Fin n → X) → ℝ)
    (h : ∀ s z, finiteSectionL2Norm w n s f z ≤ E (finiteSectionCount s))
    {C : ℝ} (hC : 0 ≤ C) (hEC : ∀ i ≤ n, E i ≤ C) :
    finiteMixedLp w p n f ≤ C :=
  (finiteMixedLp_le_bound w p n hw hp hmono E hE f
    (finiteSectionL2Control_of_sections w n hw f E h)).trans
      (finiteMixedLpBound_le_constant p E hE n hp hmono hC hEC)

end Erdos3

end

section

namespace Erdos3

variable {X : Type*} [Fintype X] [Nonempty X]

theorem finiteMixedLp_permuted_le_constant (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (p : ℕ → ℝ) (n : ℕ) (hp : ∀ i < n, 2 ≤ p i)
    (hmono : ∀ i j, i ≤ j → j < n → p j ≤ p i)
    (e : Equiv.Perm (Fin n)) (E : ℕ → ℝ) (hE : ∀ i, 0 ≤ E i)
    (f : (Fin n → X) → ℝ)
    (h : ∀ s z, finiteSectionL2Norm (fun _ => w) n s f z ≤ E (finiteSectionCount s))
    {C : ℝ} (hC : 0 ≤ C) (hEC : ∀ i ≤ n, E i ≤ C) :
    finiteMixedLp (fun _ => w) p n (fun v => f (fun i => v (e i))) ≤ C :=
  finiteMixedLp_le_constant_of_sections (fun _ => w) p n (fun _ _ => hw) hp hmono E hE _
    (finiteSectionL2Bounds_permute w n e f E h) hC hEC

end Erdos3

end

end OAI
