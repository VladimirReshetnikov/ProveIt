import OAI.Combinatorics.Progressions.Estimates.RelativeFiberSlicePatch
import OAI.Combinatorics.Progressions.Probability.FiniteProbabilityLipschitz

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

noncomputable def finiteWeightedLp (w : X → ℝ) (p : ℝ) (f : X → ℝ) : ℝ :=
  (∑ x, w x * |f x| ^ p) ^ (1 / p)

theorem finiteWeightedMoment_nonneg (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (p : ℝ) (f : X → ℝ) : 0 ≤ ∑ x, w x * |f x| ^ p :=
  Finset.sum_nonneg (fun x _ => mul_nonneg (hw x) (Real.rpow_nonneg (abs_nonneg _) _))

theorem finiteWeightedLp_nonneg (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (p : ℝ) (f : X → ℝ) : 0 ≤ finiteWeightedLp w p f :=
  Real.rpow_nonneg (finiteWeightedMoment_nonneg w hw p f) _

theorem finiteWeightedLp_mono (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    {p : ℝ} (hp : 0 < p) (f g : X → ℝ) (hfg : ∀ x, |f x| ≤ |g x|) :
    finiteWeightedLp w p f ≤ finiteWeightedLp w p g := by
  unfold finiteWeightedLp
  apply Real.rpow_le_rpow (finiteWeightedMoment_nonneg w hw p f)
  · exact Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (abs_nonneg _) (hfg x) hp.le) (hw x))
  · positivity

theorem finiteWeightedLp_smul (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    {p c : ℝ} (hp : 0 < p) (hc : 0 ≤ c) (f : X → ℝ) :
    finiteWeightedLp w p (fun x => c * f x) = c * finiteWeightedLp w p f := by
  have hm : (∑ x, w x * |c * f x| ^ p) = c ^ p * ∑ x, w x * |f x| ^ p := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [abs_mul, abs_of_nonneg hc, Real.mul_rpow hc (abs_nonneg _)]
    ring
  unfold finiteWeightedLp
  rw [hm, Real.mul_rpow (Real.rpow_nonneg hc _) (finiteWeightedMoment_nonneg w hw p f),
    ← Real.rpow_mul hc]
  have he : p * (1 / p) = 1 := by field_simp
  rw [he, Real.rpow_one]

theorem finiteWeightedLp_rpow (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    {p a : ℝ} (hp : 0 < p) (ha : 0 < a) (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) :
    finiteWeightedLp w p (fun x => f x ^ a) =
      finiteWeightedLp w (a * p) f ^ a := by
  have hpoint (x : X) : |f x ^ a| ^ p = |f x| ^ (a * p) := by
    rw [abs_of_nonneg (Real.rpow_nonneg (hf x) _), abs_of_nonneg (hf x), Real.rpow_mul (hf x)]
  unfold finiteWeightedLp
  simp_rw [hpoint]
  rw [← Real.rpow_mul (finiteWeightedMoment_nonneg w hw (a * p) f)]
  congr 1
  field_simp

theorem finiteWeightedLp_two (w : X → ℝ) (f : X → ℝ) :
    finiteWeightedLp w 2 f = Real.sqrt (∑ x, w x * f x ^ 2) := by
  simp only [finiteWeightedLp, Real.rpow_two, sq_abs, Real.sqrt_eq_rpow]

end Erdos3

end

section

namespace Erdos3

variable {X : Type*} [Fintype X]

noncomputable def finiteMixedLp (w : ℕ → X → ℝ) (p : ℕ → ℝ) :
    (n : ℕ) → ((Fin n → X) → ℝ) → ℝ
  | 0, f => |f (fun i => Fin.elim0 i)|
  | n + 1, f => finiteMixedLp w p n
      (fun v => finiteWeightedLp (w n) (p n) (fun a => f (Fin.snoc v a)))

theorem finiteMixedLp_nonneg (w : ℕ → X → ℝ) (p : ℕ → ℝ) (n : ℕ)
    (f : (Fin n → X) → ℝ) : 0 ≤ finiteMixedLp w p n f := by
  induction n with
  | zero => exact abs_nonneg _
  | succ n ih => exact ih _

theorem finiteMixedLp_mono (w : ℕ → X → ℝ) (p : ℕ → ℝ) (n : ℕ)
    (hw : ∀ i < n, ∀ x, 0 ≤ w i x) (hp : ∀ i < n, 0 < p i)
    (f g : (Fin n → X) → ℝ) (hfg : ∀ v, |f v| ≤ |g v|) :
    finiteMixedLp w p n f ≤ finiteMixedLp w p n g := by
  induction n with
  | zero => exact hfg _
  | succ n ih =>
    apply ih (fun i hi => hw i (by omega)) (fun i hi => hp i (by omega))
    intro v
    rw [abs_of_nonneg (finiteWeightedLp_nonneg (w n) (hw n (by omega)) _ _),
      abs_of_nonneg (finiteWeightedLp_nonneg (w n) (hw n (by omega)) _ _)]
    exact finiteWeightedLp_mono (w n) (hw n (by omega)) (hp n (by omega)) _ _
      (fun a => hfg (Fin.snoc v a))

theorem finiteMixedLp_smul (w : ℕ → X → ℝ) (p : ℕ → ℝ) (n : ℕ)
    (hw : ∀ i < n, ∀ x, 0 ≤ w i x) (hp : ∀ i < n, 0 < p i)
    {c : ℝ} (hc : 0 ≤ c) (f : (Fin n → X) → ℝ) :
    finiteMixedLp w p n (fun v => c * f v) = c * finiteMixedLp w p n f := by
  induction n with
  | zero =>
    change |c * f _| = c * |f _|
    rw [abs_mul, abs_of_nonneg hc]
  | succ n ih =>
    simp only [finiteMixedLp,
      finiteWeightedLp_smul (w n) (hw n (by omega)) (hp n (by omega)) hc]
    exact ih (fun i hi => hw i (by omega)) (fun i hi => hp i (by omega)) _

theorem finiteMixedLp_rpow (w : ℕ → X → ℝ) (p : ℕ → ℝ) (n : ℕ)
    (hw : ∀ i < n, ∀ x, 0 ≤ w i x) (hp : ∀ i < n, 0 < p i)
    {a : ℝ} (ha : 0 < a) (f : (Fin n → X) → ℝ) (hf : ∀ v, 0 ≤ f v) :
    finiteMixedLp w p n (fun v => f v ^ a) =
      finiteMixedLp w (fun i => a * p i) n f ^ a := by
  induction n with
  | zero => simp only [finiteMixedLp, abs_of_nonneg (hf _),
      abs_of_nonneg (Real.rpow_nonneg (hf _) _)]
  | succ n ih =>
    simp only [finiteMixedLp,
      finiteWeightedLp_rpow (w n) (hw n (by omega)) (hp n (by omega)) ha _
        (fun x => hf _)]
    exact ih (fun i hi => hw i (by omega)) (fun i hi => hp i (by omega)) _
      (fun v => finiteWeightedLp_nonneg (w n) (hw n (by omega)) _ _)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

noncomputable def finiteSectionIntegral (w : ℕ → X → ℝ) :
    (n : ℕ) → (Fin n → Bool) → ((Fin n → X) → ℝ) → (Fin n → X) → ℝ
  | 0, _, f, _ => f (fun i => Fin.elim0 i)
  | n + 1, s, f, z =>
      if s (Fin.last n) then
        finiteSectionIntegral w n (Fin.init s)
          (fun v => f (Fin.snoc v (z (Fin.last n)))) (Fin.init z)
      else
        finiteSectionIntegral w n (Fin.init s)
          (fun v => ∑ a, w n a * f (Fin.snoc v a)) (Fin.init z)

noncomputable def finiteSectionL2Norm (w : ℕ → X → ℝ) (n : ℕ)
    (s : Fin n → Bool) (f : (Fin n → X) → ℝ) (z : Fin n → X) : ℝ :=
  Real.sqrt (finiteSectionIntegral w n s (fun v => f v ^ 2) z)

def finiteSectionCount {n : ℕ} (s : Fin n → Bool) : ℕ :=
  ∑ i, if s i then 1 else 0

theorem finiteSectionCount_succ (n : ℕ) (s : Fin (n + 1) → Bool) :
    finiteSectionCount s = finiteSectionCount (Fin.init s) +
      (if s (Fin.last n) then 1 else 0) :=
  Fin.sum_univ_castSucc _

theorem finiteSectionIntegral_nonneg (w : ℕ → X → ℝ) (n : ℕ)
    (hw : ∀ i < n, ∀ x, 0 ≤ w i x) (s : Fin n → Bool)
    (f : (Fin n → X) → ℝ) (hf : ∀ v, 0 ≤ f v) (z : Fin n → X) :
    0 ≤ finiteSectionIntegral w n s f z := by
  induction n with
  | zero => exact hf _
  | succ n ih =>
    simp only [finiteSectionIntegral]
    split
    · exact ih (fun i hi => hw i (by omega)) _ _ (fun v => hf _) _
    · exact ih (fun i hi => hw i (by omega)) _ _
        (fun v => Finset.sum_nonneg (fun x _ => mul_nonneg (hw n (by omega) x) (hf _))) _

theorem finiteSectionL2Norm_zero (w : ℕ → X → ℝ) (s : Fin 0 → Bool)
    (f : (Fin 0 → X) → ℝ) (z : Fin 0 → X) :
    finiteSectionL2Norm w 0 s f z = |f (fun i => Fin.elim0 i)| := by
  simp only [finiteSectionL2Norm, finiteSectionIntegral, Real.sqrt_sq_eq_abs]

theorem finiteSectionL2Norm_fix (w : ℕ → X → ℝ) (n : ℕ)
    (s : Fin (n + 1) → Bool) (hs : s (Fin.last n) = true)
    (f : (Fin (n + 1) → X) → ℝ) (z : Fin (n + 1) → X) :
    finiteSectionL2Norm w (n + 1) s f z =
      finiteSectionL2Norm w n (Fin.init s)
        (fun v => f (Fin.snoc v (z (Fin.last n)))) (Fin.init z) := by
  simp only [finiteSectionL2Norm, finiteSectionIntegral, hs, ite_true]

theorem finiteSectionL2Norm_integrate (w : ℕ → X → ℝ) (n : ℕ)
    (hw : ∀ x, 0 ≤ w n x) (s : Fin (n + 1) → Bool) (hs : s (Fin.last n) = false)
    (f : (Fin (n + 1) → X) → ℝ) (z : Fin (n + 1) → X) :
    finiteSectionL2Norm w (n + 1) s f z =
      finiteSectionL2Norm w n (Fin.init s)
        (fun v => finiteWeightedLp (w n) 2 (fun a => f (Fin.snoc v a))) (Fin.init z) := by
  have hB : (fun v => finiteWeightedLp (w n) 2 (fun a => f (Fin.snoc v a)) ^ 2) =
      (fun v => ∑ a, w n a * f (Fin.snoc v a) ^ 2) := by
    funext v
    rw [finiteWeightedLp_two, Real.sq_sqrt]
    exact Finset.sum_nonneg (fun x _ => mul_nonneg (hw x) (sq_nonneg _))
  simp only [finiteSectionL2Norm, finiteSectionIntegral, hs, Bool.false_eq_true, ite_false, hB]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

theorem finiteWeightedLp_interpolate_two (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    {p C : ℝ} (hp : 2 ≤ p) (hC : 0 ≤ C) (f : X → ℝ)
    (hf : ∀ x, |f x| ≤ C) :
    finiteWeightedLp w p f ≤ C ^ (1 - 2 / p) * finiteWeightedLp w 2 f ^ (2 / p) := by
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hm : (∑ x, w x * |f x| ^ p) ≤ C ^ (p - 2) * ∑ x, w x * |f x| ^ (2 : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x _
    have he : p = (p - 2) + 2 := by ring
    have hxp : |f x| ^ p = |f x| ^ (p - 2) * |f x| ^ (2 : ℝ) := by
      conv_lhs => rw [he]
      exact Real.rpow_add_of_nonneg (abs_nonneg _) (sub_nonneg.mpr hp) (by norm_num)
    rw [hxp]
    calc
      w x * (|f x| ^ (p - 2) * |f x| ^ (2 : ℝ)) ≤
          w x * (C ^ (p - 2) * |f x| ^ (2 : ℝ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow (abs_nonneg _) (hf x) (sub_nonneg.mpr hp))
          (Real.rpow_nonneg (abs_nonneg _) _)) (hw x)
      _ = C ^ (p - 2) * (w x * |f x| ^ (2 : ℝ)) := by ring
  have hpow := Real.rpow_le_rpow (finiteWeightedMoment_nonneg w hw p f) hm
    (show 0 ≤ 1 / p by positivity)
  have he : (p - 2) * (1 / p) = 1 - 2 / p := by field_simp
  have he2 : (1 / (2 : ℝ)) * (2 / p) = 1 / p := by ring
  simpa only [finiteWeightedLp,
    Real.mul_rpow (Real.rpow_nonneg hC _) (finiteWeightedMoment_nonneg w hw 2 f),
    ← Real.rpow_mul hC, he,
    ← Real.rpow_mul (finiteWeightedMoment_nonneg w hw 2 f), he2] using hpow

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

noncomputable def finiteWeightedL2Map (w : X → ℝ) : (X → ℝ) →ₗ[ℝ] EuclideanSpace ℝ X where
  toFun f := WithLp.toLp 2 (fun x => Real.sqrt (w x) * f x)
  map_add' f g := by
    ext x
    change Real.sqrt (w x) * (f x + g x) = Real.sqrt (w x) * f x + Real.sqrt (w x) * g x
    ring
  map_smul' c f := by
    ext x
    change Real.sqrt (w x) * (c * f x) = c * (Real.sqrt (w x) * f x)
    ring

theorem norm_finiteWeightedL2Map (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (f : X → ℝ) :
    ‖finiteWeightedL2Map w f‖ = finiteWeightedLp w 2 f := by
  rw [EuclideanSpace.norm_eq, finiteWeightedLp_two]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  change |Real.sqrt (w x) * f x| ^ 2 = w x * f x ^ 2
  rw [sq_abs, mul_pow, Real.sq_sqrt (hw x)]

theorem finiteWeightedLp_two_sum_le {J : Type*} (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (D : Finset J) (f : J → X → ℝ) :
    finiteWeightedLp w 2 (fun x => ∑ j ∈ D, f j x) ≤ ∑ j ∈ D, finiteWeightedLp w 2 (f j) := by
  have he : (fun x => ∑ j ∈ D, f j x) = ∑ j ∈ D, f j := by
    funext x
    simp only [Finset.sum_apply]
  rw [he, ← norm_finiteWeightedL2Map w hw, map_sum]
  exact (norm_sum_le D (fun j => finiteWeightedL2Map w (f j))).trans_eq
    (Finset.sum_congr rfl (fun j _ => norm_finiteWeightedL2Map w hw (f j)))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

theorem finiteWeightedLp_rpow_self (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    {p : ℝ} (hp : 0 < p) (f : X → ℝ) :
    finiteWeightedLp w p f ^ p = ∑ x, w x * |f x| ^ p := by
  unfold finiteWeightedLp
  rw [one_div, Real.rpow_inv_rpow (finiteWeightedMoment_nonneg w hw p f) hp.ne']

theorem finiteWeightedLp_zero_support (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    {p : ℝ} (hp : 0 < p) (f : X → ℝ) (h : finiteWeightedLp w p f = 0)
    (x : X) (hx : w x ≠ 0) : f x = 0 := by
  have hm : (∑ x, w x * |f x| ^ p) = 0 := by
    rw [← finiteWeightedLp_rpow_self w hw hp f, h, Real.zero_rpow hp.ne']
  have ht : w x * |f x| ^ p = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun y _ => mul_nonneg (hw y) (Real.rpow_nonneg (abs_nonneg _) _))).mp hm x (Finset.mem_univ x)
  have ha : |f x| ^ p = 0 := (mul_eq_zero.mp ht).resolve_left hx
  exact abs_eq_zero.mp ((Real.rpow_eq_zero (abs_nonneg _) hp.ne').mp ha)

theorem finiteWeightedLp_abs (w : X → ℝ) (p : ℝ) (f : X → ℝ) :
    finiteWeightedLp w p (fun x => |f x|) = finiteWeightedLp w p f := by
  simp only [finiteWeightedLp, abs_abs]

end Erdos3

end

section

namespace Erdos3

variable {X : Type*} [Fintype X]

noncomputable def finiteMaskedLpStep (w : X → ℝ) (p : ℝ) (b : Bool) (x₀ : X)
    (n : ℕ) (f : (Fin (n + 1) → X) → ℝ) (v : Fin n → X) : ℝ :=
  if b then finiteWeightedLp w p (fun a => f (Fin.snoc v a)) else f (Fin.snoc v x₀)

noncomputable def finiteMaskedMixedLp (w : ℕ → X → ℝ) (p : ℕ → ℝ)
    (s : ℕ → Bool) (x₀ : X) : (n : ℕ) → ((Fin n → X) → ℝ) → ℝ
  | 0, f => |f (fun i => Fin.elim0 i)|
  | n + 1, f => finiteMaskedMixedLp w p s x₀ n (finiteMaskedLpStep (w n) (p n) (s n) x₀ n f)

theorem finiteMaskedMixedLp_nonneg (w : ℕ → X → ℝ) (p : ℕ → ℝ)
    (s : ℕ → Bool) (x₀ : X) (n : ℕ) (f : (Fin n → X) → ℝ) :
    0 ≤ finiteMaskedMixedLp w p s x₀ n f := by
  induction n with
  | zero => exact abs_nonneg _
  | succ n ih => exact ih _

theorem finiteMaskedMixedLp_all (w : ℕ → X → ℝ) (p : ℕ → ℝ)
    (x₀ : X) (n : ℕ) (f : (Fin n → X) → ℝ) :
    finiteMaskedMixedLp w p (fun _ => true) x₀ n f = finiteMixedLp w p n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [finiteMaskedMixedLp, finiteMixedLp, ih]
    rfl

end Erdos3

end

section

namespace Erdos3

variable {X : Type*} [Fintype X]

def finiteSectionL2Control (w : ℕ → X → ℝ) :
    (n : ℕ) → ((Fin n → X) → ℝ) → (ℕ → ℝ) → Prop
  | 0, f, E => |f (fun i => Fin.elim0 i)| ≤ E 0
  | n + 1, f, E =>
      (∀ a, finiteSectionL2Control w n (fun v => f (Fin.snoc v a))
        (fun j => E (j + 1))) ∧
      finiteSectionL2Control w n
        (fun v => finiteWeightedLp (w n) 2 (fun a => f (Fin.snoc v a))) E

theorem finiteSectionL2Control_pointwise (w : ℕ → X → ℝ) (n : ℕ)
    (f : (Fin n → X) → ℝ) (E : ℕ → ℝ) (h : finiteSectionL2Control w n f E) :
    ∀ v, |f v| ≤ E n := by
  induction n generalizing E with
  | zero =>
    intro v
    have hv : v = (fun i => Fin.elim0 i) := Subsingleton.elim _ _
    simpa only [hv, finiteSectionL2Control] using h
  | succ n ih =>
    intro v
    have hs := ih _ _ (h.1 (v (Fin.last n))) (Fin.init v)
    simpa only [Fin.snoc_init_self] using hs

theorem finiteSectionL2Control_norm (w : ℕ → X → ℝ) (n : ℕ)
    (f : (Fin n → X) → ℝ) (E : ℕ → ℝ) (h : finiteSectionL2Control w n f E) :
    finiteMixedLp w (fun _ => 2) n f ≤ E 0 := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih _ h.2

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem finiteSectionCount_eq_card (n : ℕ) (s : Fin n → Bool) :
    finiteSectionCount s = Fintype.card {i : Fin n // s i = true} := by
  rw [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]
  rfl

theorem finiteSection_free_card (n : ℕ) (s : Fin n → Bool) :
    Fintype.card {i : Fin n // s i ≠ true} = n - finiteSectionCount s := by
  rw [Fintype.card_subtype_compl, Fintype.card_fin, finiteSectionCount_eq_card]

noncomputable def finiteSectionFreeOrder (n : ℕ) (s : Fin n → Bool) :
    Fin (n - finiteSectionCount s) ≃o {i : Fin n // s i ≠ true} :=
  Fintype.orderIsoFinOfCardEq _ (finiteSection_free_card n s)

noncomputable def finiteSectionFill {X : Type*} (n : ℕ) (s : Fin n → Bool)
    (z : Fin n → X) (v : Fin (n - finiteSectionCount s) → X) : Fin n → X :=
  finiteSplitPoint (fun i => s i = true) (fun i => z i)
    (fun i => v ((finiteSectionFreeOrder n s).symm i))

theorem finiteSectionFill_fixed {X : Type*} (n : ℕ) (s : Fin n → Bool)
    (z : Fin n → X) (v : Fin (n - finiteSectionCount s) → X) (i : Fin n) (hi : s i = true) :
    finiteSectionFill n s z v i = z i := by
  exact finiteSplitPoint_fixed (fun i => s i = true) _ _ ⟨i, hi⟩

theorem finiteSectionFill_free {X : Type*} (n : ℕ) (s : Fin n → Bool)
    (z : Fin n → X) (v : Fin (n - finiteSectionCount s) → X) (i : Fin (n - finiteSectionCount s)) :
    finiteSectionFill n s z v (finiteSectionFreeOrder n s i) = v i := by
  unfold finiteSectionFill
  rw [finiteSplitPoint_free, OrderIso.symm_apply_apply]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

noncomputable def finiteSectionWeight (w : X → ℝ) (b : Bool) (z x : X) : ℝ := by
  classical
  exact if b then (if x = z then 1 else 0) else w x

omit [Fintype X] in
theorem finiteSectionWeight_false (w : X → ℝ) (z x : X) :
    finiteSectionWeight w false z x = w x := by
  simp only [finiteSectionWeight, Bool.false_eq_true, ite_false]

theorem finiteSectionWeight_sum_true (w : X → ℝ) (z : X) (f : X → ℝ) :
    (∑ x, finiteSectionWeight w true z x * f x) = f z := by
  classical
  simp [finiteSectionWeight]

theorem finiteSectionIntegral_eq_product (w : ℕ → X → ℝ) (n : ℕ)
    (s : Fin n → Bool) (f : (Fin n → X) → ℝ) (z : Fin n → X) :
    finiteSectionIntegral w n s f z =
      finiteProductIntegral (fun i : Fin n => finiteSectionWeight (w i) (s i) (z i)) f := by
  induction n with
  | zero => rw [finiteSectionIntegral, finiteProductIntegral_zero]
  | succ n ih =>
    rw [finiteProductIntegral_snoc]
    cases hs : s (Fin.last n) with
    | false =>
      simp only [finiteSectionIntegral, hs, Bool.false_eq_true, ite_false,
        finiteSectionWeight_false, Fin.val_last, ih]
      rfl
    | true =>
      simp only [finiteSectionIntegral, hs, ite_true, finiteSectionWeight_sum_true, ih]
      rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {Ω J L : Type*} [Fintype Ω]

theorem FiniteProbabilityWeights.familyL2_eq (p : FiniteProbabilityWeights Ω)
    (E : Finset L) (g : L → Ω → ℝ) :
    finiteWeightedLp (fun v : ↥E × Ω => p.weight v.2) 2 (fun v => g v.1 v.2) =
      Real.sqrt (∑ l ∈ E, p.mean (fun x => g l x ^ 2)) := by
  rw [finiteWeightedLp_two, Fintype.sum_prod_type]
  congr 1
  exact Finset.sum_coe_sort E (fun l => p.mean (fun x => g l x ^ 2))

theorem FiniteProbabilityWeights.sqrt_sum_mean_sq_triangle (p : FiniteProbabilityWeights Ω)
    (D : Finset J) (E : Finset L) (f : J → L → Ω → ℝ) :
    Real.sqrt (∑ l ∈ E, p.mean (fun x => (∑ j ∈ D, f j l x) ^ 2)) ≤
      ∑ j ∈ D, Real.sqrt (∑ l ∈ E, p.mean (fun x => f j l x ^ 2)) := by
  have h := finiteWeightedLp_two_sum_le (fun v : ↥E × Ω => p.weight v.2)
    (fun v => p.nonneg v.2) D (fun j v => f j v.1 v.2)
  rw [p.familyL2_eq E (fun l x => ∑ j ∈ D, f j l x)] at h
  simpa only [p.familyL2_eq] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

theorem finiteSectionCount_permute {n : ℕ} (e : Equiv.Perm (Fin n)) (s : Fin n → Bool) :
    finiteSectionCount (fun i => s (e i)) = finiteSectionCount s := by
  unfold finiteSectionCount
  exact Fintype.sum_equiv e _ _ (fun i => rfl)

theorem finiteSectionIntegral_permute (w : X → ℝ) (n : ℕ) (e : Equiv.Perm (Fin n))
    (s : Fin n → Bool) (f : (Fin n → X) → ℝ) (z : Fin n → X) :
    finiteSectionIntegral (fun _ => w) n s (fun v => f (fun i => v (e i))) z =
      finiteSectionIntegral (fun _ => w) n (fun i => s (e i)) f (fun i => z (e i)) := by
  rw [finiteSectionIntegral_eq_product, finiteSectionIntegral_eq_product]
  have h := finiteProductIntegral_reindex e
    (fun i => finiteSectionWeight w (s i) (z i)) (fun v => f (fun i => v (e i)))
  simpa only [Equiv.symm_apply_apply] using h.symm

theorem finiteSectionL2Norm_permute (w : X → ℝ) (n : ℕ) (e : Equiv.Perm (Fin n))
    (s : Fin n → Bool) (f : (Fin n → X) → ℝ) (z : Fin n → X) :
    finiteSectionL2Norm (fun _ => w) n s (fun v => f (fun i => v (e i))) z =
      finiteSectionL2Norm (fun _ => w) n (fun i => s (e i)) f (fun i => z (e i)) := by
  exact congrArg Real.sqrt
    (finiteSectionIntegral_permute w n e s (fun v => f v ^ 2) z)

theorem finiteSectionL2Bounds_permute (w : X → ℝ) (n : ℕ) (e : Equiv.Perm (Fin n))
    (f : (Fin n → X) → ℝ) (E : ℕ → ℝ)
    (h : ∀ s z, finiteSectionL2Norm (fun _ => w) n s f z ≤ E (finiteSectionCount s)) :
    ∀ s z, finiteSectionL2Norm (fun _ => w) n s (fun v => f (fun i => v (e i))) z ≤
      E (finiteSectionCount s) := by
  intro s z
  rw [finiteSectionL2Norm_permute]
  have hh := h (fun i => s (e i)) (fun i => z (e i))
  simpa only [finiteSectionCount_permute] using hh

end Erdos3

end

end OAI
