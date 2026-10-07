/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import Mathlib.Probability.Distributions.Uniform
import OAI.Combinatorics.Progressions.Geometry.IndependentProductTransport

namespace OAI

section

namespace Erdos3

open scoped ENNReal Classical

theorem pmf_map_injective_cap {X Y : Type*} (p : PMF X) (f : X → Y)
    (hf : Function.Injective f) {C : ℝ≥0∞} (hp : ∀ x, p x ≤ C) (y : Y) :
    p.map f y ≤ C := by
  by_cases hy : y ∈ Set.range f
  · obtain ⟨x, rfl⟩ := hy
    rw [pmf_map_injective_at p f hf]
    exact hp x
  · rw [pmf_map_zero_off_range p f y hy]
    exact bot_le

theorem pmf_bind_point_cap {X Y : Type*} (p : PMF X) (q : X → PMF Y)
    {C : ℝ≥0∞} (y : Y) (hq : ∀ x, q x y ≤ C) : p.bind q y ≤ C := by
  rw [PMF.bind_apply]
  calc
    _ ≤ ∑' x, p x * C := ENNReal.tsum_le_tsum (fun x => by gcongr; exact hq x)
    _ = C := by rw [ENNReal.tsum_mul_right, p.tsum_coe, one_mul]

theorem pmf_bind_injective_toReal_cap {X Y Z : Type*} (p : PMF X) (q : PMF Y)
    (f : Y → X → Z) (hf : ∀ y, Function.Injective (f y))
    {C : ℝ} (hC : 0 ≤ C) (hp : ∀ x, (p x).toReal ≤ C) (z : Z) :
    ((q.bind (fun y => p.map (f y))) z).toReal ≤ C := by
  have hp' (x : X) : p x ≤ ENNReal.ofReal C := by
    rw [← ENNReal.ofReal_toReal (p.apply_ne_top x)]
    exact ENNReal.ofReal_le_ofReal (hp x)
  have h := pmf_bind_point_cap q (fun y => p.map (f y)) z
    (fun y => pmf_map_injective_cap p (f y) (hf y) hp' z)
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans_eq (ENNReal.toReal_ofReal hC)

theorem pmf_map_toReal_indicator {X Y : Type*} [DecidableEq Y] (p : PMF X) (f : X → Y) (y : Y) :
    (p.map f y).toReal = ∑' x, (p x).toReal * (if f x = y then 1 else 0) := by
  rw [PMF.map_apply, ENNReal.tsum_toReal_eq]
  · apply tsum_congr
    intro x
    by_cases h : y = f x
    · simp [h]
    · simp [h, Ne.symm h]
  · intro x
    split_ifs <;> first | exact p.apply_ne_top x | exact ENNReal.zero_ne_top

theorem pmf_point_indicator_norm {X Y : Type*} [DecidableEq Y] (p : PMF X) (f : X → Y) (y : Y) :
    ‖∑' x, ((p x).toReal : ℂ) * (if f x = y then 1 else 0)‖ = (p.map f y).toReal := by
  calc
    _ = ‖((∑' x, (p x).toReal * (if f x = y then 1 else 0) : ℝ) : ℂ)‖ := by
      simp only [Complex.ofReal_tsum, Complex.ofReal_mul, apply_ite, Complex.ofReal_one, Complex.ofReal_zero]
    _ = _ := by rw [← pmf_map_toReal_indicator, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

def baseArrayJoin {K I X : Type*} (tail : K × I → X) (base : I → X) : Option K × I → X :=
  fun z => match z.1 with | none => base z.2 | some k => tail (k,z.2)

theorem baseArrayJoin_injective {K I X : Type*} (tail : K × I → X) :
    Function.Injective (baseArrayJoin tail) := by
  intro b c he
  funext i
  exact congrFun he (none,i)

theorem baseArrayJoin_eta {K I X : Type*} (z : Option K × I → X) :
    baseArrayJoin (fun k => z (some k.1,k.2)) (fun i => z (none,i)) = z := by
  funext k
  rcases k with ⟨k,i⟩
  cases k <;> rfl

theorem independentProductPMF_base_split {K I X : Type*} [Fintype K] [Fintype I]
    [Countable X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (p : Option K × I → PMF X) :
    independentProductPMF p =
      (independentProductPMF (fun k : K × I => p (some k.1,k.2))).bind
        (fun tail => (independentProductPMF (fun i => p (none,i))).map (baseArrayJoin tail)) := by
  ext z
  let tail := fun k : K × I => z (some k.1,k.2)
  let base := fun i : I => z (none,i)
  have hz : baseArrayJoin tail base = z := baseArrayJoin_eta z
  rw [← hz, PMF.bind_apply, tsum_eq_single tail]
  · rw [pmf_map_injective_at _ _ (baseArrayJoin_injective tail)]
    simp only [independentProductPMF_apply, Fintype.prod_prod_type, Fintype.prod_option, baseArrayJoin]
    exact mul_comm _ _
  · intro other hother
    have hr : baseArrayJoin tail base ∉ Set.range (baseArrayJoin other) := by
      rintro ⟨b, he⟩
      apply hother
      funext k
      exact congrFun he (some k.1,k.2)
    rw [pmf_map_zero_off_range _ _ _ hr, mul_zero]

theorem independentProductPMF_base_cap {K I X Y : Type*} [Fintype K] [Fintype I]
    [Countable X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (p : Option K × I → PMF X) (f : (Option K × I → X) → Y)
    (hf : ∀ tail, Function.Injective (fun base => f (baseArrayJoin tail base)))
    (C : I → ℝ) (hC : ∀ i, 0 ≤ C i) (hp : ∀ i x, (p (none,i) x).toReal ≤ C i) (y : Y) :
    ((independentProductPMF p).map f y).toReal ≤ ∏ i, C i := by
  rw [independentProductPMF_base_split, PMF.map_bind]
  simp_rw [PMF.map_comp]
  apply pmf_bind_injective_toReal_cap _ _ _ hf (Finset.prod_nonneg (fun i _ => hC i))
  intro base
  rw [independentProductPMF_toReal]
  exact Finset.prod_le_prod₀ (fun i _ => ENNReal.toReal_nonneg) (fun i _ => hp i (base i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

abbrev SelectedCoefficientComplement {A J : Type*} (e : A ↪ J) :=
  {j : J // j ∉ Set.range e}

noncomputable def selectedCoefficientComplementFill {A J X : Type*}
    (e : A ↪ J) (x0 : X) (tail : SelectedCoefficientComplement e → X) : J → X :=
  Function.extend Subtype.val tail (fun _ => x0)

noncomputable def selectedCoefficientJoin {A J X : Type*}
    (e : A ↪ J) (x0 : X) (tail : SelectedCoefficientComplement e → X)
    (selected : A → X) : J → X :=
  Function.extend e selected (selectedCoefficientComplementFill e x0 tail)

@[simp] theorem selectedCoefficientJoin_selected {A J X : Type*}
    (e : A ↪ J) (x0 : X) (tail : SelectedCoefficientComplement e → X)
    (selected : A → X) (a : A) :
    selectedCoefficientJoin e x0 tail selected (e a) = selected a :=
  e.injective.extend_apply _ _ _

@[simp] theorem selectedCoefficientJoin_complement {A J X : Type*}
    (e : A ↪ J) (x0 : X) (tail : SelectedCoefficientComplement e → X)
    (selected : A → X) (k : SelectedCoefficientComplement e) :
    selectedCoefficientJoin e x0 tail selected k.val = tail k := by
  rw [selectedCoefficientJoin, Function.extend_apply' _ _ _ k.property]
  exact Subtype.val_injective.extend_apply _ _ k

theorem selectedCoefficientJoin_injective {A J X : Type*}
    (e : A ↪ J) (x0 : X) (tail : SelectedCoefficientComplement e → X) :
    Function.Injective (selectedCoefficientJoin e x0 tail) := by
  intro b c he
  funext a
  have h := congrFun he (e a)
  simpa only [selectedCoefficientJoin_selected] using h

theorem selectedCoefficientJoin_eta {A J X : Type*}
    (e : A ↪ J) (x0 : X) (z : J → X) :
    selectedCoefficientJoin e x0 (fun k => z k.val) (fun a => z (e a)) = z := by
  funext j
  by_cases hj : j ∈ Set.range e
  · obtain ⟨a, rfl⟩ := hj
    exact selectedCoefficientJoin_selected e x0 _ _ a
  · exact selectedCoefficientJoin_complement e x0 _ _ ⟨j, hj⟩

theorem prod_selected_complement {A J M : Type*} [Fintype A] [Fintype J]
    [CommMonoid M] (e : A ↪ J) (f : J → M) :
    (∏ j, f j) = (∏ k : SelectedCoefficientComplement e, f k.val) * ∏ a, f (e a) := by
  let : Fintype {j : J // j ∈ Set.range e} := Subtype.fintype (fun j => j ∈ Set.range e)
  have he : (∏ a, f (e a)) = ∏ k : {j : J // j ∈ Set.range e}, f k.val :=
    Fintype.prod_equiv (Equiv.ofInjective e e.injective) _ _ (fun _ => rfl)
  rw [he, mul_comm]
  exact (Fintype.prod_subtype_mul_prod_subtype (fun j => j ∈ Set.range e) f).symm

theorem independentProductPMF_selected_split {A J X : Type*}
    [Fintype A] [Fintype J] [Countable X]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (e : A ↪ J) (x0 : X) (p : J → PMF X) :
    independentProductPMF p =
      (independentProductPMF (fun k : SelectedCoefficientComplement e => p k.val)).bind
        (fun tail => (independentProductPMF (fun a => p (e a))).map
          (selectedCoefficientJoin e x0 tail)) := by
  ext z
  let tail := fun k : SelectedCoefficientComplement e => z k.val
  let selected := fun a : A => z (e a)
  have hz : selectedCoefficientJoin e x0 tail selected = z :=
    selectedCoefficientJoin_eta e x0 z
  rw [← hz, PMF.bind_apply, tsum_eq_single tail]
  · rw [pmf_map_injective_at _ _ (selectedCoefficientJoin_injective e x0 tail)]
    simp only [independentProductPMF_apply]
    rw [prod_selected_complement e]
    simp only [selectedCoefficientJoin_complement, selectedCoefficientJoin_selected]
  · intro other hother
    have hr : selectedCoefficientJoin e x0 tail selected ∉
        Set.range (selectedCoefficientJoin e x0 other) := by
      rintro ⟨b, he⟩
      apply hother
      funext k
      have h := congrFun he k.val
      simpa only [selectedCoefficientJoin_complement] using h
    rw [pmf_map_zero_off_range _ _ _ hr, mul_zero]

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem independentProductPMF_uniform {J X : Type*}
    [Fintype J] [Fintype X] [Nonempty X]
    [MeasurableSpace X] [MeasurableSingletonClass X] :
    independentProductPMF (fun _ : J => PMF.uniformOfFintype X) =
      PMF.uniformOfFintype (J → X) := by
  ext x
  simp only [independentProductPMF_apply, PMF.uniformOfFintype_apply,
    Fintype.card_fun, Finset.prod_const, Finset.card_univ, Nat.cast_pow, ENNReal.inv_pow]

theorem uniformOfFintype_selected_split {A J X : Type*}
    [Fintype A] [Fintype J] [Fintype X] [Nonempty X]
    (e : A ↪ J) (x0 : X) :
    PMF.uniformOfFintype (J → X) =
      (PMF.uniformOfFintype (SelectedCoefficientComplement e → X)).bind
        (fun tail => (PMF.uniformOfFintype (A → X)).map
          (selectedCoefficientJoin e x0 tail)) := by
  let : MeasurableSpace X := ⊤
  have : MeasurableSingletonClass X := ⟨fun _ => trivial⟩
  have h := independentProductPMF_selected_split e x0 (fun _ => PMF.uniformOfFintype X)
  simp only [independentProductPMF_uniform] at h
  convert h using 1
  congr 1
  congr 1
  exact Subsingleton.elim _ _

theorem uniformZMod_selected_split {A J : Type*}
    [Fintype A] [Fintype J] (N : ℕ) [NeZero N] (e : A ↪ J) :
    PMF.uniformOfFintype (J → ZMod N) =
      (PMF.uniformOfFintype (SelectedCoefficientComplement e → ZMod N)).bind
        (fun tail => (PMF.uniformOfFintype (A → ZMod N)).map
          (selectedCoefficientJoin e (0 : ZMod N) tail)) :=
  uniformOfFintype_selected_split e 0

end Erdos3

end

end OAI
