import OAI.Combinatorics.Progressions.Fourier.TorusCircleActions

namespace OAI

section

namespace Erdos3.CircleFourier

open scoped NNReal

variable {X α : Type*} [PseudoMetricSpace X]

noncomputable def iteratedCircleSmooth (N : ℕ) (A : α → IsometricCircleAction X) :
    List α → (X → ℂ) → X → ℂ
  | [], f => f
  | i :: is, f => (A i).smooth N (iteratedCircleSmooth N A is f)

theorem iteratedCircleSmooth_lipschitz {N : ℕ} (hN : 0 < N)
    (A : α → IsometricCircleAction X) (is : List α) {f : X → ℂ} {L : ℝ≥0}
    (hf : LipschitzWith L f) : LipschitzWith L (iteratedCircleSmooth N A is f) := by
  induction is with
  | nil => exact hf
  | cons i is ih => exact (A i).smooth_lipschitz hN ih

theorem iteratedCircleSmooth_norm_le {N : ℕ} (hN : 0 < N)
    (A : α → IsometricCircleAction X) (is : List α) {f : X → ℂ} {L : ℝ≥0} {B : ℝ}
    (hf : LipschitzWith L f) (hb : ∀ x, ‖f x‖ ≤ B) :
    ∀ x, ‖iteratedCircleSmooth N A is f x‖ ≤ B := by
  induction is with
  | nil => exact hb
  | cons i is ih => exact (A i).smooth_norm_le hN (iteratedCircleSmooth_lipschitz hN A is hf).continuous ih

theorem iteratedCircleSmooth_error {N : ℕ} (hN : 0 < N)
    (A : α → IsometricCircleAction X) (is : List α) {f : X → ℂ} {L : ℝ≥0} {ε : ℝ}
    (hf : LipschitzWith L f)
    (hstep : ∀ i ∈ is, ∀ g : X → ℂ, LipschitzWith L g → ∀ x,
      ‖(A i).smooth N g x - g x‖ ≤ ε) (x : X) :
    ‖iteratedCircleSmooth N A is f x - f x‖ ≤ is.length * ε := by
  induction is with
  | nil => simp [iteratedCircleSmooth]
  | cons i is ih =>
    have ht := ih (fun j hj => hstep j (List.mem_cons_of_mem i hj))
    have hs := hstep i (List.mem_cons_self) (iteratedCircleSmooth N A is f)
      (iteratedCircleSmooth_lipschitz hN A is hf) x
    change ‖(A i).smooth N (iteratedCircleSmooth N A is f) x - f x‖ ≤ _
    calc
      _ ≤ ‖(A i).smooth N (iteratedCircleSmooth N A is f) x - iteratedCircleSmooth N A is f x‖ +
          ‖iteratedCircleSmooth N A is f x - f x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ε + is.length * ε := add_le_add hs ht
      _ = (i :: is).length * ε := by simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring

theorem iteratedCircleSmooth_orbit_error {N : ℕ} (hN : 0 < N)
    (A : α → IsometricCircleAction X) (is : List α) {f : X → ℂ} {L D : ℝ≥0}
    (hf : LipschitzWith L f) {η : ℝ} (hη : 0 < η)
    (horbit : ∀ i ∈ is, ∀ (t : Circle) x, dist ((A i).act t x) x ≤ D * ‖t‖) (x : X) :
    ‖iteratedCircleSmooth N A is f x - f x‖ ≤
      is.length * ((L : ℝ) * D * (η + 1 / (8 * N * η ^ 2))) := by
  apply iteratedCircleSmooth_error hN A is hf
  intro i hi g hg y
  apply (A i).smooth_error hN hg.continuous (mul_nonneg L.coe_nonneg D.coe_nonneg) hη
  intro t z
  rw [← dist_eq_norm]
  calc
    dist (g ((A i).act t z)) (g z) ≤ L * dist ((A i).act t z) z := hg.dist_le_mul _ _
    _ ≤ L * (D * ‖t‖) := mul_le_mul_of_nonneg_left (horbit i hi t z) L.coe_nonneg
    _ = (L : ℝ) * D * ‖t‖ := by ring

end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier

open scoped NNReal

variable {X α : Type*} [PseudoMetricSpace X]

noncomputable def iteratedCircleComponent (N : ℕ) (A : α → IsometricCircleAction X) :
    (is : List α) → (Fin is.length → ℤ) → (X → ℂ) → X → ℂ
  | [], _, f => f
  | i :: is, k, f => (A i).component N (k 0)
      (iteratedCircleComponent N A is (fun j => k j.succ) f)

theorem iteratedCircleComponent_lipschitz {N : ℕ} (hN : 0 < N)
    (A : α → IsometricCircleAction X) (is : List α) (k : Fin is.length → ℤ)
    {f : X → ℂ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    LipschitzWith L (iteratedCircleComponent N A is k f) := by
  induction is with
  | nil => exact hf
  | cons i is ih => exact (A i).component_lipschitz hN (k 0) (ih (fun j => k j.succ))

theorem iteratedCircleComponent_norm_le {N : ℕ} (hN : 0 < N)
    (A : α → IsometricCircleAction X) (is : List α) (k : Fin is.length → ℤ)
    {f : X → ℂ} {B : ℝ≥0} (hf : ∀ x, ‖f x‖ ≤ B) :
    ∀ x, ‖iteratedCircleComponent N A is k f x‖ ≤ B := by
  induction is with
  | nil => exact hf
  | cons i is ih => exact (A i).component_norm_le hN (k 0) (ih (fun j => k j.succ))

theorem iteratedCircleComponent_character (N : ℕ)
    (A : α → IsometricCircleAction X) (is : List α) (k : Fin is.length → ℤ)
    (hcomm : ∀ i ∈ is, ∀ j ∈ is, (A i).Commutes (A j)) (f : X → ℂ)
    (j : Fin is.length) : ∀ (t : Circle) x,
    iteratedCircleComponent N A is k f ((A (is.get j)).act t x) =
      character ((-k j) • t) * iteratedCircleComponent N A is k f x := by
  induction is with
  | nil => exact Fin.elim0 j
  | cons i is ih =>
    have ht : ∀ a ∈ is, ∀ b ∈ is, (A a).Commutes (A b) :=
      fun a ha b hb => hcomm a (List.mem_cons_of_mem i ha) b (List.mem_cons_of_mem i hb)
    refine Fin.cases ?_ (fun q => ?_) j
    · exact (A i).component_character N (k 0) (iteratedCircleComponent N A is (fun q => k q.succ) f)
    · have hm : is.get q ∈ is := List.get_mem is q
      exact (A i).component_preserves_character (A (is.get q))
        (hcomm i (List.mem_cons_self) (is.get q) (List.mem_cons_of_mem i hm))
        N (k 0) (-(k q.succ)) (ih (fun r => k r.succ) ht q)

end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier

open scoped BigOperators NNReal

abbrev FejerChoice (N : ℕ) := ↥(fejerFrequencies N)

theorem sum_fin_tuple_cons {β : Type*} [Fintype β] (n : ℕ) (f : (Fin (n + 1) → β) → ℂ) :
    ∑ k, f k = ∑ b : β, ∑ k : Fin n → β, f (Fin.cons b k) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => β)).sum_comp f]
  exact Fintype.sum_prod_type _

variable {X α : Type*} [PseudoMetricSpace X]

theorem iteratedCircleSmooth_eq_sum {N : ℕ} (hN : 0 < N)
    (A : α → IsometricCircleAction X) (is : List α) {f : X → ℂ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (x : X) :
    iteratedCircleSmooth N A is f x =
      ∑ k : Fin is.length → FejerChoice N,
        iteratedCircleComponent N A is (fun j => (k j : ℤ)) f x := by
  classical
  induction is generalizing x with
  | nil => simp [iteratedCircleSmooth, iteratedCircleComponent]
  | cons i is ih =>
    have ht : iteratedCircleSmooth N A is f = fun y =>
        ∑ k : Fin is.length → FejerChoice N,
          iteratedCircleComponent N A is (fun j => (k j : ℤ)) f y := funext ih
    change (A i).smooth N (iteratedCircleSmooth N A is f) x = _
    rw [ht, (A i).smooth_eq_sum]
    apply Eq.trans ?_ (sum_fin_tuple_cons is.length (fun k : Fin (is.length + 1) → FejerChoice N =>
      iteratedCircleComponent N A (i :: is) (fun j => (k j : ℤ)) f x)).symm
    rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro b _
    rw [(A i).component_sum N (b : ℤ) Finset.univ
      (fun k : Fin is.length → FejerChoice N =>
        iteratedCircleComponent N A is (fun j => (k j : ℤ)) f)
      (fun k _ => (iteratedCircleComponent_lipschitz hN A is (fun j => (k j : ℤ)) hf).continuous) x]
    apply Finset.sum_congr rfl
    intro k _
    rfl

theorem card_fejerChoices (N d : ℕ) :
    Fintype.card (Fin d → FejerChoice N) ≤ N ^ (2 * d) := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
  apply (Nat.pow_le_pow_left (card_fejerFrequencies_le N) d).trans_eq
  rw [pow_mul]

end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier
open MeasureTheory
open scoped NNReal

variable {X α : Type*} [PseudoMetricSpace X]

namespace IsometricCircleAction

theorem component_sub (A : IsometricCircleAction X) (N : ℕ) (h : ℤ)
    {f g : X → ℂ} (hf : Continuous f) (hg : Continuous g) (x : X) :
    A.component N h (fun y => f y - g y) x =
      A.component N h f x - A.component N h g x := by
  let := A.toAddAction
  let := A.toContinuousVAdd
  change (fejerCoefficient N h : ℂ) *
    (∫ t : Circle, character ((-(-h)) • t) * (f (t +ᵥ x) - g (t +ᵥ x)) ∂circleHaar) = _
  simp_rw [mul_sub]
  rw [integral_sub (integrable_circleFourierComponent (-h) hf x)
    (integrable_circleFourierComponent (-h) hg x)]
  exact mul_sub _ _ _

theorem component_norm_sub_le (A : IsometricCircleAction X) {N : ℕ} (hN : 0 < N)
    (h : ℤ) {f g : X → ℂ} (hf : Continuous f) (hg : Continuous g) {ε : ℝ}
    (hfg : ∀ x, ‖f x - g x‖ ≤ ε) (x : X) :
    ‖A.component N h f x - A.component N h g x‖ ≤ ε := by
  rw [← A.component_sub N h hf hg x]
  let := A.toAddAction
  change ‖(fejerCoefficient N h : ℂ) *
    circleFourierComponent (-h) (fun y => f y - g y) x‖ ≤ ε
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (fejerCoefficient_nonneg N h)]
  exact (mul_le_mul (fejerCoefficient_le_one hN h)
    (norm_circleFourierComponent_le (-h) _ hfg x) (norm_nonneg _) zero_le_one).trans_eq
    (one_mul _)

end IsometricCircleAction

theorem iteratedCircleComponent_norm_sub_le {N : ℕ} (hN : 0 < N)
    (A : α → IsometricCircleAction X) (is : List α) (k : Fin is.length → ℤ)
    {f g : X → ℂ} {K H : ℝ≥0} (hf : LipschitzWith K f) (hg : LipschitzWith H g)
    {ε : ℝ} (hfg : ∀ x, ‖f x - g x‖ ≤ ε) (x : X) :
    ‖iteratedCircleComponent N A is k f x - iteratedCircleComponent N A is k g x‖ ≤ ε := by
  induction is generalizing x with
  | nil => exact hfg x
  | cons i is ih =>
    apply (A i).component_norm_sub_le hN (k 0)
      (iteratedCircleComponent_lipschitz hN A is (fun j => k j.succ) hf).continuous
      (iteratedCircleComponent_lipschitz hN A is (fun j => k j.succ) hg).continuous
    intro y
    exact ih (fun j => k j.succ) y

end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier

open scoped BigOperators NNReal

variable {X α : Type*} [PseudoMetricSpace X]

theorem iteratedCircleComponent_equivariant (N : ℕ) (A : α → IsometricCircleAction X)
    (is : List α) (k : Fin is.length → ℤ) (g : X → X) (z : ℂ)
    (hg : ∀ i ∈ is, ∀ t x, (A i).act t (g x) = g ((A i).act t x))
    {f : X → ℂ} (hf : ∀ x, f (g x) = z * f x) :
    ∀ x, iteratedCircleComponent N A is k f (g x) = z * iteratedCircleComponent N A is k f x := by
  induction is with
  | nil => exact hf
  | cons i is ih =>
    exact (A i).component_equivariant N (k 0) g z (hg i List.mem_cons_self)
      (ih (fun j => k j.succ) (fun a ha => hg a (List.mem_cons_of_mem i ha)))

theorem exists_controlled_finite_circle_decomposition
    (A : α → IsometricCircleAction X) (is : List α)
    (hcomm : ∀ i ∈ is, ∀ j ∈ is, (A i).Commutes (A j))
    (f : X → ℂ) (L B D : ℝ≥0) (hf : LipschitzWith L f) (hb : ∀ x, ‖f x‖ ≤ B)
    (horbit : ∀ i ∈ is, ∀ (t : Circle) x, dist ((A i).act t x) x ≤ D * ‖t‖)
    (δ p : ℝ) (hδ : 0 < δ) (hp : 0 ≤ p) (hd : (is.length : ℝ) ≤ p)
    (hLp : (L : ℝ) ≤ Real.exp p) (hDp : (D : ℝ) ≤ Real.exp p) (hδp : δ⁻¹ ≤ Real.exp p) :
    ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ Real.exp ((2 * p + 2) ^ 4) ∧
      (Fintype.card (Fin is.length → FejerChoice N) : ℝ) ≤ Real.exp (2 * p * (2 * p + 2) ^ 4) ∧
      (∀ k : Fin is.length → FejerChoice N,
        (∀ j, (|(k j : ℤ)| : ℝ) ≤ Real.exp ((2 * p + 2) ^ 4)) ∧
        LipschitzWith L (iteratedCircleComponent N A is (fun j => (k j : ℤ)) f) ∧
        (∀ x, ‖iteratedCircleComponent N A is (fun j => (k j : ℤ)) f x‖ ≤ B) ∧
        ∀ (j : Fin is.length) (t : Circle) x,
          iteratedCircleComponent N A is (fun r => (k r : ℤ)) f ((A (is.get j)).act t x) =
            character ((-(k j : ℤ)) • t) *
              iteratedCircleComponent N A is (fun r => (k r : ℤ)) f x) ∧
      ∀ x, ‖(∑ k : Fin is.length → FejerChoice N,
        iteratedCircleComponent N A is (fun j => (k j : ℤ)) f x) - f x‖ ≤ δ := by
  let O : ℝ := (L : ℝ) * D
  have hO : 0 ≤ O := mul_nonneg L.coe_nonneg D.coe_nonneg
  let ε := δ / (is.length + 1)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hOp : O ≤ Real.exp (2 * p) := by
    calc
      O ≤ Real.exp p * Real.exp p := mul_le_mul hLp hDp D.coe_nonneg (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hεp : ε⁻¹ ≤ Real.exp (2 * p) := by
    have hlen : (is.length : ℝ) + 1 ≤ Real.exp p :=
      (by linarith : (is.length : ℝ) + 1 ≤ p + 1).trans (Real.add_one_le_exp p)
    calc
      ε⁻¹ = ((is.length : ℝ) + 1) * δ⁻¹ := by dsimp [ε]; rw [inv_div, div_eq_mul_inv]
      _ ≤ Real.exp p * Real.exp p := mul_le_mul hlen hδp (inv_nonneg.mpr hδ.le) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  obtain ⟨N, hN, hcut, hNb⟩ := exists_fejer_cutoff hO hε
  have hNe : (N : ℝ) ≤ Real.exp ((2 * p + 2) ^ 4) :=
    hNb.trans (fejer_cutoff_bound (by linarith : 0 ≤ 2 * p) hO hε hOp hεp)
  refine ⟨N, hN, hNe, ?_, ?_, ?_⟩
  · apply (Nat.cast_le.mpr (card_fejerChoices N is.length)).trans
    rw [Nat.cast_pow]
    apply (pow_le_pow_left₀ (Nat.cast_nonneg N) hNe _).trans
    rw [← Real.exp_nat_mul, Nat.cast_mul, Nat.cast_ofNat]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hd (by norm_num)) (by positivity))
  · intro k
    refine ⟨?_, iteratedCircleComponent_lipschitz hN A is _ hf,
      iteratedCircleComponent_norm_le hN A is _ hb, ?_⟩
    · intro j
      have hk : (|(k j : ℤ)| : ℝ) < N := by
        exact_mod_cast abs_lt_of_mem_fejerFrequencies (k j).property
      exact hk.le.trans hNe
    · exact fun j => iteratedCircleComponent_character N A is _ hcomm f j
  · intro x
    rw [← iteratedCircleSmooth_eq_sum hN A is hf x]
    have hstep : ∀ i ∈ is, ∀ g : X → ℂ, LipschitzWith L g → ∀ y,
        ‖(A i).smooth N g y - g y‖ ≤ ε := by
      intro i hi g hg y
      have hη : 0 < ε / (2 * (O + 1)) := by positivity
      apply ((A i).smooth_error hN hg.continuous hO hη ?_ y).trans
        (fejer_error_le_of_cutoff hO hε hN hcut)
      intro t z
      rw [← dist_eq_norm]
      exact (hg.dist_le_mul _ _).trans ((mul_le_mul_of_nonneg_left (horbit i hi t z) L.coe_nonneg).trans_eq
        (by dsimp [O]; ring))
    apply (iteratedCircleSmooth_error hN A is hf hstep x).trans
    change (is.length : ℝ) * (δ / (is.length + 1)) ≤ δ
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith

end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier

open scoped BigOperators NNReal

variable {X ι : Type*} [PseudoMetricSpace X] [Fintype ι]

theorem exists_controlled_commuting_circle_decomposition
    (A : ι → IsometricCircleAction X) (hcomm : ∀ i j, (A i).Commutes (A j))
    (f : X → ℂ) (L B D : ℝ≥0) (hf : LipschitzWith L f) (hb : ∀ x, ‖f x‖ ≤ B)
    (horbit : ∀ i (t : Circle) x, dist ((A i).act t x) x ≤ D * ‖t‖)
    (δ p : ℝ) (hδ : 0 < δ) (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hLp : (L : ℝ) ≤ Real.exp p) (hDp : (D : ℝ) ≤ Real.exp p) (hδp : δ⁻¹ ≤ Real.exp p) :
    ∃ (J : Type) (inst : Fintype J), letI := inst
    ∃ (ν : J → ι → ℤ) (v : J → X → ℂ),
      (Fintype.card J : ℝ) ≤ Real.exp (2 * p * (2 * p + 2) ^ 4) ∧
      (∀ j i, (|ν j i| : ℝ) ≤ Real.exp ((2 * p + 2) ^ 4)) ∧
      (∀ j, LipschitzWith L (v j) ∧ (∀ x, ‖v j x‖ ≤ B)) ∧
      (∀ j i (t : Circle) x, v j ((A i).act t x) = character (ν j i • t) * v j x) ∧
      (∀ (g : X → X) (z : ℂ),
        (∀ i t x, (A i).act t (g x) = g ((A i).act t x)) →
        (∀ x, f (g x) = z * f x) → ∀ j x, v j (g x) = z * v j x) ∧
      ∀ x, ‖(∑ j, v j x) - f x‖ ≤ δ := by
  classical
  let is := (Finset.univ : Finset ι).toList
  have hd' : (is.length : ℝ) ≤ p := by simpa [is] using hd
  obtain ⟨N, _, _, hcard, hprops, herr⟩ := exists_controlled_finite_circle_decomposition A is
    (fun i _ j _ => hcomm i j) f L B D hf hb (fun i _ => horbit i)
    δ p hδ hp hd' hLp hDp hδp
  have hcover : ∀ i : ι, ∃ r : Fin is.length, is.get r = i := by
    intro i
    apply List.mem_iff_get.mp
    simp [is]
  choose index hindex using hcover
  let J := Fin is.length → FejerChoice N
  let ν : J → ι → ℤ := fun k i => -(k (index i) : ℤ)
  let v : J → X → ℂ := fun k => iteratedCircleComponent N A is (fun r => (k r : ℤ)) f
  refine ⟨J, inferInstance, ν, v, hcard, ?_, ?_, ?_, ?_, herr⟩
  · intro k i
    simpa only [ν, Int.cast_neg, abs_neg] using (hprops k).1 (index i)
  · intro k
    exact ⟨(hprops k).2.1, (hprops k).2.2.1⟩
  · intro k i t x
    have hi := (hprops k).2.2.2 (index i) t x
    rw [hindex i] at hi
    exact hi
  · intro g z hg hf k x
    exact iteratedCircleComponent_equivariant N A is (fun r => (k r : ℤ))
      g z (fun i _ => hg i) hf x

end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier

open scoped BigOperators NNReal

variable {X ι : Type*} [PseudoMetricSpace X] [Fintype ι]

theorem exists_uniform_controlled_commuting_circle_operators
    (A : ι → IsometricCircleAction X) (hcomm : ∀ i j, (A i).Commutes (A j))
    (D : ℝ≥0)
    (horbit : ∀ i (t : Circle) x, dist ((A i).act t x) x ≤ D * ‖t‖)
    (δ p : ℝ) (hδ : 0 < δ) (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hDp : (D : ℝ) ≤ Real.exp p) (hδp : δ⁻¹ ≤ Real.exp p) :
    ∃ (J : Type) (inst : Fintype J), letI := inst
    ∃ (ν : J → ι → ℤ) (V : J → (X → ℂ) → X → ℂ),
      (Fintype.card J : ℝ) ≤ Real.exp (2 * p * (2 * p + 2) ^ 4) ∧
      (∀ j i, (|ν j i| : ℝ) ≤ Real.exp ((2 * p + 2) ^ 4)) ∧
      (∀ j (f g : X → ℂ) (K H : ℝ≥0), LipschitzWith K f → LipschitzWith H g →
        ∀ ε : ℝ, (∀ x, ‖f x - g x‖ ≤ ε) → ∀ x, ‖V j f x - V j g x‖ ≤ ε) ∧
      ∀ (f : X → ℂ) (L B : ℝ≥0), LipschitzWith L f → (∀ x, ‖f x‖ ≤ B) →
        (L : ℝ) ≤ Real.exp p →
          (∀ j, LipschitzWith L (V j f) ∧ (∀ x, ‖V j f x‖ ≤ B)) ∧
          (∀ j i (t : Circle) x, V j f ((A i).act t x) = character (ν j i • t) * V j f x) ∧
          (∀ (g : X → X) (z : ℂ),
            (∀ i t x, (A i).act t (g x) = g ((A i).act t x)) →
            (∀ x, f (g x) = z * f x) → ∀ j x, V j f (g x) = z * V j f x) ∧
          ∀ x, ‖(∑ j, V j f x) - f x‖ ≤ δ := by
  classical
  let is := (Finset.univ : Finset ι).toList
  have hd' : (is.length : ℝ) ≤ p := by simpa [is] using hd
  let O : ℝ := Real.exp p * D
  have hO : 0 ≤ O := mul_nonneg (Real.exp_nonneg _) D.coe_nonneg
  let ε := δ / (is.length + 1)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hOp : O ≤ Real.exp (2 * p) := by
    calc
      O ≤ Real.exp p * Real.exp p := mul_le_mul_of_nonneg_left hDp (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hεp : ε⁻¹ ≤ Real.exp (2 * p) := by
    have hlen : (is.length : ℝ) + 1 ≤ Real.exp p :=
      (by linarith : (is.length : ℝ) + 1 ≤ p + 1).trans (Real.add_one_le_exp p)
    calc
      ε⁻¹ = ((is.length : ℝ) + 1) * δ⁻¹ := by dsimp [ε]; rw [inv_div, div_eq_mul_inv]
      _ ≤ Real.exp p * Real.exp p :=
        mul_le_mul hlen hδp (inv_nonneg.mpr hδ.le) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  obtain ⟨N, hN, hcut, hNb⟩ := exists_fejer_cutoff hO hε
  have hNe : (N : ℝ) ≤ Real.exp ((2 * p + 2) ^ 4) :=
    hNb.trans (fejer_cutoff_bound (by linarith : 0 ≤ 2 * p) hO hε hOp hεp)
  have hcard : (Fintype.card (Fin is.length → FejerChoice N) : ℝ) ≤
      Real.exp (2 * p * (2 * p + 2) ^ 4) := by
    apply (Nat.cast_le.mpr (card_fejerChoices N is.length)).trans
    rw [Nat.cast_pow]
    apply (pow_le_pow_left₀ (Nat.cast_nonneg N) hNe _).trans
    rw [← Real.exp_nat_mul, Nat.cast_mul, Nat.cast_ofNat]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hd' (by norm_num)) (by positivity))
  have hcover : ∀ i : ι, ∃ r : Fin is.length, is.get r = i := by
    intro i
    apply List.mem_iff_get.mp
    simp [is]
  choose index hindex using hcover
  let J := Fin is.length → FejerChoice N
  let ν : J → ι → ℤ := fun k i => -(k (index i) : ℤ)
  let V : J → (X → ℂ) → X → ℂ := fun k f =>
    iteratedCircleComponent N A is (fun r => (k r : ℤ)) f
  refine ⟨J, inferInstance, ν, V, hcard, ?_, ?_, ?_⟩
  · intro k i
    have hk : (|(k (index i) : ℤ)| : ℝ) < N := by
      exact_mod_cast abs_lt_of_mem_fejerFrequencies (k (index i)).property
    simpa only [ν, Int.cast_neg, abs_neg] using hk.le.trans hNe
  · intro k f g K H hf hg ε hfg x
    exact iteratedCircleComponent_norm_sub_le hN A is (fun r => (k r : ℤ)) hf hg hfg x
  · intro f L B hf hb hLp
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro k
      exact ⟨iteratedCircleComponent_lipschitz hN A is _ hf,
        iteratedCircleComponent_norm_le hN A is _ hb⟩
    · intro k i t x
      have hi := iteratedCircleComponent_character N A is (fun r => (k r : ℤ))
        (fun a _ b _ => hcomm a b) f (index i) t x
      rw [hindex i] at hi
      exact hi
    · intro g z hg hfz k x
      exact iteratedCircleComponent_equivariant N A is (fun r => (k r : ℤ))
        g z (fun i _ => hg i) hfz x
    · intro x
      change ‖(∑ k : Fin is.length → FejerChoice N,
        iteratedCircleComponent N A is (fun r => (k r : ℤ)) f x) - f x‖ ≤ δ
      rw [← iteratedCircleSmooth_eq_sum hN A is hf x]
      have hstep : ∀ i ∈ is, ∀ g : X → ℂ, LipschitzWith L g → ∀ y,
          ‖(A i).smooth N g y - g y‖ ≤ ε := by
        intro i _ g hg y
        have hη : 0 < ε / (2 * (O + 1)) := by positivity
        apply ((A i).smooth_error hN hg.continuous hO hη ?_ y).trans
          (fejer_error_le_of_cutoff hO hε hN hcut)
        intro t z
        rw [← dist_eq_norm]
        calc
          dist (g ((A i).act t z)) (g z) ≤ L * dist ((A i).act t z) z := hg.dist_le_mul _ _
          _ ≤ L * (D * ‖t‖) := mul_le_mul_of_nonneg_left (horbit i t z) L.coe_nonneg
          _ ≤ Real.exp p * (D * ‖t‖) :=
            mul_le_mul_of_nonneg_right hLp (mul_nonneg D.coe_nonneg (norm_nonneg _))
          _ = O * ‖t‖ := by dsimp [O]; ring
      apply (iteratedCircleSmooth_error hN A is hf hstep x).trans
      change (is.length : ℝ) * (δ / (is.length + 1)) ≤ δ
      rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
      nlinarith

end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier

open scoped BigOperators NNReal

variable {X ι : Type*} [PseudoMetricSpace X] [Fintype ι]

theorem exists_uniform_controlled_commuting_circle_decomposition
    (A : ι → IsometricCircleAction X) (hcomm : ∀ i j, (A i).Commutes (A j))
    (D : ℝ≥0)
    (horbit : ∀ i (t : Circle) x, dist ((A i).act t x) x ≤ D * ‖t‖)
    (δ p : ℝ) (hδ : 0 < δ) (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hDp : (D : ℝ) ≤ Real.exp p) (hδp : δ⁻¹ ≤ Real.exp p) :
    ∃ (J : Type) (inst : Fintype J), letI := inst
    ∃ ν : J → ι → ℤ,
      (Fintype.card J : ℝ) ≤ Real.exp (2 * p * (2 * p + 2) ^ 4) ∧
      (∀ j i, (|ν j i| : ℝ) ≤ Real.exp ((2 * p + 2) ^ 4)) ∧
      ∀ (f : X → ℂ) (L B : ℝ≥0), LipschitzWith L f → (∀ x, ‖f x‖ ≤ B) →
        (L : ℝ) ≤ Real.exp p → ∃ v : J → X → ℂ,
          (∀ j, LipschitzWith L (v j) ∧ (∀ x, ‖v j x‖ ≤ B)) ∧
          (∀ j i (t : Circle) x, v j ((A i).act t x) = character (ν j i • t) * v j x) ∧
          (∀ (g : X → X) (z : ℂ),
            (∀ i t x, (A i).act t (g x) = g ((A i).act t x)) →
            (∀ x, f (g x) = z * f x) → ∀ j x, v j (g x) = z * v j x) ∧
          ∀ x, ‖(∑ j, v j x) - f x‖ ≤ δ := by
  classical
  let is := (Finset.univ : Finset ι).toList
  have hd' : (is.length : ℝ) ≤ p := by simpa [is] using hd
  let O : ℝ := Real.exp p * D
  have hO : 0 ≤ O := mul_nonneg (Real.exp_nonneg _) D.coe_nonneg
  let ε := δ / (is.length + 1)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hOp : O ≤ Real.exp (2 * p) := by
    calc
      O ≤ Real.exp p * Real.exp p := mul_le_mul_of_nonneg_left hDp (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hεp : ε⁻¹ ≤ Real.exp (2 * p) := by
    have hlen : (is.length : ℝ) + 1 ≤ Real.exp p :=
      (by linarith : (is.length : ℝ) + 1 ≤ p + 1).trans (Real.add_one_le_exp p)
    calc
      ε⁻¹ = ((is.length : ℝ) + 1) * δ⁻¹ := by dsimp [ε]; rw [inv_div, div_eq_mul_inv]
      _ ≤ Real.exp p * Real.exp p :=
        mul_le_mul hlen hδp (inv_nonneg.mpr hδ.le) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  obtain ⟨N, hN, hcut, hNb⟩ := exists_fejer_cutoff hO hε
  have hNe : (N : ℝ) ≤ Real.exp ((2 * p + 2) ^ 4) :=
    hNb.trans (fejer_cutoff_bound (by linarith : 0 ≤ 2 * p) hO hε hOp hεp)
  have hcard : (Fintype.card (Fin is.length → FejerChoice N) : ℝ) ≤
      Real.exp (2 * p * (2 * p + 2) ^ 4) := by
    apply (Nat.cast_le.mpr (card_fejerChoices N is.length)).trans
    rw [Nat.cast_pow]
    apply (pow_le_pow_left₀ (Nat.cast_nonneg N) hNe _).trans
    rw [← Real.exp_nat_mul, Nat.cast_mul, Nat.cast_ofNat]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hd' (by norm_num)) (by positivity))
  have hcover : ∀ i : ι, ∃ r : Fin is.length, is.get r = i := by
    intro i
    apply List.mem_iff_get.mp
    simp [is]
  choose index hindex using hcover
  let J := Fin is.length → FejerChoice N
  let ν : J → ι → ℤ := fun k i => -(k (index i) : ℤ)
  refine ⟨J, inferInstance, ν, hcard, ?_, ?_⟩
  · intro k i
    have hk : (|(k (index i) : ℤ)| : ℝ) < N := by
      exact_mod_cast abs_lt_of_mem_fejerFrequencies (k (index i)).property
    simpa only [ν, Int.cast_neg, abs_neg] using hk.le.trans hNe
  · intro f L B hf hb hLp
    let v : J → X → ℂ := fun k => iteratedCircleComponent N A is (fun r => (k r : ℤ)) f
    refine ⟨v, ?_, ?_, ?_, ?_⟩
    · intro k
      exact ⟨iteratedCircleComponent_lipschitz hN A is _ hf,
        iteratedCircleComponent_norm_le hN A is _ hb⟩
    · intro k i t x
      have hi := iteratedCircleComponent_character N A is (fun r => (k r : ℤ))
        (fun a _ b _ => hcomm a b) f (index i) t x
      rw [hindex i] at hi
      exact hi
    · intro g z hg hfz k x
      exact iteratedCircleComponent_equivariant N A is (fun r => (k r : ℤ))
        g z (fun i _ => hg i) hfz x
    · intro x
      change ‖(∑ k : Fin is.length → FejerChoice N,
        iteratedCircleComponent N A is (fun r => (k r : ℤ)) f x) - f x‖ ≤ δ
      rw [← iteratedCircleSmooth_eq_sum hN A is hf x]
      have hstep : ∀ i ∈ is, ∀ g : X → ℂ, LipschitzWith L g → ∀ y,
          ‖(A i).smooth N g y - g y‖ ≤ ε := by
        intro i _ g hg y
        have hη : 0 < ε / (2 * (O + 1)) := by positivity
        apply ((A i).smooth_error hN hg.continuous hO hη ?_ y).trans
          (fejer_error_le_of_cutoff hO hε hN hcut)
        intro t z
        rw [← dist_eq_norm]
        calc
          dist (g ((A i).act t z)) (g z) ≤ L * dist ((A i).act t z) z := hg.dist_le_mul _ _
          _ ≤ L * (D * ‖t‖) := mul_le_mul_of_nonneg_left (horbit i t z) L.coe_nonneg
          _ ≤ Real.exp p * (D * ‖t‖) :=
            mul_le_mul_of_nonneg_right hLp (mul_nonneg D.coe_nonneg (norm_nonneg _))
          _ = O * ‖t‖ := by dsimp [O]; ring
      apply (iteratedCircleSmooth_error hN A is hf hstep x).trans
      change (is.length : ℝ) * (δ / (is.length + 1)) ≤ δ
      rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
      nlinarith

end Erdos3.CircleFourier

end

end OAI
