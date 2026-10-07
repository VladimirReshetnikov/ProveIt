import OAI.Combinatorics.Progressions.Geometry.CoordinateFiberPatch

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem finite_mean_square_as_pair {T : Type*} [Fintype T]
    (q : FiniteProbabilityWeights T) (f : T → ℝ) :
    (q.mean f) ^ 2 = (q.prod q).mean (fun t => f t.1 * f t.2) := by
  rw [FiniteProbabilityWeights.mean_prod]
  simp only [q.mean_const_mul, q.mean_mul_const, pow_two]

theorem sampled_second_moment_identity {Ω T : Type*} [Fintype Ω] [Fintype T]
    (p : FiniteProbabilityWeights Ω) (q : FiniteProbabilityWeights T) (e : Ω → T → ℝ) :
    p.mean (fun x => (q.mean (e x)) ^ 2) =
      (q.prod q).mean (fun t => p.mean (fun x => e x t.1 * e x t.2)) := by
  simp_rw [finite_mean_square_as_pair q]
  exact p.mean_comm (q.prod q) (fun x t => e x t.1 * e x t.2)

theorem finite_mean_bad_event_bound {X : Type*} [Fintype X]
    (p : FiniteProbabilityWeights X) (Bad : X → Prop) (f : X → ℝ) {C epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (hbad : ∀ x, Bad x → f x ≤ C)
    (hgood : ∀ x, ¬ Bad x → f x ≤ epsilon) :
    p.mean f ≤ C * p.eventProbability Bad + epsilon := by
  have hpoint (x : X) : f x ≤ C * (if Bad x then (1 : ℝ) else 0) + epsilon := by
    by_cases hx : Bad x
    · simp only [hx, ite_true, mul_one]
      linarith [hbad x hx]
    · simpa only [hx, ite_false, mul_zero, zero_add] using hgood x hx
  apply (p.mean_mono hpoint).trans_eq
  rw [p.mean_add, p.mean_const_mul, p.mean_const]
  rfl

theorem sampled_second_moment_bad_pairs {Ω T : Type*} [Fintype Ω] [Fintype T]
    (p : FiniteProbabilityWeights Ω) (q : FiniteProbabilityWeights T) (e : Ω → T → ℝ)
    (Bad : T × T → Prop) {C epsilon beta : ℝ} (hC : 0 ≤ C) (hepsilon : 0 ≤ epsilon)
    (hmass : (q.prod q).eventProbability Bad ≤ beta)
    (hbad : ∀ t, Bad t → |p.mean (fun x => e x t.1 * e x t.2)| ≤ C)
    (hgood : ∀ t, ¬ Bad t → |p.mean (fun x => e x t.1 * e x t.2)| ≤ epsilon) :
    p.mean (fun x => (q.mean (e x)) ^ 2) ≤ C * beta + epsilon := by
  rw [sampled_second_moment_identity]
  have h := finite_mean_bad_event_bound (q.prod q) Bad
    (fun t => p.mean (fun x => e x t.1 * e x t.2)) hepsilon
    (fun t ht => (le_abs_self _).trans (hbad t ht))
    (fun t ht => (le_abs_self _).trans (hgood t ht))
  have hm := mul_le_mul_of_nonneg_left hmass hC
  linarith

theorem sampled_weighted_error_of_bad_pairs {Ω T : Type*} [Fintype Ω] [Fintype T]
    (p : FiniteProbabilityWeights Ω) (q : FiniteProbabilityWeights T) (e : Ω → T → ℝ)
    (Bad : T × T → Prop) {C epsilon beta : ℝ} (hC : 0 ≤ C) (hepsilon : 0 ≤ epsilon)
    (hmass : (q.prod q).eventProbability Bad ≤ beta)
    (hbad : ∀ t, Bad t → |p.mean (fun x => e x t.1 * e x t.2)| ≤ C)
    (hgood : ∀ t, ¬ Bad t → |p.mean (fun x => e x t.1 * e x t.2)| ≤ epsilon)
    (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x ∧ w x ≤ 1) :
    |p.mean (fun x => w x * q.mean (e x))| ≤ Real.sqrt (C * beta + epsilon) := by
  have he := sampled_second_moment_bad_pairs p q e Bad hC hepsilon hmass hbad hgood
  have hw2 : p.mean (fun x => w x ^ 2) ≤ 1 := by
    apply (p.mean_mono (g := fun _ => 1) ?_).trans_eq (p.mean_const 1)
    intro x
    have h := hw x
    nlinarith
  have he0 := p.mean_nonneg (fun x => sq_nonneg (q.mean (e x)))
  have hc := p.mean_mul_sq_le w (fun x => q.mean (e x))
  have hm := mul_le_mul_of_nonneg_right hw2 he0
  apply Real.le_sqrt_of_sq_le
  rw [sq_abs]
  nlinarith only [hc, hm, he]

theorem sampled_pair_correlation_cap {Ω T : Type*} [Fintype Ω]
    (p : FiniteProbabilityWeights Ω) (e : Ω → T → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (henergy : ∀ t, p.mean (fun x => e x t ^ 2) ≤ C) (t u : T) :
    |p.mean (fun x => e x t * e x u)| ≤ C := by
  apply abs_le_of_sq_le_sq _ hC
  calc
    _ ≤ p.mean (fun x => e x t ^ 2) * p.mean (fun x => e x u ^ 2) :=
      p.mean_mul_sq_le (fun x => e x t) (fun x => e x u)
    _ ≤ C * C := mul_le_mul (henergy t) (henergy u) (p.mean_nonneg (fun x => sq_nonneg _)) hC
    _ = C ^ 2 := by ring

theorem sampled_weighted_error_of_energy {Ω T : Type*} [Fintype Ω] [Fintype T]
    (p : FiniteProbabilityWeights Ω) (q : FiniteProbabilityWeights T) (e : Ω → T → ℝ)
    (Bad : T × T → Prop) {C epsilon beta : ℝ} (hC : 0 ≤ C) (hepsilon : 0 ≤ epsilon)
    (henergy : ∀ t, p.mean (fun x => e x t ^ 2) ≤ C)
    (hmass : (q.prod q).eventProbability Bad ≤ beta)
    (hgood : ∀ t, ¬ Bad t → |p.mean (fun x => e x t.1 * e x t.2)| ≤ epsilon)
    (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x ∧ w x ≤ 1) :
    |p.mean (fun x => w x * q.mean (e x))| ≤ Real.sqrt (C * beta + epsilon) :=
  sampled_weighted_error_of_bad_pairs p q e Bad hC hepsilon hmass
    (fun t _ => sampled_pair_correlation_cap p e hC henergy t.1 t.2) hgood w hw

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem sampled_error_of_dominated_source {Ω P : Type*} [Fintype Ω] [Fintype P]
    (p q : FiniteProbabilityWeights Ω) (r : FiniteProbabilityWeights P)
    (e : Ω → P → ℝ) (Bad : P × P → Prop) {D C epsilon beta : ℝ}
    (hD : 0 < D) (hdom : ∀ x, q.weight x ≤ D * p.weight x)
    (hC : 0 ≤ C) (hepsilon : 0 ≤ epsilon)
    (henergy : ∀ t, p.mean (fun x => e x t ^ 2) ≤ C)
    (hmass : (r.prod r).eventProbability Bad ≤ beta)
    (hgood : ∀ t, ¬ Bad t → |p.mean (fun x => e x t.1 * e x t.2)| ≤ epsilon) :
    |q.mean (fun x => r.mean (e x))| ≤ D * Real.sqrt (C * beta + epsilon) := by
  obtain ⟨w, hw, he⟩ := p.exists_bounded_change_of_measure q hD hdom
  rw [he (fun x => r.mean (e x)), abs_mul, abs_of_pos hD]
  exact mul_le_mul_of_nonneg_left
    (sampled_weighted_error_of_energy p r e Bad hC hepsilon henergy hmass hgood w hw) hD.le

theorem smooth_window_sampled_error {K I P : Type*}
    [Fintype K] [Fintype I] [Fintype P]
    (a S : Option K × I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (hscale : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S i)
    (W : Finset (Option K × I → ℤ))
    (hW : ∀ z ∈ W, ∀ i, |(z i : ℝ) - a i| ≤ S i / 2)
    (q : FiniteProbabilityWeights P) (t : P → K → ℤ)
    (T : Finset (I → ℤ)) (e : (I → ℤ) → ℝ) (he : ∀ y ∉ T, e y = 0)
    {E epsilon beta : ℝ} (hE : 0 ≤ E) (hepsilon : 0 ≤ epsilon)
    (henergy : (∑ y ∈ T, e y ^ 2) ≤ E * T.card)
    (Bad : P × P → Prop) (hmass : (q.prod q).eventProbability Bad ≤ beta)
    (hgood : ∀ u, ¬ Bad u →
      |(smoothSourceFiniteWeights a S hS hZ).mean (fun z =>
        e (smoothAffineSample (t u.1) z.val) * e (smoothAffineSample (t u.2) z.val))| ≤ epsilon) :
    |𝔼 z ∈ W, q.mean (fun u => e (smoothAffineSample (t u) z))| ≤
      ((3 : ℝ) ^ Fintype.card (Option K × I) * (∏ i, S i) / W.card) *
        Real.sqrt (((∏ i, 2 / S (none, i)) * (E * T.card)) * beta + epsilon) := by
  obtain ⟨w, hw, hchange⟩ := smooth_window_change_of_measure a S hS hZ hscale W hW
  have hC : 0 ≤ (∏ i, 2 / S (none, i)) * (E * T.card) := by
    apply mul_nonneg
    · exact Finset.prod_nonneg (fun i _ => div_nonneg (by norm_num) (hS (none, i)).le)
    · exact mul_nonneg hE (Nat.cast_nonneg _)
  have hsample := sampled_weighted_error_of_energy (smoothSourceFiniteWeights a S hS hZ) q
    (fun z u => e (smoothAffineSample (t u) z.val)) Bad hC hepsilon
    (fun u => smoothSourceFiniteWeights_energy a S hS hZ (fun i => hscale (none, i))
      (t u) T e he henergy) hmass hgood w hw
  have hfactor : 0 ≤ (3 : ℝ) ^ Fintype.card (Option K × I) * (∏ i, S i) / W.card := by
    exact div_nonneg (mul_nonneg (by positivity) (Finset.prod_nonneg (fun i _ => (hS i).le)))
      (Nat.cast_nonneg _)
  rw [hchange (fun z => q.mean (fun u => e (smoothAffineSample (t u) z))), abs_mul,
    abs_of_nonneg hfactor]
  exact mul_le_mul_of_nonneg_left hsample hfactor

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem sampled_weighted_error_of_dominated_source {Ω P : Type*} [Fintype Ω] [Fintype P]
    (p q : FiniteProbabilityWeights Ω) (r : FiniteProbabilityWeights P)
    (e : Ω → P → ℝ) (Bad : P × P → Prop) {D C epsilon beta : ℝ}
    (hD : 0 < D) (hdom : ∀ x, q.weight x ≤ D * p.weight x)
    (hC : 0 ≤ C) (hepsilon : 0 ≤ epsilon)
    (henergy : ∀ t, p.mean (fun x => e x t ^ 2) ≤ C)
    (hmass : (r.prod r).eventProbability Bad ≤ beta)
    (hgood : ∀ t, ¬ Bad t → |p.mean (fun x => e x t.1 * e x t.2)| ≤ epsilon)
    (v : Ω → ℝ) (hv : ∀ x, 0 ≤ v x ∧ v x ≤ 1) :
    |q.mean (fun x => v x * r.mean (e x))| ≤ D * Real.sqrt (C * beta + epsilon) := by
  obtain ⟨w, hw, he⟩ := p.exists_bounded_change_of_measure q hD hdom
  have hprod (x : Ω) : 0 ≤ w x * v x ∧ w x * v x ≤ 1 :=
    ⟨mul_nonneg (hw x).1 (hv x).1, (mul_le_mul (hw x).2 (hv x).2 (hv x).1 zero_le_one).trans_eq (one_mul 1)⟩
  have h := sampled_weighted_error_of_energy p r e Bad hC hepsilon henergy hmass hgood
    (fun x => w x * v x) hprod
  rw [he (fun x => v x * r.mean (e x)), abs_mul, abs_of_pos hD]
  exact mul_le_mul_of_nonneg_left (by simpa only [mul_assoc] using h) hD.le

theorem smooth_window_weighted_sampled_error {K I P : Type*}
    [Fintype K] [Fintype I] [Fintype P]
    (a S : Option K × I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (hscale : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S i)
    (W : Finset (Option K × I → ℤ))
    (hW : ∀ z ∈ W, ∀ i, |(z i : ℝ) - a i| ≤ S i / 2)
    (q : FiniteProbabilityWeights P) (t : P → K → ℤ)
    (T : Finset (I → ℤ)) (e : (I → ℤ) → ℝ) (he : ∀ y ∉ T, e y = 0)
    {E epsilon beta : ℝ} (hE : 0 ≤ E) (hepsilon : 0 ≤ epsilon)
    (henergy : (∑ y ∈ T, e y ^ 2) ≤ E * T.card)
    (Bad : P × P → Prop) (hmass : (q.prod q).eventProbability Bad ≤ beta)
    (hgood : ∀ u, ¬ Bad u → |(smoothSourceFiniteWeights a S hS hZ).mean
      (fun z => e (smoothAffineSample (t u.1) z.val) * e (smoothAffineSample (t u.2) z.val))| ≤ epsilon)
    (v : (Option K × I → ℤ) → ℝ) (hv : ∀ z, 0 ≤ v z ∧ v z ≤ 1) :
    |𝔼 z ∈ W, v z * q.mean (fun u => e (smoothAffineSample (t u) z))| ≤
      ((3 : ℝ) ^ Fintype.card (Option K × I) * (∏ i, S i) / W.card) *
        Real.sqrt (((∏ i, 2 / S (none, i)) * (E * T.card)) * beta + epsilon) := by
  obtain ⟨w, hw, hchange⟩ := smooth_window_change_of_measure a S hS hZ hscale W hW
  have hC : 0 ≤ (∏ i, 2 / S (none, i)) * (E * T.card) := by
    exact mul_nonneg (Finset.prod_nonneg (fun i _ => div_nonneg (by norm_num) (hS (none, i)).le))
      (mul_nonneg hE (Nat.cast_nonneg _))
  have hprod (z : rectangularWeightIndices a S 1) : 0 ≤ w z * v z.val ∧ w z * v z.val ≤ 1 :=
    ⟨mul_nonneg (hw z).1 (hv z.val).1,
      (mul_le_mul (hw z).2 (hv z.val).2 (hv z.val).1 zero_le_one).trans_eq (one_mul 1)⟩
  have hsample := sampled_weighted_error_of_energy (smoothSourceFiniteWeights a S hS hZ) q
    (fun z u => e (smoothAffineSample (t u) z.val)) Bad hC hepsilon
    (fun u => smoothSourceFiniteWeights_energy a S hS hZ (fun i => hscale (none, i)) (t u) T e he henergy)
    hmass hgood (fun z => w z * v z.val) hprod
  have hfactor : 0 ≤ (3 : ℝ) ^ Fintype.card (Option K × I) * (∏ i, S i) / W.card := by
    exact div_nonneg (mul_nonneg (by positivity) (Finset.prod_nonneg (fun i _ => (hS i).le))) (Nat.cast_nonneg _)
  rw [hchange (fun z => v z * q.mean (fun u => e (smoothAffineSample (t u) z))), abs_mul, abs_of_nonneg hfactor]
  exact mul_le_mul_of_nonneg_left (by simpa only [mul_assoc] using hsample) hfactor

end Erdos3

end

end OAI
