import OAI.Combinatorics.Progressions.Linear.UniformPhysicalFrameConstruction

namespace OAI

section

namespace Erdos3

theorem exists_physical_record_inflation (Ke C Kf : ℕ) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ x : ℝ, 0 ≤ x →
      x + (x + 2) ^ C ≤ (x + 2) ^ A ∧
      x + (x + 2) ^ Kf + 8 ≤ (x + 2) ^ A ∧
      ∀ q : ℝ, 1 ≤ q → q ≤ (x + 2) ^ Ke → ∀ B : ℕ, B ≤ C →
        (q + B) ^ B ≤ (x + 2) ^ A := by
  let E : Polynomial ℕ := ((Polynomial.X + 2) ^ Ke + Polynomial.C C) ^ C
  let P : Polynomial ℕ := E + Polynomial.X + (Polynomial.X + 2) ^ C +
    Polynomial.X + (Polynomial.X + 2) ^ Kf + 8
  obtain ⟨A, hA, hbudget⟩ := exists_natPolynomial_fixed_power_budget P
  refine ⟨A, by omega, ?_⟩
  intro x hx
  have hsum : ((x + 2) ^ Ke + C) ^ C + x + (x + 2) ^ C + x + (x + 2) ^ Kf + 8 ≤
      (x + 2) ^ A := by simpa [P, E, Polynomial.eval₂_pow] using hbudget x hx
  have hE : 0 ≤ ((x + 2) ^ Ke + C) ^ C := by positivity
  have hC : 0 ≤ (x + 2) ^ C := by positivity
  have hF : 0 ≤ (x + 2) ^ Kf := by positivity
  refine ⟨by linarith, by linarith, ?_⟩
  intro q hq1 hq B hB
  have hq0 : 0 ≤ q := by linarith
  have hBC : (B : ℝ) ≤ C := by exact_mod_cast hB
  have hbase : q + B ≤ (x + 2) ^ Ke + C := add_le_add hq hBC
  have hlarge : 1 ≤ (x + 2) ^ Ke + C := by have := Nat.cast_nonneg (α := ℝ) C; linarith
  calc
    (q + B) ^ B ≤ ((x + 2) ^ Ke + C) ^ B := pow_le_pow_left₀ (by positivity) hbase B
    _ ≤ ((x + 2) ^ Ke + C) ^ C := pow_le_pow_right₀ hlarge hB
    _ ≤ (x + 2) ^ A := by linarith

theorem inherited_relative_width {W oldWidth newWidth p x D R δ : ℝ}
    (hp : p ≤ x) (hδ : 0 < δ) (hδbound : δ⁻¹ ≤ Real.exp D)
    (hbudget : x + D + 8 ≤ R) (hnew0 : 0 ≤ newWidth)
    (hold : 2 * Real.exp (-p) * W ≤ oldWidth)
    (hnew : δ * oldWidth / 8 ≤ newWidth) :
    2 * Real.exp (-R) * W ≤ newWidth := by
  have hexp : Real.exp p * Real.exp (-p) = 1 := by rw [← Real.exp_add]; simp
  have hold' : 2 * W ≤ Real.exp p * oldWidth := by
    calc
      2 * W = 2 * (Real.exp p * Real.exp (-p)) * W := by rw [hexp]; ring
      _ = Real.exp p * (2 * Real.exp (-p) * W) := by ring
      _ ≤ Real.exp p * oldWidth := mul_le_mul_of_nonneg_left hold (Real.exp_nonneg _)
  have hnew' : oldWidth ≤ 8 * newWidth / δ :=
    (le_div_iff₀ hδ).mpr (by linarith)
  have h8 : (8 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp (8 : ℝ)]
  have hcoeff : 8 * Real.exp p * δ⁻¹ ≤ Real.exp R := by
    calc
      8 * Real.exp p * δ⁻¹ ≤ (Real.exp 8 * Real.exp x) * Real.exp D :=
        mul_le_mul (mul_le_mul h8 (Real.exp_le_exp.mpr hp) (Real.exp_nonneg _) (Real.exp_nonneg _))
          hδbound (inv_nonneg.mpr hδ.le) (by positivity)
      _ = Real.exp (x + D + 8) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp R := Real.exp_le_exp.mpr hbudget
  have htotal : 2 * W ≤ Real.exp R * newWidth := by
    calc
      2 * W ≤ Real.exp p * oldWidth := hold'
      _ ≤ Real.exp p * (8 * newWidth / δ) := mul_le_mul_of_nonneg_left hnew' (Real.exp_nonneg _)
      _ = (8 * Real.exp p * δ⁻¹) * newWidth := by ring
      _ ≤ Real.exp R * newWidth := mul_le_mul_of_nonneg_right hcoeff hnew0
  calc
    2 * Real.exp (-R) * W = Real.exp (-R) * (2 * W) := by ring
    _ ≤ Real.exp (-R) * (Real.exp R * newWidth) := mul_le_mul_of_nonneg_left htotal (Real.exp_nonneg _)
    _ = newWidth := by rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

end Erdos3

end

section

namespace Erdos3

universe u v

namespace PhysicalEpochComparison

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {s bound m a J : ℕ} {gap : ℝ}
  {base : PhysicalEpochSource.{u, v} σ s bound}

def Controlled (c : PhysicalEpochComparison base m a J gap) : Prop :=
  (a : ℝ) ≤ Real.exp base.recordBudget ∧
  ∀ i, 2 * Real.exp (-base.recordBudget) * (base.sides i : ℝ) ≤ (c.sides i : ℝ)

end PhysicalEpochComparison

theorem PhysicalEpochFrame.child_comparison_controlled
    {σ : Type u} [Fintype σ] [DecidableEq σ] {s bound m a J C Kf : ℕ} {gap δ : ℝ}
    {base : PhysicalEpochSource.{u, v} σ (s + 1) bound}
    (frame : PhysicalEpochFrame base) (c : PhysicalEpochComparison base m a J gap)
    (next : PhysicalEpochComparison frame.child m (a * frame.period) J (gap / 4))
    (hc : c.Controlled) (hC : frame.freezePower ≤ C)
    (hperiodBudget : frame.child.incomingBudget + (frame.child.incomingBudget + 2) ^ C ≤ frame.child.recordBudget)
    (hwidthBudget : frame.child.incomingBudget + (frame.child.incomingBudget + 2) ^ Kf + 8 ≤ frame.child.recordBudget)
    (hδ : 0 < δ) (hδbound : δ⁻¹ ≤ Real.exp ((frame.work + 2) ^ Kf))
    (hside : ∀ i, δ * (c.sides i : ℝ) / 8 ≤ (next.sides i : ℝ)) :
    next.Controlled := by
  have hx := frame.child.incoming_nonneg
  have hw : 0 ≤ frame.work := by linarith [base.incoming_nonneg, frame.incoming_le_work]
  have hp : base.recordBudget ≤ frame.child.incomingBudget := by
    linarith [frame.record_le_work, frame.work_le_child]
  have hwx : frame.work + 2 ≤ frame.child.incomingBudget + 2 := by linarith [frame.work_le_child]
  have hpow : (frame.work + 2) ^ frame.freezePower ≤ (frame.child.incomingBudget + 2) ^ C :=
    (pow_le_pow_left₀ (by linarith) hwx _).trans
      (pow_le_pow_right₀ (by linarith) hC)
  have hperiod : (frame.period : ℝ) ≤ Real.exp ((frame.child.incomingBudget + 2) ^ C) :=
    frame.period_le.trans (Real.exp_le_exp.mpr hpow)
  have hδchild : δ⁻¹ ≤ Real.exp ((frame.child.incomingBudget + 2) ^ Kf) :=
    hδbound.trans (Real.exp_le_exp.mpr
      (pow_le_pow_left₀ (by linarith) hwx Kf))
  refine ⟨?_, ?_⟩
  · calc
      ((a * frame.period : ℕ) : ℝ) = (a : ℝ) * (frame.period : ℝ) := by norm_cast
      _ ≤ Real.exp frame.child.incomingBudget * Real.exp ((frame.child.incomingBudget + 2) ^ C) :=
        mul_le_mul (hc.1.trans (Real.exp_le_exp.mpr hp)) hperiod (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (frame.child.incomingBudget + (frame.child.incomingBudget + 2) ^ C) := (Real.exp_add _ _).symm
      _ ≤ Real.exp frame.child.recordBudget := Real.exp_le_exp.mpr hperiodBudget
  · intro i
    rw [frame.child_sides]
    exact inherited_relative_width hp hδ hδchild hwidthBudget (Nat.cast_nonneg _) (hc.2 i) (hside i)

theorem PhysicalEpochFrame.extend_records_of_comparison
    {σ : Type u} [Fintype σ] [DecidableEq σ] {s bound m a J : ℕ} {gap B : ℝ}
    {base : PhysicalEpochSource.{u, v} σ (s + 1) bound}
    (frame : PhysicalEpochFrame base) (c : PhysicalEpochComparison base m a J gap)
    (hc : c.Controlled) (hdiv : ∀ r ∈ frame.state.records, r.modulus ∣ m)
    (hB : B ≤ base.recordBudget)
    (hwide : ∀ i, 2 * ((m * a * J : ℕ) : ℝ) ≤ (c.sides i : ℝ))
    (hevent : ResiduePairDimensionDrop base.model base.weights base.adapted c.test
      (epochRecordIntersection frame.state.records) c.lower c.sides (m * a) c.anchor c.refined
      (fun _ => J) B) :
    ∃ state : PhysicalEpochRecords base,
      (∃ r, state.records = r :: frame.state.records) ∧
      (∀ r ∈ state.records, r.modulus ∣ m * J) ∧ state.dimension < frame.state.dimension := by
  obtain ⟨r, hhistory, hcontrolled, hmoduli, hdrop⟩ :=
    frame.state.history.extend_of_event base.model base.weights base.adapted base.fixedMap c.test
      (fun i => (base.sides i : ℝ)) base.recordBudget B frame.state.records
      frame.state.controlled c.lower c.sides m a J c.selected_pos c.auxiliary_pos c.pending_pos
      hdiv hB hc.1 c.anchor c.refined c.orbit c.compatible hwide
      (fun i => by simpa only [mul_assoc] using hc.2 i) hevent
  exact ⟨⟨r :: frame.state.records, hhistory, hcontrolled⟩, ⟨r, rfl⟩, hmoduli, hdrop⟩

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

noncomputable def physicalResidueMean {σ : Type*} [Fintype σ] [DecidableEq σ]
    (f : (σ → ℤ) → ℂ) (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (u : σ → ℤ) : ℂ :=
  𝔼 x : IntegerResidueBox lo (fun i => lo i + N i) (fun _ => (M : ℤ)) u,
    f (fun i => (x i).val)

namespace RationalFilteredNilmanifold.Niltest

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d}

theorem scalarAffinePullback_eval_stride (T : D.Niltest (fun _ : σ => 1))
    (M : ℕ) (u x : σ → ℤ) (hx : ∀ i, x i ≡ u i [ZMOD (M : ℤ)]) :
    (T.scalarAffinePullback (M : ℚ) (fun i => (u i : ℚ))).eval (commonStrideIndex u M x) = T.eval x := by
  have heq : (fun i => (M : ℤ) * commonStrideIndex u M x i + u i) = x := by
    funext i
    have h := congrFun (commonStridePoint_index_of_modEq u M x hx) i
    change u i + (M : ℤ) * commonStrideIndex u M x i = x i at h
    linarith
  simpa only [Int.cast_natCast, heq] using T.scalarAffinePullback_eval_integer (M : ℤ) u (commonStrideIndex u M x)

theorem scalarAffinePullback_pair_false [Fintype σ] [DecidableEq σ]
    (T : D.Niltest (fun _ : σ => 1)) (lo : σ → ℤ) (N : σ → ℕ) (M J : ℕ) (u v : σ → ℤ) :
    residuePairMean (T.scalarAffinePullback (M : ℚ) (fun i => (u i : ℚ))).eval lo N M u v (fun _ => J) false =
      physicalResidueMean T.eval lo N M u := by
  rw [residuePairMean_false]
  apply Finset.expect_congr rfl
  intro x _
  exact T.scalarAffinePullback_eval_stride M u (fun i => (x i).val)
    (fun i => (Finset.mem_filter.mp (x i).property).2)

theorem scalarAffinePullback_pair_true [Fintype σ] [DecidableEq σ]
    (T : D.Niltest (fun _ : σ => 1)) (lo : σ → ℤ) (N : σ → ℕ) (M J : ℕ) (u v : σ → ℤ)
    (hv : ∀ i, v i ≡ u i [ZMOD (M : ℤ)]) :
    residuePairMean (T.scalarAffinePullback (M : ℚ) (fun i => (u i : ℚ))).eval lo N M u v (fun _ => J) true =
      physicalResidueMean T.eval lo N (M * J) v := by
  rw [residuePairMean_true]
  apply Finset.expect_congr rfl
  intro x _
  apply T.scalarAffinePullback_eval_stride
  intro i
  have hd : (M : ℤ) ∣ ((M * J : ℕ) : ℤ) := by exact_mod_cast Nat.dvd_mul_right M J
  exact (Int.ModEq.of_dvd hd (Finset.mem_filter.mp (x i).property).2).trans (hv i)

end RationalFilteredNilmanifold.Niltest

universe u v

theorem exists_initial_physical_comparison
    {σ : Type u} [Fintype σ] [DecidableEq σ] {s bound m J : ℕ} {gap : ℝ}
    (base : PhysicalEpochSource.{u, v} σ s bound) (T : base.model.Niltest (fun _ : σ => 1))
    (horbit : T.orbit = base.fixedMap.orbit) (hpositive : T.UnitIntervalValued)
    (hcomplexity : T.ComplexityLE base.incomingBudget)
    (hm : 0 < m) (hJ : 0 < J) (anchor refined : σ → ℤ)
    (hanchor : ∀ i, base.lower i ≤ anchor i ∧ anchor i < base.lower i + base.sides i)
    (hrefined : ∀ i, base.lower i ≤ refined i ∧ refined i < base.lower i + base.sides i)
    (hcompat : ∀ i, refined i ≡ anchor i [ZMOD (m : ℤ)])
    (hgap : 0 < gap) (hgap1 : gap ≤ 1) (hinverse : gap⁻¹ ≤ Real.exp base.incomingBudget)
    (hrecord : 2 ≤ base.recordBudget)
    (hdiscrepancy : gap ≤ ‖physicalResidueMean T.eval base.lower base.sides m anchor -
      physicalResidueMean T.eval base.lower base.sides (m * J) refined‖) :
    ∃ c : PhysicalEpochComparison base m 1 J gap,
      c.Controlled ∧ c.anchor = anchor ∧ c.refined = refined ∧ c.lower = base.lower ∧ c.sides = base.sides := by
  let S := T.scalarAffinePullback (m : ℚ) (fun i => (anchor i : ℚ))
  have hSorbit : S.orbit = (base.fixedMap.scalarAffinePullback (m : ℚ) (fun i => (anchor i : ℚ))).orbit := by
    dsimp only [S, RationalFilteredNilmanifold.Niltest.scalarAffinePullback,
      RationalFilteredNilmanifold.Niltest.substitute]
    rw [horbit]
  have hpair : gap ≤ ‖residuePairMean S.eval base.lower base.sides m anchor refined (fun _ => J) false -
      residuePairMean S.eval base.lower base.sides m anchor refined (fun _ => J) true‖ := by
    rw [T.scalarAffinePullback_pair_false, T.scalarAffinePullback_pair_true _ _ _ _ _ _ hcompat]
    exact hdiscrepancy
  let c : PhysicalEpochComparison base m 1 J gap := {
    selected_pos := hm
    auxiliary_pos := by omega
    pending_pos := hJ
    lower := base.lower
    sides := base.sides
    sides_pos := base.sides_pos
    contained := fun _ => ⟨le_rfl, le_rfl⟩
    anchor := anchor
    refined := refined
    anchor_inside := hanchor
    refined_inside := hrefined
    compatible := by simpa only [Nat.mul_one] using hcompat
    test := S
    orbit := by simpa only [Nat.mul_one] using hSorbit
    positive := hpositive
    complexity := hcomplexity
    gap_pos := hgap
    gap_le_one := hgap1
    gap_inverse := hinverse
    discrepancy := by simpa only [Nat.mul_one] using hpair }
  refine ⟨c, ?_, rfl, rfl, rfl, rfl⟩
  have htwo : 2 ≤ Real.exp base.recordBudget := by linarith [Real.add_one_le_exp base.recordBudget]
  have hcoef : 2 * Real.exp (-base.recordBudget) ≤ 1 := by
    calc
      2 * Real.exp (-base.recordBudget) ≤ Real.exp base.recordBudget * Real.exp (-base.recordBudget) :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
      _ = 1 := by rw [← Real.exp_add]; simp
  exact ⟨by simp only [Nat.cast_one]; linarith,
    fun i => by simpa only [one_mul] using mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg (α := ℝ) (base.sides i))⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exp_neg_le_of_positive_inverse_bound {t F : ℝ} (ht : 0 < t)
    (h : t⁻¹ ≤ Real.exp F) : Real.exp (-F) ≤ t := by
  have hprod : 1 ≤ t * Real.exp F := by
    calc
      1 = t * t⁻¹ := (mul_inv_cancel₀ ht.ne').symm
      _ ≤ t * Real.exp F := mul_le_mul_of_nonneg_left h ht.le
  calc
    Real.exp (-F) = 1 * Real.exp (-F) := (one_mul _).symm
    _ ≤ (t * Real.exp F) * Real.exp (-F) := mul_le_mul_of_nonneg_right hprod (Real.exp_nonneg _)
    _ = t := by rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

theorem physical_visit_numerics {σ : Type*} [Fintype σ]
    (N : σ → ℝ) {M Q U F B ε δ : ℝ}
    (hM : 1 ≤ M) (hMQ : M ≤ Q) (hU : 0 ≤ U) (hF : 0 ≤ F) (hB : B ≤ U)
    (hε : 0 < ε) (hδ : 0 < δ)
    (hεinv : ε⁻¹ ≤ Real.exp F) (hδinv : δ⁻¹ ≤ Real.exp F)
    (hlarge : ∀ i, 16 * ((Fintype.card σ : ℝ) + 1) * Q * Real.exp (U + 2 * F) ≤ N i) :
    (∀ i, 2 * M ≤ N i) ∧
    (∀ i, M * (Real.exp B + 1) ≤ N i) ∧
    (∀ i, 8 ≤ δ * N i) ∧
    (∑ i, Q / N i) ≤ δ * ε / 8 := by
  let k : ℝ := (Fintype.card σ : ℝ) + 1
  have hk : 1 ≤ k := by dsimp [k]; have := Nat.cast_nonneg (α := ℝ) (Fintype.card σ); linarith
  have hQ : 1 ≤ Q := hM.trans hMQ
  have hQ0 : 0 < Q := by linarith
  have hk0 : 0 < k := by linarith
  have hE : 1 ≤ Real.exp U := Real.one_le_exp hU
  have hexpand : Real.exp U ≤ Real.exp (U + 2 * F) := Real.exp_le_exp.mpr (by linarith)
  have hscale : 2 ≤ 16 * k := by linarith
  have hwidth : ∀ i, 2 * Q * Real.exp U ≤ N i := by
    intro i
    calc
      2 * Q * Real.exp U ≤ 16 * k * Q * Real.exp (U + 2 * F) := by gcongr
      _ ≤ N i := hlarge i
  have h16 : ∀ i, 16 * Real.exp (U + 2 * F) ≤ N i := by
    intro i
    calc
      16 * Real.exp (U + 2 * F) ≤ 16 * k * Q * Real.exp (U + 2 * F) := by
        have : 1 ≤ k * Q := one_le_mul_of_one_le_of_one_le hk hQ
        nlinarith [Real.exp_pos (U + 2 * F)]
      _ ≤ N i := hlarge i
  have hδlower := exp_neg_le_of_positive_inverse_bound hδ hδinv
  have hεlower := exp_neg_le_of_positive_inverse_bound hε hεinv
  have hpair : Real.exp (-(2 * F)) ≤ δ * ε := by
    calc
      Real.exp (-(2 * F)) = Real.exp (-F) * Real.exp (-F) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ δ * ε := mul_le_mul hδlower hεlower (Real.exp_nonneg _) hδ.le
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    calc
      2 * M ≤ 2 * Q * Real.exp U := by nlinarith
      _ ≤ N i := hwidth i
  · intro i
    have : Real.exp B + 1 ≤ 2 * Real.exp U := by linarith [Real.exp_le_exp.mpr hB]
    calc
      M * (Real.exp B + 1) ≤ Q * (2 * Real.exp U) :=
        mul_le_mul hMQ this (by positivity) (by linarith)
      _ = 2 * Q * Real.exp U := by ring
      _ ≤ N i := hwidth i
  · intro i
    have hside : 8 * Real.exp F ≤ N i := by
      calc
        8 * Real.exp F ≤ 16 * Real.exp (U + 2 * F) := by
          have := Real.exp_le_exp.mpr (show F ≤ U + 2 * F by linarith)
          nlinarith [Real.exp_pos F]
        _ ≤ N i := h16 i
    calc
      8 = Real.exp (-F) * (8 * Real.exp F) := by
        rw [show Real.exp (-F) * (8 * Real.exp F) = 8 * (Real.exp (-F) * Real.exp F) by ring,
          ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
      _ ≤ δ * N i := mul_le_mul hδlower hside (by positivity) hδ.le
  · have hterm : ∀ i, Q / N i ≤ (δ * ε) / (16 * k) := by
      intro i
      have hbase : 16 * k * Q * Real.exp (2 * F) ≤ N i := by
        calc
          16 * k * Q * Real.exp (2 * F) ≤ 16 * k * Q * Real.exp (U + 2 * F) := by gcongr; linarith
          _ ≤ N i := hlarge i
      calc
        Q / N i ≤ Q / (16 * k * Q * Real.exp (2 * F)) :=
          div_le_div_of_nonneg_left hQ0.le (by positivity) hbase
        _ = Real.exp (-(2 * F)) / (16 * k) := by
          rw [Real.exp_neg]
          field_simp
        _ ≤ (δ * ε) / (16 * k) := div_le_div_of_nonneg_right hpair (by positivity)
    calc
      (∑ i, Q / N i) ≤ ∑ _i : σ, (δ * ε) / (16 * k) := Finset.sum_le_sum (fun i _ => hterm i)
      _ = (Fintype.card σ : ℝ) * ((δ * ε) / (16 * k)) := by simp
      _ = ((Fintype.card σ : ℝ) / (16 * k)) * (δ * ε) := by ring
      _ ≤ (1 / 8) * (δ * ε) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg hδ.le hε.le)
        apply (div_le_iff₀ (show 0 < 16 * k by positivity)).mpr
        dsimp only [k]
        have := Nat.cast_nonneg (α := ℝ) (Fintype.card σ)
        linarith
      _ = δ * ε / 8 := by ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

universe u v

theorem PhysicalEpochFrame.uniform_visit_bounds
    {σ : Type u} [Fintype σ] [DecidableEq σ] {s bound m a J : ℕ} {gap U F B ε δ : ℝ}
    {base : PhysicalEpochSource.{u, v} σ (s + 1) bound}
    (frame : PhysicalEpochFrame base) (c : PhysicalEpochComparison base m a J gap)
    (hc : c.Controlled) (hrecord : base.recordBudget ≤ U)
    (hperiod : (frame.period : ℝ) ≤ Real.exp U) (hF : 0 ≤ F) (hB : B ≤ U)
    (hε : 0 < ε) (hδ : 0 < δ) (hεinv : ε⁻¹ ≤ Real.exp F) (hδinv : δ⁻¹ ≤ Real.exp F)
    (hsource : ∀ i, ((m * J : ℕ) : ℝ) * Real.exp (5 * U + 2 * F + 16) ≤ (base.sides i : ℝ)) :
    (∀ i, 2 * ((m * a * J : ℕ) : ℝ) ≤ (c.sides i : ℝ)) ∧
    (∀ i, ((m * a * J : ℕ) : ℝ) * (Real.exp B + 1) ≤ (c.sides i : ℝ)) ∧
    (∀ i, 8 ≤ δ * (c.sides i : ℝ)) ∧
    (∑ i, ((Nat.lcm (m * a) (m * a * frame.period) * J : ℕ) : ℝ) / (c.sides i : ℝ)) ≤ δ * ε / 8 := by
  let k : ℝ := (Fintype.card σ : ℝ) + 1
  let T : ℝ := ((m * J : ℕ) : ℝ)
  let Q : ℝ := ((m * a * frame.period * J : ℕ) : ℝ)
  have hU : 0 ≤ U := base.incoming_nonneg.trans (base.incoming_le_record.trans hrecord)
  have hT : 0 ≤ T := Nat.cast_nonneg _
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have haux : (a : ℝ) ≤ Real.exp U := hc.1.trans (Real.exp_le_exp.mpr hrecord)
  have hQ : Q ≤ T * Real.exp (2 * U) := by
    calc
      Q = T * ((a : ℝ) * (frame.period : ℝ)) := by dsimp [Q, T]; push_cast; ring_nf
      _ ≤ T * (Real.exp U * Real.exp U) :=
        mul_le_mul_of_nonneg_left (mul_le_mul haux hperiod (Nat.cast_nonneg _) (Real.exp_nonneg _)) hT
      _ = T * Real.exp (2 * U) := by rw [← Real.exp_add]; congr 1; ring_nf
  have hkexp : k ≤ Real.exp U := by
    dsimp only [k]
    linarith [base.coordinates_le, base.incoming_le_record, Real.add_one_le_exp U]
  have h16 : (16 : ℝ) ≤ Real.exp 16 := by linarith [Real.add_one_le_exp (16 : ℝ)]
  have hcoeff : 16 * k ≤ Real.exp (U + 16) := by
    calc
      16 * k ≤ Real.exp 16 * Real.exp U := mul_le_mul h16 hkexp hk (Real.exp_nonneg _)
      _ = Real.exp (U + 16) := by rw [← Real.exp_add]; congr 1; ring_nf
  have hsmall : ∀ i, 16 * k * T * Real.exp (4 * U + 2 * F) ≤ (base.sides i : ℝ) := by
    intro i
    calc
      16 * k * T * Real.exp (4 * U + 2 * F) ≤ Real.exp (U + 16) * T * Real.exp (4 * U + 2 * F) := by gcongr
      _ = T * (Real.exp (U + 16) * Real.exp (4 * U + 2 * F)) := by ring_nf
      _ = T * Real.exp (5 * U + 2 * F + 16) := by rw [← Real.exp_add]; congr 1; ring_nf
      _ ≤ (base.sides i : ℝ) := hsource i
  have hlarge : ∀ i, 16 * k * Q * Real.exp (U + 2 * F) ≤ (c.sides i : ℝ) := by
    intro i
    have hexp : Real.exp (2 * U) * Real.exp (U + 2 * F) =
        Real.exp (-U) * Real.exp (4 * U + 2 * F) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring_nf
    calc
      16 * k * Q * Real.exp (U + 2 * F) ≤ 16 * k * (T * Real.exp (2 * U)) * Real.exp (U + 2 * F) := by gcongr
      _ = 16 * k * T * (Real.exp (2 * U) * Real.exp (U + 2 * F)) := by ring_nf
      _ = Real.exp (-U) * (16 * k * T * Real.exp (4 * U + 2 * F)) := by rw [hexp]; ring_nf
      _ ≤ Real.exp (-U) * (base.sides i : ℝ) := mul_le_mul_of_nonneg_left (hsmall i) (Real.exp_nonneg _)
      _ ≤ Real.exp (-base.recordBudget) * (base.sides i : ℝ) := by gcongr
      _ ≤ 2 * Real.exp (-base.recordBudget) * (base.sides i : ℝ) := by
        nlinarith [mul_nonneg (Real.exp_nonneg (-base.recordBudget)) (Nat.cast_nonneg (α := ℝ) (base.sides i))]
      _ ≤ (c.sides i : ℝ) := hc.2 i
  have hM : 1 ≤ ((m * a * J : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Nat.mul_ne_zero c.selected_pos.ne' c.auxiliary_pos.ne') c.pending_pos.ne')
  have hMQ : ((m * a * J : ℕ) : ℝ) ≤ Q := by
    have hp : 1 ≤ frame.period := frame.period_pos
    have h := Nat.mul_le_mul_right J (Nat.mul_le_mul_left (m * a) hp)
    simpa only [Nat.mul_one, Q] using (Nat.cast_le (α := ℝ)).mpr h
  obtain ⟨hwide, hstep, hround, hcount⟩ := physical_visit_numerics (fun i => (c.sides i : ℝ))
    hM hMQ hU hF hB hε hδ hεinv hδinv hlarge
  refine ⟨hwide, hstep, hround, ?_⟩
  have hlcm : Nat.lcm (m * a) (m * a * frame.period) = m * a * frame.period :=
    Nat.lcm_eq_right_iff_dvd.mpr (Nat.dvd_mul_right (m * a) frame.period)
  simpa only [hlcm] using hcount

end Erdos3

end

end OAI
