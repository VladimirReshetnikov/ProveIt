/- Modified for ProveIt: Use IsModuleTopology.topologicalAddGroup on Lean 4.32; statements unchanged. -/
import OAI.Combinatorics.Progressions.Dynamics.AnchoredEpochVisit
import OAI.Combinatorics.Progressions.Dynamics.ControlledAdaptedEpochChild
import OAI.Combinatorics.Progressions.Dynamics.RetainedEpochTransition
import OAI.Combinatorics.Progressions.Estimates.PhysicalChildComparison
import OAI.Combinatorics.Progressions.Estimates.PhysicalOrbitRecovery

namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

universe u v

structure PhysicalEpochFrame {σ : Type u} [Fintype σ] [DecidableEq σ] {s bound : ℕ}
    (base : PhysicalEpochSource.{u, v} σ (s + 1) bound) where
  state : PhysicalEpochRecords base
  modulus : ℕ
  modulus_pos : 0 < modulus
  anchor : σ → ℤ
  anchor_inside : ∀ i, base.lower i ≤ anchor i ∧ anchor i < base.lower i + base.sides i
  record_moduli : ∀ r ∈ state.records, r.modulus ∣ modulus
  work : ℝ
  incoming_le_work : base.incomingBudget + 16 ≤ work
  record_le_work : base.recordBudget + 16 ≤ work
  period : ℕ
  period_pos : 0 < period
  freezePower : ℕ
  eventPower : ℕ
  period_le : (period : ℝ) ≤ Real.exp ((work + 2) ^ freezePower)
  child : PhysicalEpochSource.{u, v} σ s bound
  child_lower : child.lower = base.lower
  child_sides : child.sides = base.sides
  child_dimension_le : child.dimension ≤ base.dimension
  childCost : ℝ
  childCost_nonneg : 0 ≤ childCost
  childCost_le : childCost ≤ child.incomingBudget
  incoming_le_child : base.incomingBudget + 16 ≤ child.incomingBudget
  work_le_child : work ≤ child.incomingBudget
  transition : FixedAffineEpochTransition base.model base.weights base.adapted
    (epochRecordIntersection state.records)
    (base.fixedMap.scalarAffinePullback (modulus : ℚ) (fun i => (anchor i : ℚ)))
    (fun i => (base.sides i : ℝ) / modulus)
    child.model (child.fixedMap.scalarAffinePullback (modulus : ℚ) (fun i => (anchor i : ℚ))).orbit
    work childCost period freezePower eventPower

end Erdos3

end

section

namespace Erdos3

universe u v

theorem exists_physical_frame_precision :
    ∃ Ke : ℕ, 2 ≤ Ke ∧ ∀ C : ℕ, ∃ Kf : ℕ, 2 ≤ Kf ∧
      ∀ {σ : Type u} [Fintype σ] [DecidableEq σ] {s bound m a J : ℕ} {gap : ℝ}
        {base : PhysicalEpochSource.{u, v} σ (s + 1) bound}
        (frame : PhysicalEpochFrame base) (_c : PhysicalEpochComparison base m a J gap),
      frame.freezePower ≤ C → ∃ rho q ε δ : ℝ,
        base.incomingBudget + 16 ≤ q ∧ verticalDecompositionBudget (base.incomingBudget + 16) ≤ q ∧
        q ≤ (base.incomingBudget + 2) ^ Ke ∧ 0 < rho ∧ rho⁻¹ ≤ Real.exp (base.incomingBudget + 16) ∧
        0 < ε ∧ ε < 1 / 2 ∧ 0 < δ ∧ δ ≤ 1 ∧
        ε⁻¹ ≤ Real.exp ((frame.work + 2) ^ Kf) ∧ δ⁻¹ ≤ Real.exp ((frame.work + 2) ^ Kf) ∧
        2 * (2 * rho + Real.exp (verticalDecompositionBudget (base.incomingBudget + 16) - q)) ≤ gap / 2 ∧
        8 * ε + 2 * (Real.exp ((frame.work + 2) ^ frame.freezePower) * δ) ≤ gap / 4 := by
  obtain ⟨Ke, hKe, hprecision⟩ := exists_separated_residue_precision
  refine ⟨Ke, hKe, ?_⟩
  intro C
  obtain ⟨Kf, hKf, hstep⟩ := hprecision C
  refine ⟨Kf, hKf, ?_⟩
  intro σ _ _ s bound m a J gap base frame c hC
  obtain ⟨rho, q, hpq, hfreq, hq, hrho, hrhop, hprojection, hfreezing⟩ :=
    hstep base.incomingBudget base.incoming_nonneg gap c.gap_pos c.gap_le_one c.gap_inverse
  obtain ⟨ε, δ, hε, hεhalf, hδ, hδone, hεbound, hδbound, herror⟩ :=
    hfreezing frame.work frame.incoming_le_work
  refine ⟨rho, q, ε, δ, hpq, hfreq, hq, hrho, hrhop, hε, hεhalf, hδ, hδone,
    hεbound, hδbound, hprojection, ?_⟩
  have hwork : 0 ≤ frame.work := by linarith [frame.incoming_le_work, base.incoming_nonneg]
  have hpow : (frame.work + 2) ^ frame.freezePower ≤ (frame.work + 2) ^ C :=
    pow_le_pow_right₀ (by linarith) hC
  calc
    8 * ε + 2 * (Real.exp ((frame.work + 2) ^ frame.freezePower) * δ) ≤
        8 * ε + 2 * (Real.exp ((frame.work + 2) ^ C) * δ) := by gcongr
    _ = gap / 4 := herror

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct BigOperators

universe u v

theorem PhysicalEpochFrame.visit
    {σ : Type u} [Fintype σ] [DecidableEq σ] {s bound m a J : ℕ} {gap : ℝ}
    {base : PhysicalEpochSource.{u, v} σ (s + 1) bound}
    (frame : PhysicalEpochFrame base) (c : PhysicalEpochComparison base m a J gap)
    (hdiv : frame.modulus ∣ m * a)
    (hcompat : ∀ i, c.anchor i ≡ frame.anchor i [ZMOD (frame.modulus : ℤ)])
    (q rho ε δ : ℝ) (hpq : base.incomingBudget + 16 ≤ q)
    (hfreq : verticalDecompositionBudget (base.incomingBudget + 16) ≤ q)
    (hrho : 0 < rho) (hrhop : rho⁻¹ ≤ Real.exp (base.incomingBudget + 16))
    (hcop : (m * a * (m * a * frame.period)).Coprime J)
    (hsteplarge : ∀ i, ((m * a * J : ℕ) : ℝ) *
      (Real.exp ((q + frame.eventPower) ^ frame.eventPower) + 1) ≤ (c.sides i : ℝ))
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hε : ε < 1 / 2)
    (hprojection : 2 * (2 * rho + Real.exp (verticalDecompositionBudget (base.incomingBudget + 16) - q)) ≤ gap / 2)
    (hfreezing : 8 * ε + 2 * (Real.exp ((frame.work + 2) ^ frame.freezePower) * δ) ≤ gap / 4)
    (hlarge : ∀ i, 8 ≤ δ * (c.sides i : ℝ))
    (hcount : (∑ i, ((Nat.lcm (m * a) (m * a * frame.period) * J : ℕ) : ℝ) / (c.sides i : ℝ)) ≤ δ * ε / 8) :
    ResiduePairDimensionDrop base.model base.weights base.adapted c.test
      (epochRecordIntersection frame.state.records) c.lower c.sides (m * a) c.anchor c.refined
      (fun _ => J) ((q + frame.eventPower) ^ frame.eventPower) ∨
    ∃ next : PhysicalEpochComparison frame.child m (a * frame.period) J (gap / 4),
      (∀ i, c.lower i ≤ next.lower i ∧ next.lower i + next.sides i ≤ c.lower i + c.sides i) ∧
      (∀ i, δ * (c.sides i : ℝ) / 8 ≤ (next.sides i : ℝ) ∧ (next.sides i : ℝ) ≤ δ * (c.sides i : ℝ) / 2) ∧
      (∀ i, next.anchor i ≡ c.anchor i [ZMOD (m * a : ℕ)]) ∧
      (∀ i, next.refined i ≡ c.refined i [ZMOD (m * a * J : ℕ)]) := by
  have hparent := base.fixedMap.scalarAffinePullback_refinement_orbit frame.anchor c.anchor hdiv hcompat
  have hinput : c.test.orbit = base.model.filtration.realification.scalarAffineOrbitHom (m * a / frame.modulus : ℕ)
      (fun i => (commonStrideIndex frame.anchor frame.modulus c.anchor i : ℚ))
      (base.fixedMap.scalarAffinePullback (frame.modulus : ℚ) (fun i => (frame.anchor i : ℚ))).orbit :=
    c.orbit.trans hparent.symm
  have hresult := FixedAffineEpochTransition.on_anchored_box
    base.model base.weights base.adapted (epochRecordIntersection frame.state.records)
    (base.fixedMap.scalarAffinePullback (frame.modulus : ℚ) (fun i => (frame.anchor i : ℚ)))
    frame.child.model (frame.child.fixedMap.scalarAffinePullback (frame.modulus : ℚ) (fun i => (frame.anchor i : ℚ))).orbit
    frame.work frame.childCost frame.period frame.freezePower frame.eventPower
    base.lower frame.anchor base.sides frame.modulus frame.modulus_pos frame.anchor_inside frame.transition
    (base.incomingBudget + 16) (by linarith [base.incoming_nonneg]) frame.incoming_le_work
    c.lower c.anchor c.refined c.sides (m * a) (fun _ => J) (Nat.mul_pos c.selected_pos c.auxiliary_pos)
    hdiv hcompat c.anchor_inside c.contained c.sides_pos c.test hinput c.positive
    (c.complexity.mono (by linarith)) q rho hpq (base.coordinates_le.trans (by linarith))
    hfreq hrho hrhop (fun _ => c.pending_pos) c.compatible (fun _ => hcop) hsteplarge
    gap ε δ hδ hδone hε hprojection hfreezing hlarge hcount c.discrepancy
  rcases hresult with hevent | hchild
  · exact Or.inl hevent
  · have hchildOrbit := frame.child.fixedMap.scalarAffinePullback_refinement_orbit
      frame.anchor c.anchor hdiv hcompat
    have hchild' : AnchoredChildResidueComparison frame.child.model
        (frame.child.fixedMap.scalarAffinePullback (m * a : ℕ) (fun i => (c.anchor i : ℚ))).orbit
        frame.childCost (gap / 4) δ c.lower c.sides (m * a) frame.period c.anchor c.refined (fun _ => J) := by
      rw [← hchildOrbit]
      exact hchild
    exact Or.inr (physical_comparison_of_anchored frame.child m a J frame.period
      c.selected_pos c.auxiliary_pos c.pending_pos frame.period_pos c.lower c.sides c.anchor c.refined
      frame.childCost (gap / 4) δ frame.childCost_le (div_pos c.gap_pos (by norm_num)) (by linarith [c.gap_le_one])
      (quarter_discrepancy_inverse c.gap_inverse frame.incoming_le_child)
      (fun i => by simpa only [frame.child_lower, frame.child_sides] using c.contained i) hchild')

end Erdos3

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold
open scoped TensorProduct

universe u v

theorem exists_physical_epoch_frame (s : ℕ) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ {σ : Type u} [Fintype σ] [DecidableEq σ] {bound : ℕ}
      (base : PhysicalEpochSource.{u, v} σ (s + 1) bound) (state : PhysicalEpochRecords base)
      (M : ℕ), 0 < M → ∀ anchor : σ → ℤ,
      (∀ i, base.lower i ≤ anchor i ∧ anchor i < base.lower i + base.sides i) →
      (∀ r ∈ state.records, r.modulus ∣ M) →
      ∀ inflate : ℝ → ℝ, (∀ p, 0 ≤ p → p ≤ inflate p) →
      (∀ i, Real.exp ((base.recordBudget + 2) ^ K) ≤ (base.sides i : ℝ) / M) →
      ∃ frame : PhysicalEpochFrame base,
        frame.state = state ∧ frame.modulus = M ∧ frame.anchor = anchor ∧
        frame.work ≤ (base.recordBudget + 2) ^ K ∧
        frame.child.incomingBudget ≤ (base.recordBudget + 2) ^ K ∧
        frame.child.recordBudget = inflate frame.child.incomingBudget ∧
        (frame.period : ℝ) ≤ Real.exp ((base.recordBudget + 2) ^ K) ∧
        frame.freezePower ≤ K ∧ frame.eventPower ≤ K := by
  obtain ⟨C, K₀, _, _, hretained⟩ := exists_retained_epoch_from_records s
  obtain ⟨B, _, htransition⟩ := exists_retained_affine_epoch_transition s
  obtain ⟨R, _, hadapted⟩ := exists_controlled_adapted_epoch_child
  let Q : Polynomial ℕ := (Polynomial.X + 2) ^ K₀ +
    ((Polynomial.X + 2) ^ K₀ + Polynomial.C R) ^ R + Polynomial.X + 16 +
    ((Polynomial.X + 2) ^ K₀ + 2) ^ C
  obtain ⟨K₁, hK₁, hbudget⟩ := exists_natPolynomial_fixed_power_budget Q
  let K := max K₁ (max B C)
  refine ⟨K, hK₁.trans (le_max_left _ _), ?_⟩
  intro σ _ _ bound base state M hM anchor hanchor hdiv inflate hinflate hlarge
  let p := base.recordBudget
  have hp : 0 ≤ p := base.incoming_nonneg.trans base.incoming_le_record
  have hK₁K : (p + 2) ^ K₁ ≤ (p + 2) ^ K :=
    pow_le_pow_right₀ (by linarith : 1 ≤ p + 2) (le_max_left _ _)
  have hsum : (p + 2) ^ K₀ + ((p + 2) ^ K₀ + R) ^ R + p + 16 +
      ((p + 2) ^ K₀ + 2) ^ C ≤ (p + 2) ^ K := by
    have h := hbudget p hp
    simp only [Q, Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_ofNat, Polynomial.eval₂_C] at h
    exact h.trans hK₁K
  have hpow0 : 0 ≤ (p + 2) ^ K₀ := by positivity
  have hpowR : 0 ≤ ((p + 2) ^ K₀ + R) ^ R := by positivity
  have hperiodPow0 : 0 ≤ ((p + 2) ^ K₀ + 2) ^ C := by positivity
  have hsize : (p + 2) ^ K₀ ≤ (p + 2) ^ K := by linarith
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hspan : ∀ i, (M : ℝ) * ((base.sides i : ℝ) / M) ≤ (base.sides i : ℝ) := by
    intro i
    apply le_of_eq
    field_simp
  obtain ⟨work, cost, hpwork, hwork, hcost0, hcost, hepoch⟩ :=
    hretained base.model base.weights base.adapted base.fixedMap state.records state.history
      p hp (base.geometry.mono base.model base.incoming_le_record)
      (base.coordinates_le.trans base.incoming_le_record)
      (fun i => (base.sides i : ℝ)) state.controlled M hM hdiv
      (fun i => (base.sides i : ℝ) / M)
      (fun i => (Real.exp_le_exp.mpr hsize).trans (hlarge i)) hspan (fun i => (anchor i : ℚ))
  obtain ⟨P, hP, hPb, E, hE, n, hn, V₀, hV₀, hchild⟩ :=
    htransition base.model base.weights base.adapted (epochRecordIntersection state.records)
      (base.fixedMap.scalarAffinePullback (M : ℚ) (fun i => (anchor i : ℚ)))
      (fun i => (base.sides i : ℝ) / M) work cost C (by linarith) hepoch
  let N := (base.model.filtration.gradedRefiltrationSubalgebra (epochRecordIntersection state.records)) ⧸
    E.filtration.layerIdeal (s + 1)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] N)
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] N)
  let := realification_moduleTopology_t2 V₀.basis
  obtain ⟨V, _, _, hV, childOrbit, _, hstep⟩ := hchild
  obtain ⟨F, hdimension, hgeometry, hstep'⟩ := hadapted base.model base.weights base.adapted
    (epochRecordIntersection state.records)
    (base.fixedMap.scalarAffinePullback (M : ℚ) (fun i => (anchor i : ℚ)))
    (fun i => (base.sides i : ℝ) / M) V childOrbit work cost P C B hcost0 hV hstep
  let childCost := (cost + R) ^ R
  let next := base.incomingBudget + work + childCost + 16
  have hwork0 : 0 ≤ work := by linarith
  have hchildCost0 : 0 ≤ childCost := by dsimp only [childCost]; positivity
  have hnext0 : 0 ≤ next := by dsimp only [next]; linarith [base.incoming_nonneg]
  have hchildCost : childCost ≤ ((p + 2) ^ K₀ + R) ^ R := by
    dsimp only [childCost]
    gcongr
  have hnext : next ≤ (p + 2) ^ K := by
    dsimp only [next]
    linarith [base.incoming_le_record]
  let physicalOrbit := F.model.filtration.realification.scalarAffineOrbitHom (1 / (M : ℚ))
    (fun i => -(anchor i : ℚ) / M) childOrbit
  let child : PhysicalEpochSource.{u, v} σ s bound := {
    Carrier := N
    dimension := finrank ℚ N
    dimension_le := (by rw [hdimension]; exact hn.trans base.dimension_le)
    model := F.model
    weights := F.weight
    adapted := F.model_layers
    fixedMap := (RationalFilteredNilmanifold.Niltest.const F.model (fun _ : σ => 1) 0).withOrbit physicalOrbit
    lower := base.lower
    sides := base.sides
    sides_pos := base.sides_pos
    incomingBudget := next
    recordBudget := inflate next
    incoming_nonneg := hnext0
    incoming_le_record := hinflate next hnext0
    geometry := hgeometry.mono F.model (by change childCost ≤ next; dsimp only [next]; linarith [base.incoming_nonneg])
    coordinates_le := base.coordinates_le.trans (by dsimp only [next]; linarith) }
  have hrecover : (child.fixedMap.scalarAffinePullback (M : ℚ) (fun i => (anchor i : ℚ))).orbit = childOrbit := by
    change F.model.filtration.realification.scalarAffineOrbitHom (M : ℚ) (fun i => (anchor i : ℚ))
      (F.model.filtration.realification.scalarAffineOrbitHom (1 / (M : ℚ))
        (fun i => -(anchor i : ℚ) / M) childOrbit) = childOrbit
    exact F.model.filtration.realification.scalarAffineOrbitHom_inverse_recover childOrbit M hM anchor
  let frame : PhysicalEpochFrame base := {
    state := state
    modulus := M
    modulus_pos := hM
    anchor := anchor
    anchor_inside := hanchor
    record_moduli := hdiv
    work := work
    incoming_le_work := by linarith [base.incoming_le_record]
    record_le_work := hpwork
    period := P
    period_pos := hP
    freezePower := C
    eventPower := B
    period_le := hPb
    child := child
    child_lower := rfl
    child_sides := rfl
    child_dimension_le := by change finrank ℚ N ≤ base.dimension; rw [hdimension]; exact hn
    childCost := childCost
    childCost_nonneg := hchildCost0
    childCost_le := by change childCost ≤ next; dsimp only [next]; linarith [base.incoming_nonneg]
    incoming_le_child := by change base.incomingBudget + 16 ≤ next; dsimp only [next]; linarith
    work_le_child := by change work ≤ next; dsimp only [next]; linarith [base.incoming_nonneg]
    transition := by rw [hrecover]; exact hstep' }
  have hperiodWork : (work + 2) ^ C ≤ ((p + 2) ^ K₀ + 2) ^ C := by
    have hwork0 : 0 ≤ work := by linarith
    gcongr
  have hperiodBound : (P : ℝ) ≤ Real.exp ((p + 2) ^ K) :=
    hPb.trans (Real.exp_le_exp.mpr (hperiodWork.trans (by linarith)))
  exact ⟨frame, rfl, rfl, rfl, hwork.trans hsize, hnext, rfl, hperiodBound,
    (le_max_right B C).trans (le_max_right K₁ (max B C)),
    (le_max_left B C).trans (le_max_right K₁ (max B C))⟩

end Erdos3

end

section

namespace Erdos3

universe u v

def PhysicalFrameConstructionBound (s K : ℕ) : Prop :=
  ∀ {σ : Type u} [Fintype σ] [DecidableEq σ] {bound : ℕ}
    (base : PhysicalEpochSource.{u, v} σ (s + 1) bound) (state : PhysicalEpochRecords base)
    (M : ℕ), 0 < M → ∀ anchor : σ → ℤ,
    (∀ i, base.lower i ≤ anchor i ∧ anchor i < base.lower i + base.sides i) →
    (∀ r ∈ state.records, r.modulus ∣ M) →
    ∀ inflate : ℝ → ℝ, (∀ p, 0 ≤ p → p ≤ inflate p) →
    (∀ i, Real.exp ((base.recordBudget + 2) ^ K) ≤ (base.sides i : ℝ) / M) →
    ∃ frame : PhysicalEpochFrame base,
      frame.state = state ∧ frame.modulus = M ∧ frame.anchor = anchor ∧
      frame.work ≤ (base.recordBudget + 2) ^ K ∧
      frame.child.incomingBudget ≤ (base.recordBudget + 2) ^ K ∧
      frame.child.recordBudget = inflate frame.child.incomingBudget ∧
      (frame.period : ℝ) ≤ Real.exp ((base.recordBudget + 2) ^ K) ∧
      frame.freezePower ≤ K ∧ frame.eventPower ≤ K

theorem PhysicalFrameConstructionBound.mono {s K L : ℕ}
    (h : PhysicalFrameConstructionBound.{u, v} s K) (hKL : K ≤ L) :
    PhysicalFrameConstructionBound.{u, v} s L := by
  intro σ _ _ bound base state M hM anchor hanchor hmod inflate hinflate hlarge
  have hp : 0 ≤ base.recordBudget := base.incoming_nonneg.trans base.incoming_le_record
  have hpow : (base.recordBudget + 2) ^ K ≤ (base.recordBudget + 2) ^ L :=
    pow_le_pow_right₀ (by linarith) hKL
  obtain ⟨frame, hs, hm, ha, hw, hi, hr, hperiod, hf, he⟩ :=
    h base state M hM anchor hanchor hmod inflate hinflate
      (fun i => (Real.exp_le_exp.mpr hpow).trans (hlarge i))
  exact ⟨frame, hs, hm, ha, hw.trans hpow, hi.trans hpow, hr,
    hperiod.trans (Real.exp_le_exp.mpr hpow), hf.trans hKL, he.trans hKL⟩

theorem exists_uniform_physical_frame_construction (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ t : ℕ, t ≤ s → PhysicalFrameConstructionBound.{u, v} t C := by
  induction s with
  | zero =>
    obtain ⟨C, hC, hframe⟩ := exists_physical_epoch_frame 0
    refine ⟨C, hC, ?_⟩
    intro t ht
    have : t = 0 := by omega
    subst t
    exact @hframe
  | succ s ih =>
    obtain ⟨C, hC, hframes⟩ := ih
    obtain ⟨K, hK, htop⟩ := exists_physical_epoch_frame (s + 1)
    refine ⟨max C K, hC.trans (le_max_left _ _), ?_⟩
    intro t ht
    by_cases hts : t ≤ s
    · exact PhysicalFrameConstructionBound.mono (@hframes t hts) (le_max_left _ _)
    · have heq : t = s + 1 := by omega
      subst t
      exact PhysicalFrameConstructionBound.mono (@htop) (le_max_right _ _)

end Erdos3

end

end OAI
