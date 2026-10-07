import OAI.Combinatorics.Progressions.Estimates.UniformPhysicalVisitBounds

namespace OAI

section

namespace Erdos3

universe u v

theorem exists_uniform_controlled_frame_visit (C : ℕ) :
    ∃ A Kf : ℕ, 1 ≤ A ∧ 2 ≤ Kf ∧
    ∀ {σ : Type u} [Fintype σ] [DecidableEq σ] {s bound m a J : ℕ} {gap U : ℝ}
      {base : PhysicalEpochSource.{u, v} σ (s + 1) bound}
      (frame : PhysicalEpochFrame base) (c : PhysicalEpochComparison base m a J gap),
    c.Controlled → base.recordBudget ≤ U →
    (base.incomingBudget + 2) ^ A ≤ base.recordBudget →
    (frame.child.incomingBudget + 2) ^ A ≤ frame.child.recordBudget →
    frame.work ≤ U → (frame.period : ℝ) ≤ Real.exp U →
    frame.freezePower ≤ C → frame.eventPower ≤ C →
    frame.modulus ∣ m →
    (∀ i, c.anchor i ≡ frame.anchor i [ZMOD (frame.modulus : ℤ)]) →
    (m * a * (m * a * frame.period)).Coprime J →
    (∀ i, ((m * J : ℕ) : ℝ) * Real.exp (5 * U + 2 * (U + 2) ^ Kf + 16) ≤ (base.sides i : ℝ)) →
    (∃ state : PhysicalEpochRecords base,
      (∃ r, state.records = r :: frame.state.records) ∧
      (∀ r ∈ state.records, r.modulus ∣ m * J) ∧ state.dimension < frame.state.dimension) ∨
    ∃ next : PhysicalEpochComparison frame.child m (a * frame.period) J (gap / 4),
      next.Controlled ∧
      (∀ i, c.lower i ≤ next.lower i ∧ next.lower i + next.sides i ≤ c.lower i + c.sides i) ∧
      (∀ i, next.anchor i ≡ c.anchor i [ZMOD (m * a : ℕ)]) ∧
      (∀ i, next.refined i ≡ c.refined i [ZMOD (m * a * J : ℕ)]) := by
  obtain ⟨Ke, _, hprecision⟩ := exists_physical_frame_precision
  obtain ⟨Kf, hKf, hprecision⟩ := hprecision C
  obtain ⟨A, hA, hinflation⟩ := exists_physical_record_inflation Ke C Kf
  refine ⟨A, Kf, hA, hKf, ?_⟩
  intro σ _ _ s bound m a J gap U base frame c hc hrecord hbase hchild hwork hperiod hfreeze hevent hmod hanchor hcop hsource
  have hU : 0 ≤ U := base.incoming_nonneg.trans (base.incoming_le_record.trans hrecord)
  have hwork0 : 0 ≤ frame.work := by linarith [base.incoming_nonneg, frame.incoming_le_work]
  obtain ⟨rho, q, ε, δ, hpq, hfreq, hq, hrho, hrhop, hε, hεhalf, hδ, hδone,
    hεinv, hδinv, hprojection, hfreezing⟩ := hprecision frame c hfreeze
  have hq1 : 1 ≤ q := by linarith [base.incoming_nonneg]
  have hB : (q + frame.eventPower) ^ frame.eventPower ≤ base.recordBudget :=
    ((hinflation base.incomingBudget base.incoming_nonneg).2.2 q hq1 hq frame.eventPower hevent).trans hbase
  have hF : (frame.work + 2) ^ Kf ≤ (U + 2) ^ Kf :=
    pow_le_pow_left₀ (by linarith) (by linarith) Kf
  obtain ⟨hwide, hstep, hround, hcount⟩ := frame.uniform_visit_bounds c hc hrecord hperiod
    (show 0 ≤ (U + 2) ^ Kf by positivity) (hB.trans hrecord) hε hδ
    (hεinv.trans (Real.exp_le_exp.mpr hF)) (hδinv.trans (Real.exp_le_exp.mpr hF)) hsource
  rcases frame.visit c (hmod.trans (Nat.dvd_mul_right m a)) hanchor q rho ε δ
      hpq hfreq hrho hrhop hcop hstep hδ hδone hεhalf hprojection hfreezing hround hcount with he | hn
  · exact Or.inl (frame.extend_records_of_comparison c hc
      (fun r hr => (frame.record_moduli r hr).trans hmod) hB hwide he)
  · obtain ⟨next, hcontained, hside, hnextAnchor, hnextRefined⟩ := hn
    have hc' := frame.child_comparison_controlled c next hc hfreeze
      ((hinflation frame.child.incomingBudget frame.child.incoming_nonneg).1.trans hchild)
      ((hinflation frame.child.incomingBudget frame.child.incoming_nonneg).2.1.trans hchild)
      hδ hδinv (fun i => (hside i).1)
    exact Or.inr ⟨next, hc', hcontained, hnextAnchor, hnextRefined⟩

end Erdos3

end

end OAI
