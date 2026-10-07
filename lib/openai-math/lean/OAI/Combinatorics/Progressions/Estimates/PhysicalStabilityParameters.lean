import OAI.Combinatorics.Progressions.Dynamics.ScheduledPhysicalEpochStack
import OAI.Combinatorics.Progressions.Lattices.PrimeCoordinateCells
import OAI.Combinatorics.Progressions.Linear.UniformControlledFrameVisit

namespace OAI

section

namespace Erdos3.PhysicalEpochStack

open scoped BigOperators

universe u v

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {bound s : ℕ}
  {base : PhysicalEpochSource.{u, v} σ s bound}

def periods : {s : ℕ} → {base : PhysicalEpochSource.{u, v} σ s bound} → PhysicalEpochStack base → List ℕ
  | _, _, .zero _ => []
  | _, _, .succ frame tail => frame.period :: periods tail

theorem periods_length (stack : PhysicalEpochStack base) : stack.periods.length = s := by
  induction stack with
  | zero => rfl
  | succ frame tail ih => simp only [periods, List.length_cons, ih]

theorem periods_product_pos (stack : PhysicalEpochStack base) : 0 < stack.periods.prod := by
  induction stack with
  | zero => simp [periods]
  | succ frame tail ih => exact Nat.mul_pos frame.period_pos ih

theorem period_dvd_product (stack : PhysicalEpochStack base) {P : ℕ} (hP : P ∈ stack.periods) :
    P ∣ stack.periods.prod := List.dvd_prod hP

theorem UniformAt.periods_product_le {A M : ℕ} {anchor : σ → ℤ} {budget : ℝ} {power : ℕ}
    {stack : PhysicalEpochStack base} (h : UniformAt A M anchor budget power stack) :
    (stack.periods.prod : ℝ) ≤ Real.exp ((s : ℝ) * budget) := by
  revert h
  induction stack with
  | zero => intro h; simp [periods]
  | @succ t base frame tail ih =>
    intro h
    obtain ⟨_, _, _, _, _, hperiod, _, _, _, htail⟩ := h
    change ((frame.period * tail.periods.prod : ℕ) : ℝ) ≤ _
    rw [Nat.cast_mul]
    calc
      (frame.period : ℝ) * tail.periods.prod ≤ Real.exp budget * Real.exp ((t : ℝ) * budget) :=
        mul_le_mul hperiod (ih htail) (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (((t + 1 : ℕ) : ℝ) * budget) := by
        rw [← Real.exp_add]
        congr 1
        push_cast
        ring

theorem UniformAt.period_exclusions_card_le {A M : ℕ} {anchor : σ → ℤ} {budget logM : ℝ}
    {power : ℕ} {stack : PhysicalEpochStack base}
    (h : UniformAt A M anchor budget power stack) (hM : 0 < M) (hMb : (M : ℝ) ≤ Real.exp logM)
    {ι : Type*} [Fintype ι] (prime : ι → ℕ) (hprime : ∀ i, (prime i).Prime)
    (hinj : Function.Injective prime) :
    ((periodPrimeCoordinates prime (M * stack.periods.prod)).card : ℝ) ≤ 2 * (logM + (s : ℝ) * budget) := by
  apply periodPrimeCoordinates_card_le prime hprime hinj (Nat.mul_pos hM stack.periods_product_pos)
  rw [Nat.cast_mul, Real.exp_add]
  exact mul_le_mul hMb h.periods_product_le (Nat.cast_nonneg _) (Real.exp_nonneg _)

theorem pending_coprime_periods (stack : PhysicalEpochStack base) (M : ℕ)
    {ι : Type*} [Fintype ι] (prime power : ι → ℕ) (hprime : ∀ i, (prime i).Prime)
    (J : Finset ι) (hJ : Disjoint J (periodPrimeCoordinates prime (M * stack.periods.prod))) :
    ∀ P ∈ stack.periods, (M * (M * P)).Coprime (∏ i ∈ J, prime i ^ power i) := by
  have h := periodPrimeCoordinates_pending_coprime prime power hprime (M * stack.periods.prod) J hJ
  have hm := Nat.Coprime.of_dvd_right (dvd_mul_right M stack.periods.prod) h
  intro P hP
  have hp := Nat.Coprime.of_dvd_right
    ((stack.period_dvd_product hP).trans (dvd_mul_left stack.periods.prod M)) h
  exact (hm.mul_right (hm.mul_right hp)).symm

end Erdos3.PhysicalEpochStack

end

section

namespace Erdos3

universe u v

namespace PhysicalEpochStack

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {bound : ℕ}

inductive RecordEvent (m J : ℕ) : {s : ℕ} → {base : PhysicalEpochSource.{u, v} σ s bound} →
    PhysicalEpochStack base → Prop
  | head {s : ℕ} {base : PhysicalEpochSource.{u, v} σ (s + 1) bound}
      (frame : PhysicalEpochFrame base) (tail : PhysicalEpochStack frame.child)
      (state : PhysicalEpochRecords base)
      (record : ∃ r, state.records = r :: frame.state.records)
      (moduli : ∀ r ∈ state.records, r.modulus ∣ m * J)
      (drop : state.dimension < frame.state.dimension) : RecordEvent m J (.succ frame tail)
  | tail {s : ℕ} {base : PhysicalEpochSource.{u, v} σ (s + 1) bound}
      (frame : PhysicalEpochFrame base) {oldTail : PhysicalEpochStack frame.child}
      (event : RecordEvent m J oldTail) : RecordEvent m J (.succ frame oldTail)

end PhysicalEpochStack

open PhysicalEpochStack

theorem exists_physical_stack_record_descent (C : ℕ) :
    ∃ A Kf : ℕ, 1 ≤ A ∧ 2 ≤ Kf ∧
    ∀ {σ : Type u} [Fintype σ] [DecidableEq σ] {s bound m a J : ℕ} {gap U : ℝ}
      (selected : σ → ℤ) {base : PhysicalEpochSource.{u, v} σ s bound}
      (stack : PhysicalEpochStack base) (c : PhysicalEpochComparison base m a J gap),
    BudgetedAt A U C stack → AlignedAt m selected stack → c.Controlled →
    (∀ i, c.anchor i ≡ selected i [ZMOD (m : ℤ)]) →
    (m * a * stack.periods.prod).Coprime J →
    (∀ i, ((m * J : ℕ) : ℝ) * Real.exp (5 * U + 2 * (U + 2) ^ Kf + 16) ≤ (base.sides i : ℝ)) →
    RecordEvent m J stack := by
  obtain ⟨A, Kf, hA, hKf, hvisit⟩ := exists_uniform_controlled_frame_visit C
  refine ⟨A, Kf, hA, hKf, ?_⟩
  intro σ _ _ s bound m a J gap U selected base stack
  revert a gap
  induction stack with
  | zero base =>
    intro a gap c hbudget halign hc hanchor hcop hsource
    exact False.elim c.impossible_at_zero
  | @succ s base frame tail ih =>
    intro a gap c hbudget halign hc hanchor hcop hsource
    obtain ⟨hrecord, hinflate, hwork, hperiod, hfreeze, hevent, htail⟩ := hbudget
    obtain ⟨hmod, halign, htailAlign⟩ := halign
    have hchild : (frame.child.incomingBudget + 2) ^ A ≤ frame.child.recordBudget := by
      cases tail with
      | zero => exact htail.2
      | succ => exact htail.2.1
    have hframeAnchor : ∀ i, c.anchor i ≡ frame.anchor i [ZMOD (frame.modulus : ℤ)] := by
      intro i
      exact (Int.ModEq.of_dvd (by exact_mod_cast hmod) (hanchor i)).trans (halign i)
    have hleft : (m * a).Coprime J := Nat.Coprime.of_dvd_left (Nat.dvd_mul_right _ _) hcop
    have hperiodDiv : m * a * frame.period ∣ m * a * (PhysicalEpochStack.succ frame tail).periods.prod := by
      simpa only [periods, List.prod_cons, Nat.mul_assoc] using Nat.dvd_mul_right (m * a * frame.period) tail.periods.prod
    have hright : (m * a * frame.period).Coprime J := Nat.Coprime.of_dvd_left hperiodDiv hcop
    have hlocal : (m * a * (m * a * frame.period)).Coprime J := (hleft.symm.mul_right hright.symm).symm
    rcases hvisit frame c hc hrecord hinflate hchild hwork hperiod hfreeze hevent
        hmod hframeAnchor hlocal hsource with hrecordEvent | hnext
    · obtain ⟨state, hr, hm, hd⟩ := hrecordEvent
      exact .head frame tail state hr hm hd
    · obtain ⟨next, hnextControl, _, hnextAnchor, _⟩ := hnext
      have hanchor' : ∀ i, next.anchor i ≡ selected i [ZMOD (m : ℤ)] := by
        intro i
        exact (Int.ModEq.of_dvd (by exact_mod_cast Nat.dvd_mul_right m a) (hnextAnchor i)).trans (hanchor i)
      have hcop' : (m * (a * frame.period) * tail.periods.prod).Coprime J := by
        simpa only [periods, List.prod_cons, Nat.mul_assoc] using hcop
      have hsource' : ∀ i, ((m * J : ℕ) : ℝ) * Real.exp (5 * U + 2 * (U + 2) ^ Kf + 16) ≤
          (frame.child.sides i : ℝ) := by
        simpa only [frame.child_sides] using hsource
      exact .tail frame (ih next htail htailAlign hnextControl hanchor' hcop' hsource')

end Erdos3

end

section

namespace Erdos3

open PhysicalEpochStack

universe u v

theorem exists_scheduled_physical_epoch_stack (A C limit : ℕ) (hA : 1 ≤ A) (hC : 1 ≤ C)
    (hframes : ∀ t : ℕ, t ≤ limit → PhysicalFrameConstructionBound.{u, v} t C)
    (b : ℝ) (hb : 0 ≤ b) (s : ℕ) :
    s ≤ limit → ∀ depth : ℕ, ∀ {σ : Type u} [Fintype σ] [DecidableEq σ] {bound : ℕ}
      (base : PhysicalEpochSource.{u, v} σ s bound) (state : PhysicalEpochRecords base)
      (M : ℕ), 0 < M → ∀ anchor : σ → ℤ,
      (∀ i, base.lower i ≤ anchor i ∧ anchor i < base.lower i + base.sides i) →
      (∀ r ∈ state.records, r.modulus ∣ M) →
      base.recordBudget ≤ physicalEpochBudget A C b depth →
      (base.incomingBudget + 2) ^ A ≤ base.recordBudget →
      (∀ i, Real.exp (physicalEpochBudget A C b (depth + s)) ≤ (base.sides i : ℝ) / M) →
      ∃ stack : PhysicalEpochStack base, RootState state stack ∧ RootCreatedAt M anchor stack ∧
        AlignedAt M anchor stack ∧ ScheduledAt A C b depth stack := by
  induction s with
  | zero =>
    intro hs depth σ _ _ bound base state M hM anchor hanchor hmod hcap hinflate hlarge
    exact ⟨.zero base, trivial, trivial, trivial, hcap, hinflate⟩
  | succ s ih =>
    intro hs depth σ _ _ bound base state M hM anchor hanchor hmod hcap hinflate hlarge
    have hp : 0 ≤ base.recordBudget := base.incoming_nonneg.trans base.incoming_le_record
    have hbudget := physicalEpochBudget_nonneg A C hb depth
    have hpow : (base.recordBudget + 2) ^ C ≤ (physicalEpochBudget A C b depth + 2) ^ C :=
      pow_le_pow_left₀ (by linarith) (by linarith) C
    have hbound : (physicalEpochBudget A C b depth + 2) ^ C ≤
        physicalEpochBudget A C b (depth + (s + 1)) :=
      (physicalEpochBudget_work_le hA hb depth).trans (physicalEpochBudget_mono hA hC hb (by omega))
    have hinflation : ∀ x : ℝ, 0 ≤ x → x ≤ (x + 2) ^ A := by
      intro x hx
      calc
        x ≤ x + 2 := by linarith
        _ = (x + 2) ^ 1 := (pow_one _).symm
        _ ≤ (x + 2) ^ A := pow_le_pow_right₀ (by linarith) hA
    obtain ⟨frame, hstate, hmodulus, hframeAnchor, hwork, hchildIncoming, hchildRecord, hperiod, hfreeze, hevent⟩ :=
      hframes s (by omega) base state M hM anchor hanchor hmod (fun x => (x + 2) ^ A) hinflation
        (fun i => (Real.exp_le_exp.mpr (hpow.trans hbound)).trans (hlarge i))
    have hchildCap : frame.child.recordBudget ≤ physicalEpochBudget A C b (depth + 1) := by
      rw [hchildRecord]
      change (frame.child.incomingBudget + 2) ^ A ≤ ((physicalEpochBudget A C b depth + 2) ^ C + 2) ^ A
      have hx := frame.child.incoming_nonneg
      have hcost := hchildIncoming.trans hpow
      gcongr
    have hchildInflate : (frame.child.incomingBudget + 2) ^ A ≤ frame.child.recordBudget := le_of_eq hchildRecord.symm
    have hchildAnchor : ∀ i, frame.child.lower i ≤ anchor i ∧ anchor i < frame.child.lower i + frame.child.sides i := by
      simpa only [frame.child_lower, frame.child_sides] using hanchor
    have hidx : depth + 1 + s = depth + (s + 1) := by omega
    have hchildLarge : ∀ i, Real.exp (physicalEpochBudget A C b (depth + 1 + s)) ≤
        (frame.child.sides i : ℝ) / M := by
      simpa only [frame.child_sides, hidx] using hlarge
    obtain ⟨tail, _, _, htailAlign, htailSchedule⟩ :=
      ih (by omega) (depth + 1) frame.child (PhysicalEpochRecords.empty frame.child) M hM anchor hchildAnchor
        (by simp [PhysicalEpochRecords.empty]) hchildCap hchildInflate hchildLarge
    refine ⟨.succ frame tail, hstate, ⟨hmodulus, hframeAnchor⟩, ?_, ?_⟩
    · exact ⟨hmodulus ▸ dvd_refl M, fun i => hframeAnchor ▸ Int.ModEq.refl (frame.anchor i), htailAlign⟩
    · exact ⟨hcap, hinflate, hwork.trans hpow, hperiod.trans (Real.exp_le_exp.mpr hpow),
        hfreeze, hevent, htailSchedule⟩

end Erdos3

end

section

namespace Erdos3

open PhysicalEpochStack

universe u v

theorem PhysicalEpochStack.RecordEvent.rebuild
    {A C limit : ℕ} (hA : 1 ≤ A) (hC : 1 ≤ C)
    (hframes : ∀ t : ℕ, t ≤ limit → PhysicalFrameConstructionBound.{u, v} t C)
    {b : ℝ} (hb : 0 ≤ b)
    {σ : Type u} [Fintype σ] [DecidableEq σ] {s bound m J : ℕ}
    {base : PhysicalEpochSource.{u, v} σ s bound} {stack : PhysicalEpochStack base}
    {selected : σ → ℤ} (hm : 0 < m) (hJ : 0 < J) (event : RecordEvent m J stack) :
    ∀ depth : ℕ, s ≤ limit → ScheduledAt A C b depth stack → AlignedAt m selected stack →
    ∀ anchor : σ → ℤ,
    (∀ i, base.lower i ≤ anchor i ∧ anchor i < base.lower i + base.sides i) →
    (∀ i, anchor i ≡ selected i [ZMOD (m : ℤ)]) →
    (∀ i, Real.exp (physicalEpochBudget A C b (depth + s)) ≤ (base.sides i : ℝ) / (m * J : ℕ)) →
    ∃ next : PhysicalEpochStack base,
      Event stack next ∧ AlignedAt (m * J) anchor next ∧ ScheduledAt A C b depth next := by
  induction event with
  | @head s base frame tail state record moduli drop =>
    intro depth hs hschedule halign anchor hinside hcompat hlarge
    obtain ⟨next, hroot, hcreated, halignNext, hscheduleNext⟩ :=
      exists_scheduled_physical_epoch_stack A C limit hA hC (@hframes) b hb (s + 1)
        hs depth base state (m * J) (Nat.mul_pos hm hJ) anchor hinside moduli
        hschedule.record_le hschedule.inflation hlarge
    cases next with
    | succ newFrame newTail =>
      change newFrame.state = state at hroot
      change newFrame.modulus = m * J ∧ newFrame.anchor = anchor at hcreated
      obtain ⟨r, hr⟩ := record
      have hrecords : newFrame.state.records = r :: frame.state.records := by rw [hroot]; exact hr
      have hmodulus : frame.modulus ∣ newFrame.modulus := by
        rw [hcreated.1]
        exact halign.1.trans (Nat.dvd_mul_right m J)
      have hanchor : ∀ i, newFrame.anchor i ≡ frame.anchor i [ZMOD (frame.modulus : ℤ)] := by
        intro i
        rw [hcreated.2]
        exact (Int.ModEq.of_dvd (by exact_mod_cast halign.1) (hcompat i)).trans (halign.2.1 i)
      exact ⟨.succ newFrame newTail, .head r hrecords hmodulus hanchor tail newTail, halignNext, hscheduleNext⟩
  | @tail s base frame oldTail event ih =>
    intro depth hs hschedule halign anchor hinside hcompat hlarge
    obtain ⟨hr, hi, hw, hp, hf, he, htailSchedule⟩ := hschedule
    obtain ⟨hmframe, haframe, htailAlign⟩ := halign
    have hinsideChild : ∀ i, frame.child.lower i ≤ anchor i ∧ anchor i < frame.child.lower i + frame.child.sides i := by
      simpa only [frame.child_lower, frame.child_sides] using hinside
    have hidx : depth + 1 + s = depth + (s + 1) := by omega
    have hlargeChild : ∀ i, Real.exp (physicalEpochBudget A C b (depth + 1 + s)) ≤
        (frame.child.sides i : ℝ) / (m * J : ℕ) := by
      simpa only [frame.child_sides, hidx] using hlarge
    obtain ⟨newTail, htailEvent, htailAlignNext, htailScheduleNext⟩ :=
      ih (depth + 1) (by omega) htailSchedule htailAlign anchor hinsideChild hcompat hlargeChild
    refine ⟨.succ frame newTail, .tail frame htailEvent, ?_, ?_⟩
    · refine ⟨hmframe.trans (Nat.dvd_mul_right m J), ?_, htailAlignNext⟩
      intro i
      exact (Int.ModEq.of_dvd (by exact_mod_cast hmframe) (hcompat i)).trans (haframe i)
    · exact ⟨hr, hi, hw, hp, hf, he, htailScheduleNext⟩

end Erdos3

end

section

namespace Erdos3

open PhysicalEpochStack

universe u v

theorem exists_scheduled_physical_event_parameters (limit : ℕ) :
    ∃ C A Kf K : ℕ, 2 ≤ C ∧ 1 ≤ A ∧ 2 ≤ Kf ∧ 2 ≤ K ∧
    (∀ b : ℝ, 0 ≤ b → physicalEpochBudget A C b limit ≤ (b + 2) ^ K) ∧
    (∀ t : ℕ, t ≤ limit → PhysicalFrameConstructionBound.{u, v} t C) ∧
    ∀ {σ : Type u} [Fintype σ] [DecidableEq σ] {s bound m a J : ℕ} {gap : ℝ}
      (b : ℝ) (depth : ℕ) (selected : σ → ℤ)
      {base : PhysicalEpochSource.{u, v} σ s bound}
      (stack : PhysicalEpochStack base) (c : PhysicalEpochComparison base m a J gap),
    0 ≤ b → depth + s ≤ limit → ScheduledAt A C b depth stack → AlignedAt m selected stack →
    c.Controlled → (∀ i, c.anchor i ≡ selected i [ZMOD (m : ℤ)]) →
    (m * a * stack.periods.prod).Coprime J →
    (∀ i, ((m * J : ℕ) : ℝ) * Real.exp
      (5 * physicalEpochBudget A C b (depth + s) +
        2 * (physicalEpochBudget A C b (depth + s) + 2) ^ Kf + 16) ≤ (base.sides i : ℝ)) →
    ∀ anchor : σ → ℤ,
    (∀ i, base.lower i ≤ anchor i ∧ anchor i < base.lower i + base.sides i) →
    (∀ i, anchor i ≡ selected i [ZMOD (m : ℤ)]) →
    ∃ next : PhysicalEpochStack base,
      Event stack next ∧ AlignedAt (m * J) anchor next ∧ ScheduledAt A C b depth next := by
  obtain ⟨C, hC, hframes⟩ := exists_uniform_physical_frame_construction limit
  obtain ⟨A, Kf, hA, hKf, hdescent⟩ := exists_physical_stack_record_descent C
  obtain ⟨K, hK, hgrowth⟩ := exists_physicalEpochBudget_power A C limit
  refine ⟨C, A, Kf, K, hC, hA, hKf, hK, hgrowth, @hframes, ?_⟩
  intro σ _ _ s bound m a J gap b depth selected base stack c hb hs hschedule halign hc hanchor hcop hsource
    anchor hinside hcompat
  have hC1 : 1 ≤ C := by omega
  have hevent := hdescent selected stack c (hschedule.budgeted hA hC1 hb) halign hc hanchor hcop hsource
  let U := physicalEpochBudget A C b (depth + s)
  have hU : 0 ≤ U := physicalEpochBudget_nonneg A C hb (depth + s)
  have hNJ : (0 : ℝ) < ((m * J : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos c.selected_pos c.pending_pos
  have hpower : 0 ≤ (U + 2) ^ Kf := by positivity
  have hlarge : ∀ i, Real.exp U ≤ (base.sides i : ℝ) / (m * J : ℕ) := by
    intro i
    apply (le_div_iff₀ hNJ).mpr
    calc
      Real.exp U * ((m * J : ℕ) : ℝ) ≤
          Real.exp (5 * U + 2 * (U + 2) ^ Kf + 16) * ((m * J : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) hNJ.le
      _ = ((m * J : ℕ) : ℝ) * Real.exp (5 * U + 2 * (U + 2) ^ Kf + 16) := mul_comm _ _
      _ ≤ (base.sides i : ℝ) := hsource i
  exact PhysicalEpochStack.RecordEvent.rebuild hA hC1 (@hframes) hb
    c.selected_pos c.pending_pos hevent depth (by omega) hschedule halign anchor hinside hcompat hlarge

end Erdos3

end

section

namespace Erdos3

open PhysicalEpochStack

universe u v

structure PhysicalStabilityParameters (limit : ℕ) where
  C : ℕ
  A : ℕ
  Kf : ℕ
  K : ℕ
  C_ge_two : 2 ≤ C
  A_pos : 1 ≤ A
  Kf_ge_two : 2 ≤ Kf
  K_ge_two : 2 ≤ K
  growth : ∀ b : ℝ, 0 ≤ b → physicalEpochBudget A C b limit ≤ (b + 2) ^ K
  frames : ∀ t : ℕ, t ≤ limit → PhysicalFrameConstructionBound.{u, v} t C
  event :
    ∀ {σ : Type u} [Fintype σ] [DecidableEq σ] {s bound m a J : ℕ} {gap : ℝ}
      (b : ℝ) (depth : ℕ) (selected : σ → ℤ)
      {base : PhysicalEpochSource.{u, v} σ s bound}
      (stack : PhysicalEpochStack base) (c : PhysicalEpochComparison base m a J gap),
    0 ≤ b → depth + s ≤ limit → ScheduledAt A C b depth stack → AlignedAt m selected stack →
    c.Controlled → (∀ i, c.anchor i ≡ selected i [ZMOD (m : ℤ)]) →
    (m * a * stack.periods.prod).Coprime J →
    (∀ i, ((m * J : ℕ) : ℝ) * Real.exp
      (5 * physicalEpochBudget A C b (depth + s) +
        2 * (physicalEpochBudget A C b (depth + s) + 2) ^ Kf + 16) ≤ (base.sides i : ℝ)) →
    ∀ anchor : σ → ℤ,
    (∀ i, base.lower i ≤ anchor i ∧ anchor i < base.lower i + base.sides i) →
    (∀ i, anchor i ≡ selected i [ZMOD (m : ℤ)]) →
    ∃ next : PhysicalEpochStack base,
      Event stack next ∧ AlignedAt (m * J) anchor next ∧ ScheduledAt A C b depth next

theorem exists_physical_stability_parameters (limit : ℕ) :
    Nonempty (PhysicalStabilityParameters.{u, v} limit) := by
  obtain ⟨C, A, Kf, K, hC, hA, hKf, hK, hgrowth, hframes, hevent⟩ :=
    exists_scheduled_physical_event_parameters limit
  exact ⟨⟨C, A, Kf, K, hC, hA, hKf, hK, hgrowth, @hframes, @hevent⟩⟩

end Erdos3

end

end OAI
