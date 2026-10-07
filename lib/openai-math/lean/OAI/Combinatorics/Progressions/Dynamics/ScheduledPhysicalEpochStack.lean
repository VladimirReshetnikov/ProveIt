import OAI.Combinatorics.Progressions.Linear.UniformPhysicalFrameConstruction

namespace OAI

section

namespace Erdos3

def physicalEpochBudget (A C : ℕ) (b : ℝ) : ℕ → ℝ
  | 0 => b
  | k + 1 => ((physicalEpochBudget A C b k + 2) ^ C + 2) ^ A

theorem physicalEpochBudget_nonneg (A C : ℕ) {b : ℝ} (hb : 0 ≤ b) (k : ℕ) :
    0 ≤ physicalEpochBudget A C b k := by
  induction k with
  | zero => exact hb
  | succ k ih => simp only [physicalEpochBudget]; positivity

theorem physicalEpochBudget_work_le {A C : ℕ} (hA : 1 ≤ A) {b : ℝ} (hb : 0 ≤ b) (k : ℕ) :
    (physicalEpochBudget A C b k + 2) ^ C ≤ physicalEpochBudget A C b (k + 1) := by
  have hx := physicalEpochBudget_nonneg A C hb k
  have hp : 0 ≤ (physicalEpochBudget A C b k + 2) ^ C := by positivity
  change (physicalEpochBudget A C b k + 2) ^ C ≤ ((physicalEpochBudget A C b k + 2) ^ C + 2) ^ A
  calc
    (physicalEpochBudget A C b k + 2) ^ C ≤ (physicalEpochBudget A C b k + 2) ^ C + 2 := by linarith
    _ = ((physicalEpochBudget A C b k + 2) ^ C + 2) ^ 1 := (pow_one _).symm
    _ ≤ ((physicalEpochBudget A C b k + 2) ^ C + 2) ^ A := pow_le_pow_right₀ (by linarith) hA

theorem physicalEpochBudget_mono {A C : ℕ} (hA : 1 ≤ A) (hC : 1 ≤ C) {b : ℝ} (hb : 0 ≤ b) :
    Monotone (physicalEpochBudget A C b) := by
  apply monotone_nat_of_le_succ
  intro k
  have hx := physicalEpochBudget_nonneg A C hb k
  calc
    physicalEpochBudget A C b k ≤ physicalEpochBudget A C b k + 2 := by linarith
    _ = (physicalEpochBudget A C b k + 2) ^ 1 := (pow_one _).symm
    _ ≤ (physicalEpochBudget A C b k + 2) ^ C := pow_le_pow_right₀ (by linarith) hC
    _ ≤ physicalEpochBudget A C b (k + 1) := physicalEpochBudget_work_le hA hb k

theorem exists_physicalEpochBudget_power (A C s : ℕ) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ b : ℝ, 0 ≤ b → physicalEpochBudget A C b s ≤ (b + 2) ^ K := by
  induction s with
  | zero =>
    refine ⟨2, by omega, ?_⟩
    intro b hb
    simp only [physicalEpochBudget]
    nlinarith
  | succ s ih =>
    obtain ⟨K, _, hK⟩ := ih
    let P : Polynomial ℕ := (((Polynomial.X + 2) ^ K + 2) ^ C + 2) ^ A
    obtain ⟨L, hL, hP⟩ := exists_natPolynomial_fixed_power_budget P
    refine ⟨L, hL, ?_⟩
    intro b hb
    have hx := physicalEpochBudget_nonneg A C hb s
    calc
      physicalEpochBudget A C b (s + 1) ≤ (((b + 2) ^ K + 2) ^ C + 2) ^ A := by
        simp only [physicalEpochBudget]
        gcongr
        exact hK b hb
      _ ≤ (b + 2) ^ L := by simpa [P, Polynomial.eval₂_pow] using hP b hb

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

universe u v

inductive PhysicalEpochStack {σ : Type u} [Fintype σ] [DecidableEq σ] {bound : ℕ} :
    {s : ℕ} → PhysicalEpochSource.{u, v} σ s bound → Type (max u (v + 1))
  | zero (base : PhysicalEpochSource.{u, v} σ 0 bound) : PhysicalEpochStack base
  | succ {s : ℕ} {base : PhysicalEpochSource.{u, v} σ (s + 1) bound}
      (frame : PhysicalEpochFrame base) (tail : PhysicalEpochStack frame.child) : PhysicalEpochStack base

namespace PhysicalEpochStack

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {bound s : ℕ}
  {base : PhysicalEpochSource.{u, v} σ s bound}

noncomputable def dimensions : {s : ℕ} → {base : PhysicalEpochSource.{u, v} σ s bound} →
    PhysicalEpochStack base → List ℕ
  | _, _, .zero _ => []
  | _, _, .succ frame tail => frame.state.dimension :: dimensions tail

theorem dimensions_length (stack : PhysicalEpochStack base) : stack.dimensions.length = s := by
  induction stack with
  | zero => rfl
  | succ frame tail ih => simp only [dimensions, List.length_cons, ih]

theorem dimensions_bounded (stack : PhysicalEpochStack base) :
    ∀ q ∈ stack.dimensions, q ≤ bound := by
  induction stack with
  | zero => simp [dimensions]
  | succ frame tail ih =>
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact frame.state.dimension_le
    · exact ih q hq

inductive Event : {s : ℕ} → {base : PhysicalEpochSource.{u, v} σ s bound} →
    PhysicalEpochStack base → PhysicalEpochStack base → Prop
  | head {s : ℕ} {base : PhysicalEpochSource.{u, v} σ (s + 1) bound}
      {oldFrame newFrame : PhysicalEpochFrame base}
      (record : EpochSymbolRecord base.model base.weights base.adapted base.fixedMap)
      (records : newFrame.state.records = record :: oldFrame.state.records)
      (modulus : oldFrame.modulus ∣ newFrame.modulus)
      (anchor : ∀ i, newFrame.anchor i ≡ oldFrame.anchor i [ZMOD (oldFrame.modulus : ℤ)])
      (oldTail : PhysicalEpochStack oldFrame.child) (newTail : PhysicalEpochStack newFrame.child) :
      Event (.succ oldFrame oldTail) (.succ newFrame newTail)
  | tail {s : ℕ} {base : PhysicalEpochSource.{u, v} σ (s + 1) bound}
      (frame : PhysicalEpochFrame base)
      {oldTail newTail : PhysicalEpochStack frame.child} (event : Event oldTail newTail) :
      Event (.succ frame oldTail) (.succ frame newTail)

theorem Event.to_dimension_event {oldStack newStack : PhysicalEpochStack base}
    (event : Event oldStack newStack) :
    EpochStackEvent bound oldStack.dimensions newStack.dimensions := by
  induction event with
  | @head s base oldFrame newFrame record records modulus anchor oldTail newTail =>
    have hhistory := newFrame.state.history
    rw [records] at hhistory
    have hdrop : newFrame.state.dimension < oldFrame.state.dimension := by
      cases hhistory with
      | cons history drop =>
        change finrank ℚ (epochRecordIntersection newFrame.state.records) < _
        rw [records]
        change finrank ℚ ↥(record.fast ⊓ epochRecordIntersection oldFrame.state.records) < _
        rw [inf_comm record.fast]
        exact drop
    exact EpochStackEvent.head hdrop
      (newTail.dimensions_length.trans oldTail.dimensions_length.symm) newTail.dimensions_bounded
  | tail frame event ih => exact EpochStackEvent.tail ih

theorem Event.rank_lt {oldStack newStack : PhysicalEpochStack base}
    (event : Event oldStack newStack) :
    epochStackRank bound newStack.dimensions < epochStackRank bound oldStack.dimensions :=
  event.to_dimension_event.rank_lt

theorem event_chain_bound (n : ℕ) (states : ℕ → PhysicalEpochStack base)
    (events : ∀ i, i < n → Event (states i) (states (i + 1))) :
    n ≤ (bound + 1) ^ s - 1 := by
  have h := epochEventChain_bound bound n (fun i => (states i).dimensions)
    (states 0).dimensions_bounded (fun i hi => (events i hi).to_dimension_event)
  simpa only [dimensions_length] using h

end PhysicalEpochStack

end Erdos3

end

section

namespace Erdos3.PhysicalEpochStack

universe u v

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {bound s : ℕ}
  {base : PhysicalEpochSource.{u, v} σ s bound}

def RootState (state : PhysicalEpochRecords base) : PhysicalEpochStack base → Prop
  | .zero _ => True
  | .succ frame _ => frame.state = state

def UniformAt (A M : ℕ) (anchor : σ → ℤ) (budget : ℝ) (power : ℕ) :
    {s : ℕ} → {base : PhysicalEpochSource.{u, v} σ s bound} → PhysicalEpochStack base → Prop
  | _, base, .zero _ => base.incomingBudget ≤ budget ∧ base.recordBudget ≤ budget
  | _, base, .succ frame tail =>
    base.incomingBudget ≤ budget ∧ base.recordBudget ≤ budget ∧
    frame.modulus = M ∧ frame.anchor = anchor ∧ frame.work ≤ budget ∧
    (frame.period : ℝ) ≤ Real.exp budget ∧ frame.freezePower ≤ power ∧ frame.eventPower ≤ power ∧
    frame.child.recordBudget = (frame.child.incomingBudget + 2) ^ A ∧
    UniformAt A M anchor budget power tail

theorem UniformAt.mono {A M : ℕ} {anchor : σ → ℤ} {budget budget' : ℝ} {power power' : ℕ}
    {stack : PhysicalEpochStack base} (h : UniformAt A M anchor budget power stack)
    (hbudget : budget ≤ budget') (hpower : power ≤ power') :
    UniformAt A M anchor budget' power' stack := by
  induction stack with
  | zero base => exact ⟨h.1.trans hbudget, h.2.trans hbudget⟩
  | succ frame tail ih =>
    obtain ⟨hincoming, hrecord, hmod, hanchor, hwork, hperiod, hfreeze, hevent, hinflate, htail⟩ := h
    exact ⟨hincoming.trans hbudget, hrecord.trans hbudget, hmod, hanchor, hwork.trans hbudget,
      hperiod.trans (Real.exp_le_exp.mpr hbudget), hfreeze.trans hpower, hevent.trans hpower,
      hinflate, ih htail⟩

end Erdos3.PhysicalEpochStack

end

section

namespace Erdos3.PhysicalEpochStack

universe u v

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {bound s : ℕ}
  {base : PhysicalEpochSource.{u, v} σ s bound}

def AlignedAt (M : ℕ) (anchor : σ → ℤ) :
    {s : ℕ} → {base : PhysicalEpochSource.{u, v} σ s bound} → PhysicalEpochStack base → Prop
  | _, _, .zero _ => True
  | _, _, .succ frame tail =>
    frame.modulus ∣ M ∧
    (∀ i, anchor i ≡ frame.anchor i [ZMOD (frame.modulus : ℤ)]) ∧ AlignedAt M anchor tail

def BudgetedAt (A : ℕ) (budget : ℝ) (power : ℕ) :
    {s : ℕ} → {base : PhysicalEpochSource.{u, v} σ s bound} → PhysicalEpochStack base → Prop
  | _, base, .zero _ => base.recordBudget ≤ budget ∧ (base.incomingBudget + 2) ^ A ≤ base.recordBudget
  | _, base, .succ frame tail =>
    base.recordBudget ≤ budget ∧ (base.incomingBudget + 2) ^ A ≤ base.recordBudget ∧
    frame.work ≤ budget ∧ (frame.period : ℝ) ≤ Real.exp budget ∧
    frame.freezePower ≤ power ∧ frame.eventPower ≤ power ∧ BudgetedAt A budget power tail

theorem UniformAt.aligned {A M : ℕ} {anchor : σ → ℤ} {budget : ℝ} {power : ℕ}
    {stack : PhysicalEpochStack base} (h : UniformAt A M anchor budget power stack) :
    AlignedAt M anchor stack := by
  induction stack with
  | zero => trivial
  | succ frame tail ih =>
    obtain ⟨_, _, hmod, ha, _, _, _, _, _, ht⟩ := h
    exact ⟨hmod ▸ dvd_refl M, fun i => ha ▸ Int.ModEq.refl (frame.anchor i), ih ht⟩

theorem UniformAt.budgeted {A M : ℕ} {anchor : σ → ℤ} {budget : ℝ} {power : ℕ}
    {stack : PhysicalEpochStack base} (h : UniformAt A M anchor budget power stack)
    (hinflate : (base.incomingBudget + 2) ^ A ≤ base.recordBudget) : BudgetedAt A budget power stack := by
  induction stack with
  | zero => exact ⟨h.2, hinflate⟩
  | succ frame tail ih =>
    obtain ⟨_, hr, _, _, hw, hp, hf, he, hi, ht⟩ := h
    exact ⟨hr, hinflate, hw, hp, hf, he, ih ht (le_of_eq hi.symm)⟩

theorem AlignedAt.refine {M N : ℕ} {anchor refined : σ → ℤ}
    {stack : PhysicalEpochStack base} (h : AlignedAt M anchor stack)
    (hMN : M ∣ N) (hanchor : ∀ i, refined i ≡ anchor i [ZMOD (M : ℤ)]) :
    AlignedAt N refined stack := by
  induction stack with
  | zero => trivial
  | succ frame tail ih =>
    obtain ⟨hm, ha, ht⟩ := h
    refine ⟨hm.trans hMN, ?_, ih ht⟩
    intro i
    exact (Int.ModEq.of_dvd (by exact_mod_cast hm) (hanchor i)).trans (ha i)

theorem BudgetedAt.mono {A : ℕ} {budget budget' : ℝ} {power power' : ℕ}
    {stack : PhysicalEpochStack base} (h : BudgetedAt A budget power stack)
    (hb : budget ≤ budget') (hp : power ≤ power') : BudgetedAt A budget' power' stack := by
  induction stack with
  | zero => exact ⟨h.1.trans hb, h.2⟩
  | succ frame tail ih =>
    obtain ⟨hr, hi, hw, hperiod, hf, he, ht⟩ := h
    exact ⟨hr.trans hb, hi, hw.trans hb, hperiod.trans (Real.exp_le_exp.mpr hb),
      hf.trans hp, he.trans hp, ih ht⟩

end Erdos3.PhysicalEpochStack

end

section

namespace Erdos3.PhysicalEpochStack

universe u v

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {bound s : ℕ}
  {base : PhysicalEpochSource.{u, v} σ s bound}

def RootCreatedAt (M : ℕ) (anchor : σ → ℤ) : PhysicalEpochStack base → Prop
  | .zero _ => True
  | .succ frame _ => frame.modulus = M ∧ frame.anchor = anchor

def ScheduledAt (A C : ℕ) (b : ℝ) (depth : ℕ) :
    {s : ℕ} → {base : PhysicalEpochSource.{u, v} σ s bound} → PhysicalEpochStack base → Prop
  | _, base, .zero _ =>
    base.recordBudget ≤ physicalEpochBudget A C b depth ∧
    (base.incomingBudget + 2) ^ A ≤ base.recordBudget
  | _, base, .succ frame tail =>
    base.recordBudget ≤ physicalEpochBudget A C b depth ∧
    (base.incomingBudget + 2) ^ A ≤ base.recordBudget ∧
    frame.work ≤ (physicalEpochBudget A C b depth + 2) ^ C ∧
    (frame.period : ℝ) ≤ Real.exp ((physicalEpochBudget A C b depth + 2) ^ C) ∧
    frame.freezePower ≤ C ∧ frame.eventPower ≤ C ∧ ScheduledAt A C b (depth + 1) tail

theorem ScheduledAt.record_le {A C depth : ℕ} {b : ℝ} {stack : PhysicalEpochStack base}
    (h : ScheduledAt A C b depth stack) : base.recordBudget ≤ physicalEpochBudget A C b depth := by
  cases stack <;> exact h.1

theorem ScheduledAt.inflation {A C depth : ℕ} {b : ℝ} {stack : PhysicalEpochStack base}
    (h : ScheduledAt A C b depth stack) : (base.incomingBudget + 2) ^ A ≤ base.recordBudget := by
  cases stack with
  | zero => exact h.2
  | succ => exact h.2.1

theorem ScheduledAt.budgeted {A C depth : ℕ} {b : ℝ} {stack : PhysicalEpochStack base}
    (h : ScheduledAt A C b depth stack) (hA : 1 ≤ A) (hC : 1 ≤ C) (hb : 0 ≤ b) :
    BudgetedAt A (physicalEpochBudget A C b (depth + s)) C stack := by
  induction stack generalizing depth with
  | zero => exact h
  | @succ s base frame tail ih =>
    obtain ⟨hr, hi, hw, hp, hf, he, ht⟩ := h
    have hmono := physicalEpochBudget_mono hA hC hb
    have hroot : physicalEpochBudget A C b depth ≤ physicalEpochBudget A C b (depth + (s + 1)) :=
      hmono (by omega)
    have hwork : (physicalEpochBudget A C b depth + 2) ^ C ≤
        physicalEpochBudget A C b (depth + (s + 1)) :=
      (physicalEpochBudget_work_le hA hb depth).trans (hmono (by omega))
    refine ⟨hr.trans hroot, hi, hw.trans hwork, hp.trans (Real.exp_le_exp.mpr hwork), hf, he, ?_⟩
    have hidx : depth + 1 + s = depth + (s + 1) := by omega
    simpa only [hidx] using ih ht

end Erdos3.PhysicalEpochStack

end

end OAI
