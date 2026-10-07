/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Dynamics.BudgetedPhysicalStackPeriods
import OAI.Combinatorics.Progressions.Geometry.CoordinateTreeBatch
import OAI.Combinatorics.Progressions.Lattices.AffineSampleAlphabet

namespace OAI

section

namespace Erdos3

open PhysicalEpochStack
open scoped BigOperators

universe u v w

structure PrimeStabilityContext (ι : Type w) (σ : Type u) [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (s bound : ℕ) where
  parameters : PhysicalStabilityParameters.{u, v} s
  base : PhysicalEpochSource.{u, v} σ s bound
  baseline : base.model.Niltest (fun _ : σ => 1)
  orbit : baseline.orbit = base.fixedMap.orbit
  positive : baseline.UnitIntervalValued
  complexity : baseline.ComplexityLE base.incomingBudget
  recordCap : ℝ
  recordCap_nonneg : 0 ≤ recordCap
  record_le_cap : base.recordBudget ≤ recordCap
  inflation : (base.incomingBudget + 2) ^ parameters.A ≤ base.recordBudget
  record_two : 2 ≤ base.recordBudget
  gap : ℝ
  gap_pos : 0 < gap
  gap_le_one : gap ≤ 1
  gap_inverse : gap⁻¹ ≤ Real.exp base.incomingBudget
  prime : ι → ℕ
  power : ι → ℕ
  prime_prime : ∀ i, (prime i).Prime
  prime_injective : Function.Injective prime
  primeBudget : ℝ
  primeBudget_nonneg : 0 ≤ primeBudget
  prime_bound : ∀ i, ((prime i ^ power i : ℕ) : ℝ) ≤ Real.exp primeBudget
  witnessSize : ℕ
  mandatory : Finset ι

namespace PrimeStabilityContext

variable {ι : Type w} {σ : Type u} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  {s bound : ℕ}

def moduli (ctx : PrimeStabilityContext.{u, v, w} ι σ s bound) (i : ι) : ℕ :=
  ctx.prime i ^ ctx.power i

def workBudget (ctx : PrimeStabilityContext.{u, v, w} ι σ s bound) : ℝ :=
  physicalEpochBudget ctx.parameters.A ctx.parameters.C ctx.recordCap s

noncomputable def periodCap (ctx : PrimeStabilityContext.{u, v, w} ι σ s bound) : ℕ :=
  ⌈2 * ((s : ℝ) * ctx.workBudget)⌉₊

noncomputable def stepCost (ctx : PrimeStabilityContext.{u, v, w} ι σ s bound) : ℕ :=
  ctx.periodCap + ctx.witnessSize

noncomputable def allowance (ctx : PrimeStabilityContext.{u, v, w} ι σ s bound) : ℕ :=
  ctx.mandatory.card + ctx.stepCost * (bound + 1) ^ s

noncomputable def HasLargeSides (ctx : PrimeStabilityContext.{u, v, w} ι σ s bound) : Prop :=
  ∀ i, Real.exp (ctx.primeBudget * ctx.allowance + 5 * ctx.workBudget +
    2 * (ctx.workBudget + 2) ^ ctx.parameters.Kf + 16) ≤ (ctx.base.sides i : ℝ)

noncomputable def Good (ctx : PrimeStabilityContext.{u, v, w} ι σ s bound)
    (I : Finset ι) (x : ∀ i, σ → ZMod (ctx.moduli i)) : Prop :=
  PrimeCoordinateStable ctx.baseline.eval ctx.base.lower ctx.base.sides ctx.moduli ctx.witnessSize ctx.gap I x

structure State (ctx : PrimeStabilityContext.{u, v, w} ι σ s bound)
    (I : Finset ι) (x : ∀ i, σ → ZMod (ctx.moduli i)) where
  anchor : σ → ℤ
  anchor_mem : anchor ∈ primeCoordinateCell ctx.base.lower ctx.base.sides ctx.moduli I x
  stack : PhysicalEpochStack ctx.base
  scheduled : ScheduledAt ctx.parameters.A ctx.parameters.C ctx.recordCap 0 stack
  aligned : AlignedAt (∏ i ∈ I, ctx.moduli i) anchor stack
  room : I.card + ctx.stepCost * (epochStackRank bound stack.dimensions + 1) ≤ ctx.allowance

noncomputable def State.rank {ctx : PrimeStabilityContext.{u, v, w} ι σ s bound}
    {I : Finset ι} {x : ∀ i, σ → ZMod (ctx.moduli i)} (state : ctx.State I x) : ℕ :=
  epochStackRank bound state.stack.dimensions

theorem moduli_pos (ctx : PrimeStabilityContext.{u, v, w} ι σ s bound) (i : ι) : 0 < ctx.moduli i :=
  pow_pos (ctx.prime_prime i).pos _

theorem moduli_coprime (ctx : PrimeStabilityContext.{u, v, w} ι σ s bound) :
    Pairwise (fun i j => (ctx.moduli i).Coprime (ctx.moduli j)) :=
  selectedPrimePowers_pairwise_coprime ctx.prime ctx.power ctx.prime_prime ctx.prime_injective

theorem workBudget_nonneg (ctx : PrimeStabilityContext.{u, v, w} ι σ s bound) : 0 ≤ ctx.workBudget :=
  physicalEpochBudget_nonneg ctx.parameters.A ctx.parameters.C ctx.recordCap_nonneg s

end PrimeStabilityContext

end Erdos3

end

section

namespace Erdos3.PrimeStabilityContext

open PhysicalEpochStack
open scoped BigOperators

universe u v w

variable {ι : Type w} {σ : Type u} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  {s bound : ℕ}

theorem product_pos (ctx : PrimeStabilityContext.{u, v, w} ι σ s bound) (I : Finset ι) :
    0 < ∏ i ∈ I, ctx.moduli i := Finset.prod_pos (fun i _ => ctx.moduli_pos i)

theorem product_le_exp_card (ctx : PrimeStabilityContext.{u, v, w} ι σ s bound) (I : Finset ι) :
    ((∏ i ∈ I, ctx.moduli i : ℕ) : ℝ) ≤ Real.exp (ctx.primeBudget * I.card) := by
  rw [Nat.cast_prod]
  calc
    (∏ i ∈ I, (ctx.moduli i : ℝ)) ≤ ∏ _i ∈ I, Real.exp ctx.primeBudget :=
      Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun i _ => ctx.prime_bound i)
    _ = Real.exp ((I.card : ℝ) * ctx.primeBudget) := by rw [Finset.prod_const, Real.exp_nat_mul]
    _ = Real.exp (ctx.primeBudget * I.card) := by rw [mul_comm]

theorem node_width (ctx : PrimeStabilityContext.{u, v, w} ι σ s bound) (hlarge : ctx.HasLargeSides)
    (I : Finset ι) (hcard : I.card ≤ ctx.allowance) (j : σ) :
    ((∏ i ∈ I, ctx.moduli i : ℕ) : ℝ) *
      Real.exp (5 * ctx.workBudget + 2 * (ctx.workBudget + 2) ^ ctx.parameters.Kf + 16) ≤ (ctx.base.sides j : ℝ) := by
  have hcardR : (I.card : ℝ) ≤ ctx.allowance := by exact_mod_cast hcard
  have hprod : ((∏ i ∈ I, ctx.moduli i : ℕ) : ℝ) ≤ Real.exp (ctx.primeBudget * ctx.allowance) :=
    (ctx.product_le_exp_card I).trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hcardR ctx.primeBudget_nonneg))
  calc
    _ ≤ Real.exp (ctx.primeBudget * ctx.allowance) *
        Real.exp (5 * ctx.workBudget + 2 * (ctx.workBudget + 2) ^ ctx.parameters.Kf + 16) :=
      mul_le_mul_of_nonneg_right hprod (Real.exp_nonneg _)
    _ = Real.exp (ctx.primeBudget * ctx.allowance + 5 * ctx.workBudget +
        2 * (ctx.workBudget + 2) ^ ctx.parameters.Kf + 16) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ (ctx.base.sides j : ℝ) := hlarge j

theorem construction_width (ctx : PrimeStabilityContext.{u, v, w} ι σ s bound) (hlarge : ctx.HasLargeSides)
    (I : Finset ι) (hcard : I.card ≤ ctx.allowance) (j : σ) :
    Real.exp ctx.workBudget ≤ (ctx.base.sides j : ℝ) / (∏ i ∈ I, ctx.moduli i : ℕ) := by
  have hp : (0 : ℝ) < ((∏ i ∈ I, ctx.moduli i : ℕ) : ℝ) := by exact_mod_cast ctx.product_pos I
  have hU := ctx.workBudget_nonneg
  have hpow : 0 ≤ (ctx.workBudget + 2) ^ ctx.parameters.Kf := by positivity
  apply (le_div_iff₀ hp).mpr
  calc
    _ = ((∏ i ∈ I, ctx.moduli i : ℕ) : ℝ) * Real.exp ctx.workBudget := mul_comm _ _
    _ ≤ ((∏ i ∈ I, ctx.moduli i : ℕ) : ℝ) *
        Real.exp (5 * ctx.workBudget + 2 * (ctx.workBudget + 2) ^ ctx.parameters.Kf + 16) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hp.le
    _ ≤ (ctx.base.sides j : ℝ) := ctx.node_width hlarge I hcard j

variable {ctx : PrimeStabilityContext.{u, v, w} ι σ s bound}
  {I : Finset ι} {x : ∀ i, σ → ZMod (ctx.moduli i)}

noncomputable def State.periodBatch (state : ctx.State I x) : Finset ι :=
  periodPrimeCoordinates ctx.prime state.stack.periods.prod \ I

theorem State.periodBatch_disjoint (state : ctx.State I x) : Disjoint I state.periodBatch := by
  apply Finset.disjoint_left.mpr
  intro i hi hp
  exact (Finset.mem_sdiff.mp hp).2 hi

theorem State.periodBatch_card (state : ctx.State I x) : state.periodBatch.card ≤ ctx.periodCap := by
  have hb : BudgetedAt ctx.parameters.A ctx.workBudget ctx.parameters.C state.stack := by
    simpa only [Nat.zero_add, workBudget] using
      state.scheduled.budgeted ctx.parameters.A_pos (by linarith [ctx.parameters.C_ge_two]) ctx.recordCap_nonneg
  have hcard := hb.new_period_exclusions_card_le ctx.prime ctx.prime_prime ctx.prime_injective I
  have hceil : 2 * ((s : ℝ) * ctx.workBudget) ≤ (ctx.periodCap : ℝ) := Nat.le_ceil _
  exact_mod_cast hcard.trans hceil

theorem State.periods_covered (state : ctx.State I x) :
    periodPrimeCoordinates ctx.prime state.stack.periods.prod ⊆ I ∪ state.periodBatch := by
  intro i hi
  by_cases hI : i ∈ I
  · exact Finset.mem_union_left _ hI
  · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hi, hI⟩)

theorem State.one_step_room (state : ctx.State I x) : I.card + ctx.stepCost ≤ ctx.allowance := by
  have hmul : ctx.stepCost ≤ ctx.stepCost * (state.rank + 1) := by
    have h := Nat.mul_le_mul_left ctx.stepCost (show 1 ≤ state.rank + 1 by omega)
    simpa only [Nat.mul_one] using h
  have hroom : I.card + ctx.stepCost * (state.rank + 1) ≤ ctx.allowance := state.room
  omega

theorem State.room_of_smaller_rank (state : ctx.State I x) (J : Finset ι) (rank : ℕ)
    (hcard : J.card ≤ I.card + ctx.stepCost) (hrank : rank < state.rank) :
    J.card + ctx.stepCost * (rank + 1) ≤ ctx.allowance := by
  have hmul := Nat.mul_le_mul_left ctx.stepCost (Nat.succ_le_of_lt hrank)
  have hroom : I.card + ctx.stepCost * (state.rank + 1) ≤ ctx.allowance := state.room
  nlinarith

theorem State.aligned_refinement (state : ctx.State I x) {J : Finset ι}
    {y : ∀ i, σ → ZMod (ctx.moduli i)} (hIJ : I ⊆ J) (hxy : ∀ i ∈ I, y i = x i)
    (u : σ → ℤ) (hu : u ∈ primeCoordinateCell ctx.base.lower ctx.base.sides ctx.moduli J y) :
    AlignedAt (∏ i ∈ J, ctx.moduli i) u state.stack := by
  apply state.aligned.refine (Finset.prod_dvd_prod_of_subset I J ctx.moduli hIJ)
  have hmem := primeCoordinateCell_mono ctx.base.lower ctx.base.sides ctx.moduli hIJ hxy hu
  rw [primeCoordinateCell_anchor ctx.base.lower ctx.base.sides ctx.moduli I x state.anchor state.anchor_mem] at hmem
  exact ((mem_primeCoordinateCell_anchor ctx.base.lower ctx.base.sides ctx.moduli ctx.moduli_coprime I state.anchor u).mp hmem).2

end Erdos3.PrimeStabilityContext

end

section

namespace Erdos3.PrimeStabilityContext

open PhysicalEpochStack
open scoped BigOperators

universe u v w

variable {ι : Type w} {σ : Type u} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  {s bound : ℕ} {ctx : PrimeStabilityContext.{u, v, w} ι σ s bound}
  {I : Finset ι} {x : ∀ i, σ → ZMod (ctx.moduli i)}

theorem State.repair_cell (state : ctx.State I x) (hlarge : ctx.HasLargeSides)
    (L J : Finset ι) (hIL : I ⊆ L) (hLJ : Disjoint L J)
    (hperiods : periodPrimeCoordinates ctx.prime state.stack.periods.prod ⊆ L)
    (hcard : (L ∪ J).card ≤ I.card + ctx.stepCost)
    (y z : ∀ i, σ → ZMod (ctx.moduli i))
    (hy : ∀ i ∈ I, y i = x i) (hz : ∀ i ∈ L, z i = y i)
    (u v : σ → ℤ)
    (hu : u ∈ primeCoordinateCell ctx.base.lower ctx.base.sides ctx.moduli L y)
    (hv : v ∈ primeCoordinateCell ctx.base.lower ctx.base.sides ctx.moduli (L ∪ J) z)
    (hgap : ctx.gap ≤ ‖primeCoordinateMean ctx.baseline.eval ctx.base.lower ctx.base.sides ctx.moduli L y -
      primeCoordinateMean ctx.baseline.eval ctx.base.lower ctx.base.sides ctx.moduli (L ∪ J) z‖)
    (target : ∀ i, σ → ZMod (ctx.moduli i)) (htarget : ∀ i ∈ L, target i = y i)
    (anchor : σ → ℤ)
    (hanchor : anchor ∈ primeCoordinateCell ctx.base.lower ctx.base.sides ctx.moduli (L ∪ J) target) :
    ∃ next : ctx.State (L ∪ J) target, next.rank < state.rank := by
  have halign := state.aligned_refinement hIL hy u hu
  obtain ⟨c, hc, hcu, _⟩ := exists_prime_cell_physical_comparison ctx.base ctx.baseline ctx.orbit
    ctx.positive ctx.complexity ctx.moduli ctx.moduli_pos ctx.moduli_coprime L J hLJ y z hz u v hu hv
    ctx.gap_pos ctx.gap_le_one ctx.gap_inverse ctx.record_two hgap
  have hdisjoint : Disjoint J (L ∪ periodPrimeCoordinates ctx.prime state.stack.periods.prod) :=
    hLJ.symm.mono_right (Finset.union_subset (Finset.Subset.refl _) hperiods)
  have hcop := state.stack.pending_coprime_selected_periods ctx.prime ctx.power ctx.prime_prime
    ctx.prime_injective L J hdisjoint
  have hcardD : (L ∪ J).card ≤ ctx.allowance := hcard.trans state.one_step_room
  have hsource : ∀ j, (((∏ i ∈ L, ctx.moduli i) * (∏ i ∈ J, ctx.moduli i) : ℕ) : ℝ) *
      Real.exp (5 * ctx.workBudget + 2 * (ctx.workBudget + 2) ^ ctx.parameters.Kf + 16) ≤ (ctx.base.sides j : ℝ) := by
    intro j
    simpa only [Finset.prod_union hLJ] using ctx.node_width hlarge (L ∪ J) hcardD j
  have hinside := (mem_translatedIntegerBox ctx.base.lower ctx.base.sides anchor).mp
    ((mem_primeCoordinateCell ctx.base.lower ctx.base.sides ctx.moduli (L ∪ J) target anchor).mp hanchor).1
  have hanchorOld := primeCoordinateCell_mono ctx.base.lower ctx.base.sides ctx.moduli
    Finset.subset_union_left htarget hanchor
  rw [primeCoordinateCell_anchor ctx.base.lower ctx.base.sides ctx.moduli L y u hu] at hanchorOld
  have hcompat := ((mem_primeCoordinateCell_anchor ctx.base.lower ctx.base.sides ctx.moduli
    ctx.moduli_coprime L u anchor).mp hanchorOld).2
  obtain ⟨nextStack, hevent, hnextAlign, hnextSchedule⟩ := ctx.parameters.event ctx.recordCap 0 u
    state.stack c ctx.recordCap_nonneg (by omega) state.scheduled halign hc
    (fun i => by rw [hcu]) (by simpa only [Nat.mul_one, moduli] using hcop)
    (by simpa only [Nat.zero_add, workBudget] using hsource) anchor hinside hcompat
  have hnextAlign' : AlignedAt (∏ i ∈ L ∪ J, ctx.moduli i) anchor nextStack := by
    simpa only [Finset.prod_union hLJ] using hnextAlign
  have hdrop : epochStackRank bound nextStack.dimensions < state.rank := hevent.rank_lt
  let next : ctx.State (L ∪ J) target := {
    anchor := anchor
    anchor_mem := hanchor
    stack := nextStack
    scheduled := hnextSchedule
    aligned := hnextAlign'
    room := state.room_of_smaller_rank (L ∪ J) _ hcard hdrop }
  exact ⟨next, hdrop⟩

end Erdos3.PrimeStabilityContext

end

section

namespace Erdos3.PrimeStabilityContext

open PhysicalEpochStack CoordinateDecisionTree

universe u v w

variable {ι : Type w} {σ : Type u} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  {s bound : ℕ} {ctx : PrimeStabilityContext.{u, v, w} ι σ s bound}
  {I : Finset ι} {x : ∀ i, σ → ZMod (ctx.moduli i)}

theorem State.local_tree (state : ctx.State I x) (hlarge : ctx.HasLargeSides) :
    ∃ tree : CoordinateDecisionTree ι (fun i => σ → ZMod (ctx.moduli i)),
      Valid (fun J y => ctx.Good J y ∨ ∃ next : ctx.State J y, next.rank < state.rank)
        I x tree ctx.stepCost := by
  classical
  let Post := fun (J : Finset ι) (y : ∀ i, σ → ZMod (ctx.moduli i)) =>
    ctx.Good J y ∨ ∃ next : ctx.State J y, next.rank < state.rank
  let batch := state.periodBatch
  have hbatchCard : batch.card ≤ ctx.periodCap := state.periodBatch_card
  have afterPeriods : ∀ y : ∀ i, σ → ZMod (ctx.moduli i), (∀ i ∈ I, y i = x i) →
      ∃ tree : CoordinateDecisionTree ι (fun i => σ → ZMod (ctx.moduli i)),
        Valid Post (I ∪ batch) y tree ctx.witnessSize := by
    intro y hy
    let L := I ∪ batch
    by_cases hgood : ctx.Good L y
    · exact ⟨.leaf, .leaf (Or.inl hgood)⟩
    · have hnonempty : (primeCoordinateCell ctx.base.lower ctx.base.sides ctx.moduli L y).Nonempty := by
        by_contra hempty
        exact hgood (primeCoordinateStable_of_empty ctx.baseline.eval ctx.base.lower ctx.base.sides
          ctx.moduli ctx.witnessSize ctx.gap L y hempty)
      obtain ⟨u, hu⟩ := hnonempty
      have hbad := hgood
      change ¬ PrimeCoordinateStable ctx.baseline.eval ctx.base.lower ctx.base.sides ctx.moduli
        ctx.witnessSize ctx.gap L y at hbad
      unfold PrimeCoordinateStable at hbad
      push Not at hbad
      obtain ⟨J, hLJ, hJ, z, hzy, hznonempty, hgap⟩ := hbad
      obtain ⟨v, hv⟩ := hznonempty
      have hcard : (L ∪ J).card ≤ I.card + ctx.stepCost := by
        have hL : L.card ≤ I.card + batch.card := Finset.card_union_le I batch
        have hLJcard : (L ∪ J).card ≤ L.card + J.card := Finset.card_union_le L J
        change (L ∪ J).card ≤ I.card + (ctx.periodCap + ctx.witnessSize)
        omega
      have hperiods : periodPrimeCoordinates ctx.prime state.stack.periods.prod ⊆ L := state.periods_covered
      have afterWitness : ∀ target : ∀ i, σ → ZMod (ctx.moduli i), (∀ i ∈ L, target i = y i) →
          ∃ tree : CoordinateDecisionTree ι (fun i => σ → ZMod (ctx.moduli i)),
            Valid Post (L ∪ J) target tree 0 := by
        intro target htarget
        by_cases hnonempty : (primeCoordinateCell ctx.base.lower ctx.base.sides ctx.moduli (L ∪ J) target).Nonempty
        · obtain ⟨anchor, hanchor⟩ := hnonempty
          obtain ⟨next, hnext⟩ := state.repair_cell hlarge L J Finset.subset_union_left hLJ hperiods hcard
            y z hy hzy u v hu hv hgap.le target htarget anchor hanchor
          exact ⟨.leaf, .leaf (Or.inr ⟨next, hnext⟩)⟩
        · exact ⟨.leaf, .leaf (Or.inl (primeCoordinateStable_of_empty ctx.baseline.eval ctx.base.lower
            ctx.base.sides ctx.moduli ctx.witnessSize ctx.gap (L ∪ J) target hnonempty))⟩
      obtain ⟨tree, htree⟩ := exists_query_batch Post J 0 L y hLJ afterWitness
      exact ⟨tree, htree.mono (by omega)⟩
  obtain ⟨tree, htree⟩ := exists_query_batch Post batch ctx.witnessSize I x state.periodBatch_disjoint afterPeriods
  exact ⟨tree, htree.mono (by change batch.card + ctx.witnessSize ≤ ctx.periodCap + ctx.witnessSize; omega)⟩

end Erdos3.PrimeStabilityContext

end

section

namespace Erdos3.PrimeStabilityContext

open PhysicalEpochStack CoordinateDecisionTree
open scoped BigOperators

universe u v w

variable {ι : Type w} {σ : Type u} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  {s bound : ℕ}

theorem State.stable_tree {ctx : PrimeStabilityContext.{u, v, w} ι σ s bound}
    {I : Finset ι} {x : ∀ i, σ → ZMod (ctx.moduli i)} (state : ctx.State I x) (hlarge : ctx.HasLargeSides) :
    ∃ tree : CoordinateDecisionTree ι (fun i => σ → ZMod (ctx.moduli i)),
      Valid ctx.Good I x tree (ctx.stepCost * (state.rank + 1)) :=
  exists_of_rank_decreasing_step (fun I x => ctx.State I x) (fun _ _ state => state.rank)
    ctx.Good ctx.stepCost (fun _ _ state => state.local_tree hlarge) I x state

theorem exists_stable_tree (ctx : PrimeStabilityContext.{u, v, w} ι σ s bound) (hlarge : ctx.HasLargeSides) :
    ∃ tree : CoordinateDecisionTree ι (fun i => σ → ZMod (ctx.moduli i)),
      Valid (fun I x => ctx.mandatory ⊆ I ∧ ctx.Good I x) ∅ (fun _ _ => 0) tree ctx.allowance := by
  classical
  let Final := fun (I : Finset ι) (x : ∀ i, σ → ZMod (ctx.moduli i)) => ctx.mandatory ⊆ I ∧ ctx.Good I x
  let depth := ctx.stepCost * (bound + 1) ^ s
  have afterMandatory : ∀ y : ∀ i, σ → ZMod (ctx.moduli i),
      ∃ tree : CoordinateDecisionTree ι (fun i => σ → ZMod (ctx.moduli i)),
        Valid Final ctx.mandatory y tree depth := by
    intro y
    by_cases hnonempty : (primeCoordinateCell ctx.base.lower ctx.base.sides ctx.moduli ctx.mandatory y).Nonempty
    · obtain ⟨anchor, hanchor⟩ := hnonempty
      have hinside := (mem_translatedIntegerBox ctx.base.lower ctx.base.sides anchor).mp
        ((mem_primeCoordinateCell ctx.base.lower ctx.base.sides ctx.moduli ctx.mandatory y anchor).mp hanchor).1
      have hmandatory : ctx.mandatory.card ≤ ctx.allowance := by
        change ctx.mandatory.card ≤ ctx.mandatory.card + _
        omega
      have hnorm : ∀ i, Real.exp (physicalEpochBudget ctx.parameters.A ctx.parameters.C ctx.recordCap (0 + s)) ≤
          (ctx.base.sides i : ℝ) / (∏ j ∈ ctx.mandatory, ctx.moduli j : ℕ) := by
        intro i
        simpa only [Nat.zero_add, workBudget] using ctx.construction_width hlarge ctx.mandatory hmandatory i
      obtain ⟨stack, _, _, halign, hschedule⟩ :=
        exists_scheduled_physical_epoch_stack ctx.parameters.A ctx.parameters.C s ctx.parameters.A_pos
          (by linarith [ctx.parameters.C_ge_two]) (@PhysicalStabilityParameters.frames _ ctx.parameters)
          ctx.recordCap ctx.recordCap_nonneg s le_rfl 0 ctx.base (PhysicalEpochRecords.empty ctx.base)
          (∏ i ∈ ctx.mandatory, ctx.moduli i) (ctx.product_pos ctx.mandatory) anchor hinside
          (by simp [PhysicalEpochRecords.empty]) ctx.record_le_cap ctx.inflation hnorm
      have hrank : epochStackRank bound stack.dimensions + 1 ≤ (bound + 1) ^ s := by
        have h := epochStackRank_lt bound stack.dimensions stack.dimensions_bounded
        rw [stack.dimensions_length] at h
        omega
      have hroom : ctx.mandatory.card + ctx.stepCost * (epochStackRank bound stack.dimensions + 1) ≤ ctx.allowance :=
        Nat.add_le_add_left (Nat.mul_le_mul_left ctx.stepCost hrank) _
      let initial : ctx.State ctx.mandatory y := ⟨anchor, hanchor, stack, hschedule, halign, hroom⟩
      obtain ⟨tree, htree⟩ := initial.stable_tree hlarge
      exact ⟨tree, (htree.preserve_subset (Finset.Subset.refl _)).mono (Nat.mul_le_mul_left ctx.stepCost hrank)⟩
    · exact ⟨.leaf, .leaf ⟨Finset.Subset.refl _, primeCoordinateStable_of_empty ctx.baseline.eval
        ctx.base.lower ctx.base.sides ctx.moduli ctx.witnessSize ctx.gap ctx.mandatory y hnonempty⟩⟩
  obtain ⟨tree, htree⟩ := exists_query_batch Final ctx.mandatory depth ∅ (fun _ _ => 0)
    (Finset.disjoint_empty_left _) (fun y _ => by simpa only [Finset.empty_union] using afterMandatory y)
  exact ⟨tree, htree⟩

theorem exists_covering_stable_tree (ctx : PrimeStabilityContext.{u, v, w} ι σ s bound) (hlarge : ctx.HasLargeSides) :
    ∃ tree : CoordinateDecisionTree ι (fun i => σ → ZMod (ctx.moduli i)),
      Valid (fun I x => ctx.mandatory ⊆ I ∧ ctx.Good I x) ∅ (fun _ _ => 0) tree ctx.allowance ∧
      ∀ z ∈ translatedIntegerBox ctx.base.lower ctx.base.sides,
        let leaf := trace tree ∅ (fun _ _ => 0) (fun i j => (z j : ZMod (ctx.moduli i)))
        z ∈ primeCoordinateCell ctx.base.lower ctx.base.sides ctx.moduli leaf.1 leaf.2 ∧
        ctx.mandatory ⊆ leaf.1 ∧ ctx.Good leaf.1 leaf.2 ∧ leaf.1.card ≤ ctx.allowance := by
  obtain ⟨tree, htree⟩ := ctx.exists_stable_tree hlarge
  refine ⟨tree, htree, ?_⟩
  intro z hz
  let input := fun i j => (z j : ZMod (ctx.moduli i))
  have hagree := trace_agrees tree ∅ (fun _ _ => 0) input (by simp)
  have hgood := htree.trace_good input
  have hcard := htree.trace_card_le input
  refine ⟨(mem_primeCoordinateCell _ _ _ _ _ _).mpr ⟨hz, ?_⟩, hgood.1, hgood.2, ?_⟩
  · intro i hi
    exact (hagree i hi).symm
  · simpa only [Finset.card_empty, Nat.zero_add] using hcard

end Erdos3.PrimeStabilityContext

end

end OAI
