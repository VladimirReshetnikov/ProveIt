import BoundedPAConsistency.DynamicTruthAxiomSoundnessSemantic
import BoundedPAConsistency.FixedLevelPAInduction

/-!
# Reducing two model-induction interfaces to ordinary successor induction

`DynamicTruthAxiomSoundnessSemantic` isolates three uses of full PA
induction in dynamic PA-axiom soundness.  The first of them, ordinary
induction for the semantic predicate obtained from a coded induction axiom,
is already realized by a fixed source sentence.  The remaining two are stated
directly as closure properties, and a fixed source proof cannot use them
until they have been reduced to induction over a *single* numerical variable.

This module performs that reduction, entirely semantically and for an
arbitrary relation `Sat`.  Each interface becomes one unary invariant whose
base and successor cases follow from laws that the staged certificate has
already established:

* free-environment independence peels the coded environment one semantic head
  at a time, using only the shift law;
* universal-closure introduction peels one leading quantifier at a time,
  using only the universal Tarski clause.

No definability level is attached to either invariant.  The later fixed-source
compiler supplies the corresponding closed induction axiom after the truth
predicate has been substituted, so the argument stays valid at a nonstandard
hierarchy index.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessInterfaceSemantic

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.AbstractSoundness
open LeanProofs.BoundedPAConsistency.CodedHierarchy
open LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessSemantic
open LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantPositiveRankStrongStep
open LeanProofs.BoundedPAConsistency.FixedLevelPAInduction
open LeanProofs.BoundedPAConsistency.TermEvaluationTransport

variable {V : Type*} [ORingStructure V]
variable [hPA : V↓[ℒₒᵣ] ⊧* Peano]

local instance : V↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

/-! ## Independence from the coded free environment -/

/-- At stage `k`, every shift-fixed bounded code has the same truth value
under the empty environment as under any genuine environment of length `k`.

The bound environment and the formula code are universally quantified inside
the invariant, so the whole assertion is a unary predicate of `k`. -/
def FreeIndependenceInvariant
    (level : V) (Sat : V → V → V → Prop) (k : V) : Prop :=
  ∀ p bound free : V,
    QuantifierBoundedCode ℒₒᵣ level p →
    shift ℒₒᵣ p = p →
    Arithmetic.Seq free →
    lh free = k →
    (Sat bound free p ↔ Sat bound 0 p)

/-- The only genuine environment of length zero is the empty sequence. -/
theorem freeIndependenceInvariant_zero
    {level : V} {Sat : V → V → V → Prop} :
    FreeIndependenceInvariant level Sat 0 := by
  intro p bound free _hbounded _hshiftFixed hfree hlen
  have hzero : free = (∅ : V) := hfree.isempty_of_lh_eq_zero hlen
  have hempty : (∅ : V) = 0 := emptyset_def
  rw [hzero, hempty]

/-- One semantic head is removed by the shift law.  The removed entry is
invisible to a shift-fixed code, so the truth value is unchanged. -/
theorem freeIndependenceInvariant_succ
    {level : V} {Sat : V → V → V → Prop}
    (hshift : ∀ q, ShiftInvariantAt Sat level q)
    {k : V} (ih : FreeIndependenceInvariant level Sat k) :
    FreeIndependenceInvariant level Sat (k + 1) := by
  intro p bound free hbounded hshiftFixed hfree hlen
  rcases exists_isFreeTail hfree with ⟨tail, htail, htailLen, hfreeTail⟩
  have htailLen' : lh tail = k := by
    simpa [hlen] using htailLen
  calc
    Sat bound free p ↔ Sat bound free (shift ℒₒᵣ p) := by
          rw [hshiftFixed]
    _ ↔ Sat bound tail p := hshift p bound free tail hfreeTail hbounded
    _ ↔ Sat bound 0 p :=
          ih p bound tail hbounded hshiftFixed htail htailLen'

/-- Comparing two genuine environments with the empty one gives the interface
consumed by dynamic PA-axiom soundness. -/
theorem freeEnvironmentIndependence_of_invariant
    {level : V} {Sat : V → V → V → Prop}
    (h : ∀ k : V, FreeIndependenceInvariant level Sat k) :
    FreeEnvironmentIndependence level Sat := by
  intro bound p free₁ free₂ hbounded hshiftFixed hfree₁ hfree₂
  exact (h (lh free₁) p bound free₁ hbounded hshiftFixed hfree₁ rfl).trans
    (h (lh free₂) p bound free₂ hbounded hshiftFixed hfree₂ rfl).symm

/-! ## Introduction of an internally iterated universal block -/

/-- At stage `k`, the remaining `k` quantifiers are true under every genuine
bound environment whose length, together with `k`, is the original closure
length.  Carrying the rank hypothesis inside the invariant supplies the
premise required by the universal Tarski clause at successor stages. -/
def ClosureInvariant
    (level : V) (Sat : V → V → V → Prop) (k : V) : Prop :=
  ∀ m b free base : V,
    QuantifierBoundedCode ℒₒᵣ level (qqAlls b k) →
    (∀ base', Arithmetic.Seq base' → lh base' = m → Sat base' free b) →
    Arithmetic.Seq base →
    lh base + k = m →
    Sat base free (qqAlls b k)

/-- With no quantifiers left, the closure body is the assumed premise. -/
theorem closureInvariant_zero
    {level : V} {Sat : V → V → V → Prop} :
    ClosureInvariant level Sat 0 := by
  intro m b free base _hbounded hbody hbase hlen
  simpa using hbody base hbase (by simpa using hlen)

/-- One leading quantifier is removed by the universal Tarski clause, and the
witness is appended to the bound environment. -/
theorem closureInvariant_succ
    {level : V} {Sat : V → V → V → Prop}
    (laws : Laws level Sat)
    {k : V} (ih : ClosureInvariant level Sat k) :
    ClosureInvariant level Sat (k + 1) := by
  intro m b free base hbounded hbody hbase hlen
  rw [qqAlls_succ] at hbounded ⊢
  have hchildBound : QuantifierBoundedCode ℒₒᵣ level (qqAlls b k) := by
    apply quantifierBoundedCode_of_qqAlls (k := 1)
    have hone : qqAlls (qqAlls b k) 1 = ^∀ (qqAlls b k) := by
      simpa using qqAlls_succ (qqAlls b k) 0
    rw [hone]
    exact hbounded
  apply (laws.all_iff hbounded).mpr
  intro a
  apply ih m b free (base ⁀' a) hchildBound hbody (hbase.seqCons a)
  rw [Seq.lh_seqCons _ hbase]
  simpa [add_assoc, add_comm, add_left_comm] using hlen

/-- Running the invariant from the empty bound environment introduces the
complete, possibly nonstandard, universal block. -/
theorem universalClosureIntroduction_of_invariant
    {level : V} {Sat : V → V → V → Prop}
    (h : ∀ k : V, ClosureInvariant level Sat k) :
    UniversalClosureIntroduction level Sat := by
  intro m b free hbounded _hfree hbody
  have hzeroSeq : Arithmetic.Seq (0 : V) := by
    simpa [emptyset_def] using (seq_empty : Arithmetic.Seq (∅ : V))
  have hlhZero : lh (0 : V) = 0 := by
    simpa [emptyset_def] using (lh_empty (V := V))
  exact h m m b free 0 hbounded hbody hzeroSeq (by simp [hlhZero])

end LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessInterfaceSemantic
