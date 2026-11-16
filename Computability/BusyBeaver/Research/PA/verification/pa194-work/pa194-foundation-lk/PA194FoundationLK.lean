import PA194SourceContext
import Foundation.FirstOrder.Basic.Calculus
namespace PA194Logic.Relational.Source
open LO LO.FirstOrder M6.PA.RelationalSource
noncomputable section

def foundationBudget {Γ : List (Proposition language)} (d : LO.FirstOrder.Derivation Γ) : Nat :=
  max (sequentDepth (Γ : SourceSequent) + 1) (match d with
    | .identity _ _ => 1
    | .cut p q => max (foundationBudget p) (foundationBudget q)
    | .contraction p _ => foundationBudget p
    | .verum => 1
    | .or p => foundationBudget p
    | .and p q => max (foundationBudget p) (foundationBudget q)
    | .all p => foundationBudget p + 1
    | .exs p => foundationBudget p + 1)

theorem foundationDepth_lt {Γ : List (Proposition language)} (d : LO.FirstOrder.Derivation Γ)
    {p : Proposition language} (h : p ∈ Γ) : depth p < foundationBudget d := by
  unfold foundationBudget
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_of_le (depth_le_sequentDepth (by simpa using h))) (Nat.le_max_left _ _)

def refutesSubset {Γ Δ : SourceSequent} {f : Nat → Nat} {lo z : Nat}
    (h : ∀ p, p ∈ Δ → p ∈ Γ) (d : Refutes Δ f lo z) : Refutes Γ f lo z := by
  intro C supply
  exact d (fun p hp => supply p (h p hp))
def compileFoundationLK {Γ : List (Proposition language)} (d : LO.FirstOrder.Derivation Γ)
    (f : Nat → Nat) (lo z : Nat) (hlo : 0 < lo) (hf : ∀ i,f i < lo)
    (hz : lo + foundationBudget d ≤ z) : Refutes (Γ : SourceSequent) f lo z := by
  cases d with
  | identity r ts =>
    intro C h
    apply refutesIdentity r ts f lo z
    intro q hq
    apply h
    simpa using hq
  | verum =>
    intro C h
    have hn := h (⊤ : Proposition language) (by simp)
    change Context C (wn 0) at hn
    exact Context.mp (.closed truthProof) hn
  | @cut φ Γ Δ p q =>
    have hp : foundationBudget p ≤ foundationBudget (.cut p q) :=
      (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
    have hq : foundationBudget q ≤ foundationBudget (.cut p q) :=
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
    have rp : Refutes ((Γ : SourceSequent) + ⦃φ⦄) f lo z := by
      intro C h
      apply compileFoundationLK p f lo z hlo hf (by omega)
      intro r hr
      apply h
      simpa [Multiset.mem_add, or_comm] using hr
    have rq : Refutes ((Δ : SourceSequent) + ⦃Semiformula.neg φ⦄) f lo z := by
      intro C h
      apply compileFoundationLK q f lo z hlo hf (by omega)
      intro r hr
      apply h
      simpa [Multiset.mem_add, or_comm, Semiformula.neg_eq] using hr
    intro C h
    apply refutesCut rp rq
    intro r hr
    apply h
    simpa [Multiset.mem_add] using hr
  | contraction p hs =>
    have hp : foundationBudget p ≤ foundationBudget (.contraction p hs) := Nat.le_max_right _ _
    intro C h
    apply compileFoundationLK p f lo z hlo hf (by omega)
    intro r hr
    apply h
    simpa using hs (by simpa using hr)
  | @or φ ψ Γ p =>
    have hp : foundationBudget p ≤ foundationBudget (.or p) := Nat.le_max_right _ _
    have rp : Refutes ((Γ : SourceSequent) + ⦃φ,ψ⦄) f lo z := by
      intro C h
      apply compileFoundationLK p f lo z hlo hf (by omega)
      intro r hr
      apply h
      simpa [Multiset.mem_add, or_comm, or_left_comm, or_assoc] using hr
    intro C h
    apply refutesOr rp
    intro r hr
    apply h
    change r ∈ (↑(Semiformula.or φ ψ :: Γ) : SourceSequent)
    simpa [Multiset.mem_add, or_comm] using hr
  | @and φ Γ ψ p q =>
    have hp : foundationBudget p ≤ foundationBudget (.and p q) :=
      (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
    have hq : foundationBudget q ≤ foundationBudget (.and p q) :=
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
    have rp : Refutes ((Γ : SourceSequent) + ⦃φ⦄) f lo z := by
      intro C h
      apply compileFoundationLK p f lo z hlo hf (by omega)
      intro r hr
      apply h
      simpa [Multiset.mem_add, or_comm] using hr
    have rq : Refutes ((Γ : SourceSequent) + ⦃ψ⦄) f lo z := by
      intro C h
      apply compileFoundationLK q f lo z hlo hf (by omega)
      intro r hr
      apply h
      simpa [Multiset.mem_add, or_comm] using hr
    intro C h
    apply refutesAnd rp rq
    intro r hr
    apply h
    change r ∈ (↑(Semiformula.and φ ψ :: Γ) : SourceSequent)
    simpa [Multiset.mem_add, or_comm] using hr
  | @all Γ p d =>
    have hd : foundationBudget d + 1 ≤ foundationBudget (.all d) := Nat.le_max_right _ _
    have hpos : 0 < foundationBudget (.all d) := by
      have h := foundationDepth_lt (.all d) (p := ∀⁰ p) (by simp)
      omega
    have rp : Refutes ((Γ : SourceSequent).map Semiformula.shift + ⦃p.free⦄)
        (shiftedLabels f lo) (lo+1) z := by
      intro C h
      apply compileFoundationLK d (shiftedLabels f lo) (lo+1) z (by omega)
        (fun i => by cases i with
         | zero => simp [shiftedLabels]
         | succ i => simpa [shiftedLabels] using Nat.lt_trans (hf i) (Nat.lt_succ_self lo)) (by omega)
      intro r hr
      apply h
      simpa [LO.FirstOrder.Rewriting.shifts, Multiset.mem_add, or_comm] using hr
    have rr : Refutes ((Γ : SourceSequent) + ⦃Semiformula.all p⦄) f lo z :=
      refutesAll (traversal (Γ : SourceSequent)) p f lo z hlo hf (by omega)
        (by intro q hq; have h := foundationDepth_lt (.all d) (p := q) (by simpa using Or.inr hq); omega) rp
    intro C h
    apply rr
    intro r hr
    apply h
    change r ∈ (↑(Semiformula.all p :: Γ) : SourceSequent)
    simpa [Multiset.mem_add, or_comm] using hr
  | @exs p t Γ d =>
    have hd : foundationBudget d + 1 ≤ foundationBudget (.exs d) := Nat.le_max_right _ _
    have h := foundationDepth_lt (.exs d) (p := ∃⁰ p) (by simp)
    change depth p + 1 < foundationBudget (.exs d) at h
    have rp : Refutes ((Γ : SourceSequent) + ⦃instantiate p t⦄) f lo z := by
      intro C h
      apply compileFoundationLK d f lo z hlo hf (by omega)
      intro r hr
      apply h
      simpa [instantiate_eq_subst, Multiset.mem_add, or_comm] using hr
    have rr : Refutes ((Γ : SourceSequent) + ⦃Semiformula.exs p⦄) f lo z :=
      refutesExs p t f lo z hlo hf (by omega) rp
    intro C h
    apply rr
    intro r hr
    apply h
    change r ∈ (↑(Semiformula.exs p :: Γ) : SourceSequent)
    simpa [Multiset.mem_add, or_comm] using hr
termination_by structural d

def compileFoundationContext (xs : List (Proposition language)) (σ : Proposition language)
    (d : LO.FirstOrder.Derivation (xs.map Semiformula.neg ++ [σ]))
    (f : Nat → Nat) (lo z : Nat) (hlo : 0 < lo) (hf : ∀ i,f i < lo)
    (hz : lo + foundationBudget d ≤ z)
    (suppliers : ∀ p,p ∈ xs → Proof (code p f lo z)) : Proof (code σ f lo z) := by
  have r : Refutes ((xs.map Semiformula.neg : SourceSequent) + ⦃σ⦄) f lo z := by
    intro C h
    apply compileFoundationLK d f lo z hlo hf hz
    intro p hp
    apply h
    simpa [Multiset.mem_add] using hp
  exact (r.positive (fun p hp =>
    .closed (contextNegativeProof xs f lo z suppliers p (by simpa using hp)))).empty

#print axioms compileFoundationLK
#print axioms compileFoundationContext

end
end PA194Logic.Relational.Source
