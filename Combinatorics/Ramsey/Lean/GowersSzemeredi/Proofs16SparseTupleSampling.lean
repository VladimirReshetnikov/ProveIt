import GowersSzemeredi.Proofs16GlobalColumnTupleClasses
import GowersSzemeredi.Proofs16BohrSampleSelection

/-! Sparse zero kernels of additive anchor tuples form the exceptional
family in Claim 6.3. Its cardinality is at most `N^k`, and its sampling
loss is measured before restricting to the retained index set. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Fixing the alternating value determines the head from the tail. -/
theorem columnAnchorFibre_card_le {N k : Nat} [NeZero N]
    (P : Finset (ZMod N)) (c : ZMod N) : (columnAnchorFibre P k c).card ≤ N^k := by
  have h := Finset.card_le_card_of_injOn
    (s := columnAnchorFibre P k c) (t := (Finset.univ : Finset (Fin k → ZMod N)))
    (fun a : ColumnAnchorTuple N k => a.2) (by simp) (by
      intro a ha b hb he
      have hva := (Finset.mem_filter.mp ha).2.2
      have hvb := (Finset.mem_filter.mp hb).2.2
      change a.1-columnAnchorEval id (List.ofFn a.2) = c at hva
      change b.1-columnAnchorEval id (List.ofFn b.2) = c at hvb
      change a.2 = b.2 at he
      rw [he] at hva
      have hhead : a.1 = b.1 := by linear_combination hva-hvb
      exact Prod.ext hhead he)
  simpa using h

def columnTupleZeroLevel {N k : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    (rho : Real) (a : ColumnAnchorTuple N k) : Finset (ZMod N) :=
  (bohr (columnListSpectrum T (columnAnchorList a)) rho).filter
    (fun y => columnAnchorEval (fun x => L x y) (columnAnchorList a) = 0)

def sparseColumnTuples {N k : Nat} [NeZero N]
    (P : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (rho eta : Real) : Finset (ColumnAnchorTuple N k) :=
  (columnAnchorFibre P k 0).filter fun a => ((columnTupleZeroLevel T L rho a).card : Real) ≤ eta*N

theorem sparseColumnTuples_card_le {N k : Nat} [NeZero N]
    (P : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (rho eta : Real) :
    (sparseColumnTuples (k := k) P T L rho eta).card ≤ N^k :=
  (Finset.card_filter_le _ _).trans (columnAnchorFibre_card_le P 0)

/-- One sample controls sparse-kernel losses on all original additive
tuples, while retaining a set of indices of epsilon-independent density. -/
theorem sparse_tuple_bohr_sample_selection {N r k d q : Nat} [NeZero N] [Fact N.Prime] [NeZero q]
    (hr : 0 < r) (P : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (rho : Real)
    {tau : Real} (hq : 1 ≤ tau*q) (hT : ∀ x ∈ P, (T x).card ≤ d)
    {b eta epsilon : Real} (hb : 0 < b) (heta : 0 ≤ eta) (he : 0 < epsilon)
    (hP : b*N ≤ (P.card : Real))
    (hbadBudget : 8*(3 : Real)^r*eta ≤ epsilon*b*(1/(q : Real)^d)^r)
    (hcollisionBudget : 8*(3 : Real)^r ≤ b*(1/(q : Real)^d)^r*N) :
    ∃ e : Fin r → ZMod N, Function.Injective (booleanSampleValue e) ∧
      (Finset.univ.image (booleanSampleValue e)).card = 2^r ∧
      b*(1/(q : Real)^d)^r*N/2 ≤
        ((retainedSampleIndices P (fun x => bohr (T x) tau) e).card : Real) ∧
      ((sampleBadIndices (sparseColumnTuples (k := k) P T L rho eta)
        (columnTupleZeroLevel T L rho) e).card : Real) ≤ epsilon*(N : Real)^k/2 := by
  exact bohr_sample_selection hr P T hq hT (sparseColumnTuples (k := k) P T L rho eta)
    (columnTupleZeroLevel T L rho) hb heta he hP
    (by exact_mod_cast sparseColumnTuples_card_le (k := k) P T L rho eta)
    (fun a ha => (Finset.mem_filter.mp ha).2) hbadBudget hcollisionBudget

end LeanProofs.GowersSzemeredi
