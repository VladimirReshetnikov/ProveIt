import GowersSzemeredi.Proofs18IntervalDiscrepancyIncrement
import GowersSzemeredi.Proofs18NaturalIntervalIncrement

/-! An explicit function discrepancy hypothesis suffices for the nonuniform
branch on integer intervals. Its threshold is retained, not hidden in an
unspecified sufficiently-large-modulus assumption. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- Quantitative function-level inverse input needed by relative density
iteration. This is an unasserted hypothesis for general degree. -/
def FunctionDiscrepancyBound (degree : Nat) (alpha beta sigma T : Real) : Prop :=
  ∀ (N : Nat) [NeZero N] [Fact N.Prime], T ≤ N →
    ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha degree →
      ∃ M : Nat, ∃ Q : Fin M → ModAP N,
        IsPartition (fun i => (Q i).carrier) Finset.univ ∧
        (∀ i, (Q i).IsProper) ∧
        (N : Real) ^ sigma ≤ averageCellSize (fun i => (Q i).carrier) ∧
        beta * N ≤ ∑ i, ‖∑ x ∈ (Q i).carrier, f x‖

/-- A function discrepancy bound yields an ordinary progression contained
in the original interval, with increased original relative density. -/
theorem FunctionDiscrepancyBound.natural_interval_increment
    {degree : Nat} {alpha beta sigma T : Real}
    (hbound : FunctionDiscrepancyBound degree alpha beta sigma T) (hβ : 0 < beta)
    (N L : Nat) [NeZero N] [Fact N.Prime] (hL : 2 * L < N)
    (hN : T ≤ N) (hscale : 32 ≤ beta * N)
    (B : Finset (Fin L)) (delta : Real)
    (hδ : 0 ≤ delta) (hδone : delta ≤ 1) (hcard : (B.card : Real) = delta * L)
    (hnot : ¬ UniformOfDegree (intervalExtension N (finiteIntervalBalance B delta)) alpha degree) :
    ∃ Q : NatAP, Q.IsProper ∧ Q.carrier ⊆ Finset.range L ∧
      (beta / (8 * boundaryRefinementConstant (beta / 64))) *
        (N : Real) ^ (sigma / 16) ≤ (Q.length : Real) ∧
      (delta + beta / 8) * Q.length ≤ (B.image Fin.val ∩ Q.carrier).card := by
  have hLN : L ≤ N := by omega
  let A := finiteIntervalImage N B
  let S := finiteIntervalImage N (Finset.univ : Finset (Fin L))
  have hAS : A ⊆ S := finiteIntervalImage_subset B
  obtain ⟨M, R, hR, hRproper, havg, hdis⟩ := hbound N hN
    (relativeBalanced A S delta) (relativeBalanced_discValued A S delta hAS hδ hδone)
    (by simpa only [A, S, relativeBalanced_finiteIntervalImage hLN] using hnot)
  obtain ⟨P, hP, hsub, hsize, hinc⟩ := interval_density_increment_of_discrepancy_partition
    hLN beta sigma hβ hscale A delta hAS hδ hδone
    (by simpa only [A, finiteIntervalImage_card hLN] using hcard) R hR hRproper havg hdis
  obtain ⟨Q, hQ, hlen, hcarrier, hsubQ⟩ := P.exists_natAP_of_short_interval hP hL hsub
  have hPcard : P.carrier.card = P.length := hP
  refine ⟨Q, hQ, hsubQ, ?_, ?_⟩
  · simpa only [hlen, hPcard] using hsize
  · have hcount := card_inter_natAP_of_carrier_eq P Q hcarrier A
    rw [show A = finiteIntervalImage N B from rfl, finiteIntervalImage_val hLN] at hcount
    simpa only [hlen, hPcard, hcount] using hinc

/-- The quadratic inverse theorem already discharges this interface with
its proved explicit modulus threshold. General degrees remain open. -/
theorem quadratic_function_discrepancy_bound {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    FunctionDiscrepancyBound 2 alpha (quadraticDiscrepancyParameter alpha)
      (quadraticDiscrepancyExponent alpha) (quadraticExponentialThreshold alpha) := by
  intro N _ _ hN f hf hnot
  exact quadratic_nonuniformity_discrepancy_partition_explicit alpha hα hαone N
    ((quadraticDensityThreshold_le_exp_power hα hαone).trans hN) f hf hnot

end LeanProofs.GowersSzemeredi
