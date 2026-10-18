import GowersSzemeredi.Proofs05LinearPartition
import GowersSzemeredi.Proofs05ResiduePartition
import GowersSzemeredi.Proofs05DegreeDrop
import GowersSzemeredi.Proofs05PolynomialDiameter
import GowersSzemeredi.Proofs05PolynomialPartition

/-!
# The combinatorial degree step in Corollary 5.6

This assembles recurrence, residue partitions, degree reduction, and diameter
addition. The remaining input is a numerical choice of the coarse target u:
both possible child lengths must satisfy the lower-degree threshold, the final
target-length bound, and the combined diameter budget. The statement makes
those rounding obligations explicit rather than assuming the whole induction.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Finset

namespace LeanProofs.GowersSzemeredi

/-- The strong one-polynomial partition assertion in a fixed degree. -/
def StrongPolynomialPartitionAt (k : Nat) : Prop :=
  ∀ (N r v : Nat) [NeZero N] (phi : ZMod N → ZMod N),
    PolynomialOn k Finset.univ phi → polynomialPartitionThreshold k < r → r ≤ N →
    1 ≤ v → (v : Real) ≤ (r : Real) ^ (polynomialPartitionConstant k : Real)⁻¹ →
    ∃ M : Nat, ∃ P : Fin M → NatAP,
      0 < M ∧ IsNatAPPartition P (Finset.range r) ∧
      (∀ j, (P j).IsProper ∧ 0 < (P j).length ∧
        ((P j).length = v - 1 ∨ (P j).length = v)) ∧
      ∀ j, diameterAtMostReal
        ((P j).carrier.image fun x : Nat => phi (x : ZMod N))
        ((r : Real) ^ (-(2 * (polynomialPartitionConstant k : Real)⁻¹)) * N)

/-- The fixed-degree formulation is exactly the existing strong API. -/
theorem corollary_5_6_strong_diameter_iff :
    corollary_5_6_strong_diameter ↔ ∀ k, 1 ≤ k → StrongPolynomialPartitionAt k := by
  constructor
  · intro h k hk N r v _ phi hphi hthreshold hrN hv hvupper
    exact h N k r v phi hk hphi hthreshold hrN hv hvupper
  · intro h N k r v _ phi hk hphi hthreshold hrN hv hvupper
    exact h k hk N r v phi hphi hthreshold hrN hv hvupper

theorem strongPolynomialPartitionAt_one : StrongPolynomialPartitionAt 1 :=
  corollary_5_6_strong_diameter_degree_one

/-- The coefficient recurrence error on a coarse cell of length at most u,
before multiplying by the modulus. -/
def polynomialDegreeStepError (r u d : Nat) : Real :=
  (u : Real) ^ d * (r : Real) ^ (-((d : Real) * (2 : Real) ^ (d + 1))⁻¹)

/-- The actual degree step. Its numerical hypotheses must hold for both u-1
and u because the coarse partition may contain either cell length. -/
theorem section5_strong_partition_degree_step {k : Nat} (hk : 1 ≤ k)
    (hprev : StrongPolynomialPartitionAt k)
    (N r v u : Nat) [NeZero N] (phi : ZMod N → ZMod N)
    (hphi : PolynomialOn (k + 1) Finset.univ phi)
    (hthreshold : polynomialPartitionThreshold (k + 1) < r)
    (hrN : r ≤ N) (hv : 1 ≤ v) (hu : 1 ≤ u) (hu4 : u ^ 4 ≤ r)
    (hscale : ∀ L : Nat, L = u - 1 ∨ L = u →
      polynomialPartitionThreshold k < L ∧
      (v : Real) ≤ (L : Real) ^ (polynomialPartitionConstant k : Real)⁻¹ ∧
      polynomialDegreeStepError r u (k + 1) +
        (L : Real) ^ (-(2 * (polynomialPartitionConstant k : Real)⁻¹)) ≤
        (r : Real) ^ (-(2 * (polynomialPartitionConstant (k + 1) : Real)⁻¹))) :
    ∃ M : Nat, ∃ P : Fin M → NatAP,
      0 < M ∧ IsNatAPPartition P (Finset.range r) ∧
      (∀ j, (P j).IsProper ∧ 0 < (P j).length ∧
        ((P j).length = v - 1 ∨ (P j).length = v)) ∧
      ∀ j, diameterAtMostReal
        ((P j).carrier.image fun x : Nat => phi (x : ZMod N))
        ((r : Real) ^ (-(2 * (polynomialPartitionConstant (k + 1) : Real)⁻¹)) * N) := by
  obtain ⟨a, hdecompose⟩ := polynomialOn_affine_degree_drop phi hphi
  obtain ⟨p, hp, hp2, hrec⟩ :=
    lemma_5_5_square_root_auxiliary_holds (k + 1) r N (by omega) hthreshold.le hrN a
  obtain ⟨m, Q, hm, hQpart, hQcells, hQstep⟩ :=
    section5_residue_target_partition r p u (by omega) hu (by nlinarith)
  choose psi hpsi hidentity using
    fun i : Fin m => hdecompose ((Q i).start : ZMod N) (p : ZMod N)
  have hQN (i : Fin m) : (Q i).length ≤ N :=
    ((hQcells i).1.2.symm.trans_le (Finset.card_le_card (hQpart.cell_subset i))).trans
      ((Finset.card_range r).le.trans hrN)
  -- refine each coarse cell by the lower-degree partition of its lower-order part
  choose L R hL hRpart hRcells hRdiam using fun i : Fin m =>
    hprev N (Q i).length v (psi i) (hpsi i)
      (hscale (Q i).length (hQcells i).2.2).1 (hQN i) hv
      (hscale (Q i).length (hQcells i).2.2).2.1
  let T (i : Fin m) (j : Fin (L i)) := section5NatTransport (Q i) (R i j)
  have hTdiam (i : Fin m) (j : Fin (L i)) :
      diameterAtMostReal ((T i j).carrier.image fun x : Nat => phi (x : ZMod N))
        ((r : Real) ^ (-(2 * (polynomialPartitionConstant (k + 1) : Real)⁻¹)) * N) := by
    let b : ZMod N := a * (p : ZMod N) ^ (k + 1)
    -- the top-degree term `b t ^ (k + 1)` contributes at most the degree-step error
    have hmono : diameterAtMostReal
        ((R i j).carrier.image fun t : Nat => b * (t : ZMod N) ^ (k + 1))
        (polynomialDegreeStepError r u (k + 1) * N) := by
      refine ⟨_, diameterAtMost_monomial (u := u) (R i j).carrier ((hRpart i).cell_subset j |>.trans
        (Finset.range_mono (by rcases (hQcells i).2.2 with h | h <;> omega))) b, ?_⟩
      rw [polynomialDegreeStepError, mul_assoc, Nat.cast_mul, Nat.cast_pow]
      gcongr
      simpa only [b, mul_comm] using hrec
    have himage : (T i j).carrier.image (fun x : Nat => phi (x : ZMod N)) =
        (R i j).carrier.image (fun t : Nat => b * (t : ZMod N) ^ (k + 1) + psi i (t : ZMod N)) := by
      rw [show T i j = section5NatTransport (Q i) (R i j) from rfl,
        section5NatTransport_carrier, Finset.image_image]
      apply Finset.image_congr
      intro t _
      change phi (section5NatIndexPoint (Q i) t : ZMod N) = _
      rw [section5NatIndexPoint_cast, hQstep, hidentity]
    obtain ⟨d, hd, hds⟩ := diameterAtMostReal_add_image _ _ _ hmono (hRdiam i j)
    rw [himage]
    refine ⟨d, hd, hds.trans ?_⟩
    simpa only [add_mul] using mul_le_mul_of_nonneg_right
      (hscale (Q i).length (hQcells i).2.2).2.2 (Nat.cast_nonneg N)
  let e := section5NatFlattenEquiv L
  exact ⟨∑ i, L i, section5NatFlatten L T,
    (hL ⟨0, hm⟩).trans_le (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ _)),
    section5NatFlatten_partition Q _ L T hQpart fun i =>
      section5NatTransport_partition (Q i) (R i) (hQcells i).1 (hRpart i),
    fun j => ⟨section5NatTransport_isProper _ _ (hQcells (e.symm j).1).1
      (hRcells (e.symm j).1 (e.symm j).2).1, (hRcells (e.symm j).1 (e.symm j).2).2⟩,
    fun j => hTdiam (e.symm j).1 (e.symm j).2⟩

end LeanProofs.GowersSzemeredi
