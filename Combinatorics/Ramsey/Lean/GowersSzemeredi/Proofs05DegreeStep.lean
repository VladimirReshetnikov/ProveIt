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
  classical
  obtain ⟨a, hdecompose⟩ := polynomialOn_affine_degree_drop phi hphi
  obtain ⟨p, hp, hp2, hrec⟩ :=
    lemma_5_5_square_root_auxiliary_holds (k + 1) r N (by omega)
      hthreshold.le hrN a
  have hpu : p * u ^ 2 ≤ r := by
    have hsquare : (p * u ^ 2) ^ 2 ≤ r ^ 2 := by
      calc
        (p * u ^ 2) ^ 2 = p ^ 2 * u ^ 4 := by ring
        _ ≤ r * r := Nat.mul_le_mul hp2 hu4
        _ = r ^ 2 := by ring
    nlinarith
  obtain ⟨m, Q, hm, hQpart, hQcells, hQstep⟩ :=
    section5_residue_target_partition r p u (by omega) hu hpu
  choose psi hpsi hidentity using
    fun i : Fin m => hdecompose ((Q i).start : ZMod N) (p : ZMod N)
  have hQN (i : Fin m) : (Q i).length ≤ N := by
    calc
      (Q i).length = (Q i).carrier.card := (hQcells i).1.2.symm
      _ ≤ (Finset.range r).card := Finset.card_le_card (IsPartition.cell_subset hQpart i)
      _ = r := Finset.card_range r
      _ ≤ N := hrN
  choose L R hL hRpart hRcells hRdiam using fun i : Fin m =>
    hprev N (Q i).length v (psi i) (hpsi i)
      (hscale (Q i).length (hQcells i).2.2).1 (hQN i) hv
      (hscale (Q i).length (hQcells i).2.2).2.1
  let T (i : Fin m) (j : Fin (L i)) := section5NatTransport (Q i) (R i j)
  have hTpart (i : Fin m) : IsNatAPPartition (T i) (Q i).carrier :=
    section5NatTransport_partition (Q i) (R i) (hQcells i).1 (hRpart i)
  have hTcells (i : Fin m) (j : Fin (L i)) :
      (T i j).IsProper ∧ 0 < (T i j).length ∧
        ((T i j).length = v - 1 ∨ (T i j).length = v) :=
    ⟨section5NatTransport_isProper (Q i) (R i j) (hQcells i).1 (hRcells i j).1,
      (hRcells i j).2⟩
  have hTdiam (i : Fin m) (j : Fin (L i)) :
      diameterAtMostReal ((T i j).carrier.image fun x : Nat => phi (x : ZMod N))
        ((r : Real) ^ (-(2 * (polynomialPartitionConstant (k + 1) : Real)⁻¹)) * N) := by
    let b : ZMod N := a * (p : ZMod N) ^ (k + 1)
    have hrec' : (centeredAbs b : Real) ≤
        (r : Real) ^ (-(((k + 1 : Nat) : Real) * (2 : Real) ^ (k + 1 + 1))⁻¹) * N := by
      simpa only [b, mul_comm] using hrec
    have hsubset : (R i j).carrier ⊆ Finset.range u := by
      apply (IsPartition.cell_subset (hRpart i) j).trans
      apply Finset.range_mono
      rcases (hQcells i).2.2 with h | h <;> omega
    have hmono : diameterAtMostReal
        ((R i j).carrier.image fun t : Nat => b * (t : ZMod N) ^ (k + 1))
        (polynomialDegreeStepError r u (k + 1) * N) := by
      refine ⟨u ^ (k + 1) * centeredAbs b,
        diameterAtMost_monomial (R i j).carrier hsubset b, ?_⟩
      have h := mul_le_mul_of_nonneg_left hrec' (by positivity : (0 : Real) ≤ (u : Real) ^ (k + 1))
      simpa only [Nat.cast_mul, Nat.cast_pow, polynomialDegreeStepError, mul_assoc] using h
    have hsum := diameterAtMostReal_add_image (R i j).carrier
      (fun t : Nat => b * (t : ZMod N) ^ (k + 1)) (fun t : Nat => psi i (t : ZMod N))
      hmono (hRdiam i j)
    have himage : (T i j).carrier.image (fun x : Nat => phi (x : ZMod N)) =
        (R i j).carrier.image (fun t : Nat => b * (t : ZMod N) ^ (k + 1) + psi i (t : ZMod N)) := by
      rw [show T i j = section5NatTransport (Q i) (R i j) from rfl,
        section5NatTransport_carrier, Finset.image_image]
      apply Finset.image_congr
      intro t _
      change phi (section5NatIndexPoint (Q i) t : ZMod N) =
        b * (t : ZMod N) ^ (k + 1) + psi i (t : ZMod N)
      rw [section5NatIndexPoint_cast, hQstep, hidentity]
    rw [himage]
    obtain ⟨d, hd, hds⟩ := hsum
    refine ⟨d, hd, hds.trans ?_⟩
    simpa only [add_mul] using mul_le_mul_of_nonneg_right
      (hscale (Q i).length (hQcells i).2.2).2.2 (Nat.cast_nonneg N)
  have hsumL : 0 < ∑ i, L i := by
    let i : Fin m := ⟨0, hm⟩
    exact (hL i).trans_le (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i))
  refine ⟨∑ i, L i, section5NatFlatten L T, hsumL,
    section5NatFlatten_partition Q _ L T hQpart hTpart, ?_, ?_⟩
  · intro j
    let z := (section5NatFlattenEquiv L).symm j
    exact hTcells z.1 z.2
  · intro j
    let z := (section5NatFlattenEquiv L).symm j
    exact hTdiam z.1 z.2

end LeanProofs.GowersSzemeredi
