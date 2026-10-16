import GowersSzemeredi.Section05

/-!
# Audit of simultaneous polynomial partitioning (Lemma 5.9)

This file isolates the part of Lemma 5.9 which follows directly from the
live target-length Corollary 5.6 and audits the rounding budget in the
refinement induction.

For one polynomial, the stronger target-length hypothesis in Lemma 5.9 is
more than enough, so the desired conclusion follows from Corollary 5.6.  For
two or more polynomials, a Corollary 5.6 cell is allowed to have length one
less than its target.  The repaired live threshold
`(2 * polynomialPartitionThreshold k)^(K^(q-1))` leaves the required integral
margin; the recursive domination theorem below verifies that budget without
unfolding the enormous one-polynomial threshold.

The arithmetic lemmas below also verify the extra diameter slack present in
the degree-induction calculation for `k >= 2`.  That slack does not remove
the independent threshold obstruction, and for `k = 1` it is absent.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

/-! ## Strong one-polynomial input -/

/-- The stronger one-polynomial API suggested by the actual exponent in the
degree-induction proof.  A separate linear argument is needed to establish
this uniformly at `k = 1`; it is intentionally an explicit hypothesis here. -/
def corollary_5_6_strong_diameter : Prop :=
  forall (N k r v : Nat) [NeZero N] (phi : ZMod N -> ZMod N),
    1 <= k -> PolynomialOn k Finset.univ phi ->
    polynomialPartitionThreshold k < r -> r <= N ->
    1 <= v -> (v : Real) <=
      (r : Real) ^ (polynomialPartitionConstant k : Real)⁻¹ ->
      exists M : Nat, exists P : Fin M -> NatAP,
        0 < M /\ IsNatAPPartition P (Finset.range r) /\
        (forall j, (P j).IsProper /\ 0 < (P j).length /\
          ((P j).length = v - 1 \/ (P j).length = v)) /\
        forall j, diameterAtMostReal
          ((P j).carrier.image fun x : Nat => phi (x : ZMod N))
          ((r : Real) ^
            (-(2 * (polynomialPartitionConstant k : Real)⁻¹)) * N)

/-- The strong diameter API contains the live Corollary 5.6 statement. -/
theorem corollary_5_6_holds_of_strong_diameter
    (hstrong : corollary_5_6_strong_diameter) : corollary_5_6 := by
  intro N k r v _ phi hk hphi hthreshold hrN hv hvupper
  obtain ⟨M, P, hM, hpartition, hcells, hdiameter⟩ :=
    hstrong N k r v phi hk hphi hthreshold hrN hv hvupper
  refine ⟨M, P, hM, hpartition, hcells, ?_⟩
  intro j
  obtain ⟨d, hd, hdscale⟩ := hdiameter j
  refine ⟨d, hd, hdscale.trans ?_⟩
  have hrOneNat : 1 <= r := by
    have hTPos : 0 < polynomialPartitionThreshold k := by
      unfold polynomialPartitionThreshold weylThreshold
      exact pow_pos (pow_pos (by norm_num) _) _
    omega
  have hrOne : (1 : Real) <= r := by exact_mod_cast hrOneNat
  have hexponent :
      -(2 * (polynomialPartitionConstant k : Real)⁻¹) <=
        -(polynomialPartitionConstant k : Real)⁻¹ := by
    have hKInv : 0 <= (polynomialPartitionConstant k : Real)⁻¹ := by positivity
    linarith
  have hscale :
      (r : Real) ^ (-(2 * (polynomialPartitionConstant k : Real)⁻¹)) <=
        (r : Real) ^ (-(polynomialPartitionConstant k : Real)⁻¹) :=
    Real.rpow_le_rpow_of_exponent_le hrOne hexponent
  exact mul_le_mul_of_nonneg_right hscale (by positivity)

/-! ## The exact one-polynomial case -/

/-- The specialization of the live Lemma 5.9 statement to one polynomial. -/
def lemma_5_9_one_polynomial : Prop :=
  forall (N k r v : Nat) [NeZero N]
      (phi : Fin 1 -> ZMod N -> ZMod N),
    1 <= k -> (forall i, PolynomialOn k Finset.univ (phi i)) ->
    simultaneousPolynomialThreshold k 1 < r -> r <= N ->
    1 <= v -> (v : Real) <= (r : Real) ^
      (2 * (polynomialPartitionConstant k : Real) ^ (1 : Nat))⁻¹ ->
      exists M : Nat, exists P : Fin M -> NatAP,
        0 < M /\ IsNatAPPartition P (Finset.range r) /\
        (forall j, (P j).IsProper /\ 0 < (P j).length /\
          ((P j).length = v - 1 \/ (P j).length = v)) /\
        forall i j, diameterAtMostReal
          ((P j).carrier.image fun x : Nat => phi i (x : ZMod N))
          ((r : Real) ^
            (-((polynomialPartitionConstant k : Real) ^ (1 : Nat))⁻¹) * N)

/-- Corollary 5.6 proves the `q = 1` specialization of Lemma 5.9. -/
theorem lemma_5_9_one_polynomial_holds_of_corollary_5_6
    (h56 : corollary_5_6) : lemma_5_9_one_polynomial := by
  unfold lemma_5_9_one_polynomial
  intro N k r v _ phi hk hphi hthreshold hrN hv hvupper
  have hKPos : (0 : Real) < polynomialPartitionConstant k := by
    unfold polynomialPartitionConstant
    positivity
  have hrOneNat : 1 <= r := by
    have hTPos : 0 < polynomialPartitionThreshold k := by
      unfold polynomialPartitionThreshold weylThreshold
      exact pow_pos (pow_pos (by norm_num) _) _
    have hthreshold' :
        2 * polynomialPartitionThreshold k < r := by
      simpa only [simultaneousPolynomialThreshold, Nat.sub_self, pow_zero,
        pow_one] using hthreshold
    omega
  have hrOne : (1 : Real) <= r := by exact_mod_cast hrOneNat
  have hexponent :
      (2 * (polynomialPartitionConstant k : Real))⁻¹ <=
        (polynomialPartitionConstant k : Real)⁻¹ := by
    apply (inv_le_inv₀ (by positivity) hKPos).2
    nlinarith
  have hvupper56 :
      (v : Real) <=
        (r : Real) ^ (polynomialPartitionConstant k : Real)⁻¹ := by
    calc
      (v : Real) <= (r : Real) ^
          (2 * (polynomialPartitionConstant k : Real))⁻¹ := by
        simpa only [pow_one] using hvupper
      _ <= (r : Real) ^ (polynomialPartitionConstant k : Real)⁻¹ :=
        Real.rpow_le_rpow_of_exponent_le hrOne hexponent
  have hthreshold56 : polynomialPartitionThreshold k < r := by
    have hthreshold' :
        2 * polynomialPartitionThreshold k < r := by
      simpa only [simultaneousPolynomialThreshold, Nat.sub_self, pow_zero,
        pow_one] using hthreshold
    omega
  obtain ⟨M, P, hM, hpartition, hcells, hdiameter⟩ :=
    h56 N k r v (phi 0) hk (hphi 0) hthreshold56 hrN hv hvupper56
  refine ⟨M, P, hM, hpartition, hcells, ?_⟩
  intro i j
  have hi : i = 0 := Fin.eq_zero i
  subst i
  simpa only [pow_one] using hdiameter j

/-! ## Diameter slack in the degree-induction calculation -/

/-! ## The threshold-rounding budget -/

private theorem pow_add_exponent_le_add_one_pow (T K : Nat) (hT : 1 <= T) :
    T ^ K + K <= (T + 1) ^ K := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [pow_succ, pow_succ]
      calc
        T ^ K * T + (K + 1) <= (T ^ K + K) * (T + 1) := by
          have hpow : 1 <= T ^ K := one_le_pow₀ hT
          nlinarith
        _ <= (T + 1) ^ K * (T + 1) :=
          Nat.mul_le_mul_right (T + 1) ih

/-- The exact recursive threshold needed to survive the possible `u - 1`
cell at each successive refinement.  The argument is deliberately abstract
in the one-polynomial threshold and the partition constant. -/
def polynomialPartitionIteratedRoundingThreshold (T K : Nat) : Nat -> Nat
  | 0 => T
  | n + 1 => (polynomialPartitionIteratedRoundingThreshold T K n + 2) ^ K

/-- The convenient closed threshold `(2*T)^(K^n)` dominates the recursive
rounding-safe threshold.  The `+3` margin is preserved because increasing a
positive base by one increases its `K`-th power by at least `K`. -/
theorem polynomialPartitionIteratedRoundingThreshold_le
    (T K n : Nat) (hT : 3 <= T) (hK : 3 <= K) :
    polynomialPartitionIteratedRoundingThreshold T K n + 3 <=
      (2 * T) ^ (K ^ n) := by
  induction n with
  | zero =>
      simp only [polynomialPartitionIteratedRoundingThreshold, pow_zero,
        pow_one]
      omega
  | succ n ih =>
      let S := polynomialPartitionIteratedRoundingThreshold T K n
      let B := (2 * T) ^ (K ^ n)
      have hSOne : 1 <= S + 2 := by omega
      have hgap : (S + 2) ^ K + 3 <= (S + 3) ^ K := by
        exact (Nat.add_le_add_left hK ((S + 2) ^ K)).trans
          (pow_add_exponent_le_add_one_pow (S + 2) K hSOne)
      have hbase : (S + 3) ^ K <= B ^ K :=
        pow_le_pow_left₀ (by omega) ih K
      calc
        polynomialPartitionIteratedRoundingThreshold T K (n + 1) + 3 =
            (S + 2) ^ K + 3 := rfl
        _ <= (S + 3) ^ K := hgap
        _ <= B ^ K := hbase
        _ = (2 * T) ^ (K ^ (n + 1)) := by
          dsimp only [B]
          rw [← pow_mul, pow_succ]

/-- The closed repaired threshold dominates the exact recursive
applicability budget for `q - 1` refinements. -/
theorem polynomialPartitionIteratedRoundingThreshold_le_roundingSafe
    (k q : Nat) (hT : 3 <= polynomialPartitionThreshold k)
    (hK : 3 <= polynomialPartitionConstant k) :
    polynomialPartitionIteratedRoundingThreshold
        (polynomialPartitionThreshold k) (polynomialPartitionConstant k)
        (q - 1) + 3 <=
      simultaneousPolynomialThreshold k q := by
  unfold simultaneousPolynomialThreshold
  exact polynomialPartitionIteratedRoundingThreshold_le
    (polynomialPartitionThreshold k) (polynomialPartitionConstant k)
    (q - 1) hT hK

/-- At `r = T^K + 1`, the unrepaired ideal-root threshold `T^K < r` holds,
but no
integer target `u >= T+1` can satisfy `u^K <= r`.  Such a target is exactly
the weakest conceivable rounding margin; the next strict Corollary 5.6 call
actually needs the still stronger `u >= T+2`. -/
theorem polynomialPartition_rounding_threshold_gap
    (T K : Nat) (hT : 1 <= T) (hK : 2 <= K) :
    T ^ K < T ^ K + 1 /\
      ¬ exists u : Nat, T + 1 <= u /\ u ^ K <= T ^ K + 1 := by
  refine ⟨Nat.lt_add_one _, ?_⟩
  rintro ⟨u, hu, hupow⟩
  have hbase : (T + 1) ^ K <= u ^ K :=
    pow_le_pow_left₀ (by omega) hu K
  have hgap : T ^ K + 1 < (T + 1) ^ K := by
    have htwo : T ^ K + 2 <= (T + 1) ^ K := by
      exact (Nat.add_le_add_left hK (T ^ K)).trans
        (pow_add_exponent_le_add_one_pow T K hT)
    omega
  omega

end LeanProofs.GowersSzemeredi
