import GowersSzemeredi.Proofs05Downstream
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Data.Fintype.EquivFin

/-!
# Global polynomial phase removal (Lemma 5.14)

This module assembles the local refinements constructed in
`Proofs05Downstream` over every cell of an input partition.  The dependent
families of local cells are flattened through a sigma type, and Jensen's
inequality supplies the sharp global cell-count exponent.

The final result remains conditional on `corollary_5_6`: that is precisely
the outstanding analytic input used by the local refinement theorem.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

/-! ### Flattening dependent families of refinements -/

/-- The canonical finite reindexing of a dependent family of finite types. -/
noncomputable def section5FlattenEquiv {M : Nat} (L : Fin M → Nat) :
    (Σ i : Fin M, Fin (L i)) ≃ Fin (∑ i, L i) :=
  Fintype.equivFinOfCardEq (by simp)

/-- Flatten a dependent family of modular progressions to one `Fin`-indexed
family, without adding any padding cells. -/
noncomputable def section5Flatten {N M : Nat} (L : Fin M → Nat)
    (R : (i : Fin M) → Fin (L i) → ModAP N) :
    Fin (∑ i, L i) → ModAP N := fun j =>
  let z := (section5FlattenEquiv L).symm j
  R z.1 z.2

private theorem section5_sigma_partition {X : Type*} [DecidableEq X]
    {M : Nat} (L : Fin M → Nat) (A : Fin M → Finset X) (S : Finset X)
    (B : (i : Fin M) → Fin (L i) → Finset X)
    (hA : IsPartition A S) (hB : ∀ i, IsPartition (B i) (A i)) :
    (forall x, x ∈ S ↔ exists z : Σ i : Fin M, Fin (L i), x ∈ B z.1 z.2) ∧
      forall z w : Σ i : Fin M, Fin (L i), z != w →
        Disjoint (B z.1 z.2) (B w.1 w.2) := by
  constructor
  · intro x
    rw [hA.1]
    constructor
    · rintro ⟨i, hi⟩
      obtain ⟨j, hj⟩ := (hB i).1 x |>.mp hi
      exact ⟨⟨i, j⟩, hj⟩
    · rintro ⟨⟨i, j⟩, hij⟩
      exact ⟨i, (hB i).1 x |>.mpr ⟨j, hij⟩⟩
  · intro z w hzw
    have hzw' : z ≠ w := bne_iff_ne.mp hzw
    by_cases hi : z.1 = w.1
    · rcases z with ⟨i, j⟩
      rcases w with ⟨i', j'⟩
      dsimp only at hi ⊢
      subst i'
      have hj : j ≠ j' := by
        intro h
        subst j'
        exact hzw' rfl
      exact (hB i).2 j j' (bne_iff_ne.mpr hj)
    · exact Disjoint.mono (IsPartition.cell_subset (hB z.1) z.2)
        (IsPartition.cell_subset (hB w.1) w.2)
        (hA.2 z.1 w.1 (bne_iff_ne.mpr hi))

/-- Flattening local partitions gives a partition of the original union. -/
theorem section5Flatten_partition {N M : Nat} [NeZero N]
    (Q : Fin M → ModAP N)
    (L : Fin M → Nat) (R : (i : Fin M) → Fin (L i) → ModAP N)
    (hQ : IsPartition (fun i ↦ (Q i).carrier) Finset.univ)
    (hR : ∀ i, IsPartition (fun j ↦ (R i j).carrier) (Q i).carrier) :
    IsPartition (fun j ↦ (section5Flatten L R j).carrier) Finset.univ := by
  classical
  let e := section5FlattenEquiv L
  have hsigma := section5_sigma_partition L (fun i ↦ (Q i).carrier)
    Finset.univ (fun i j ↦ (R i j).carrier) hQ hR
  constructor
  · intro x
    rw [hsigma.1 x]
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨e z, ?_⟩
      change x ∈
        (R ((section5FlattenEquiv L).symm (section5FlattenEquiv L z)).1
          ((section5FlattenEquiv L).symm (section5FlattenEquiv L z)).2).carrier
      rw [(section5FlattenEquiv L).symm_apply_apply z]
      exact hz
    · rintro ⟨j, hj⟩
      refine ⟨e.symm j, ?_⟩
      simpa only [section5Flatten, e] using hj
  · intro i j hij
    have hij' : i ≠ j := bne_iff_ne.mp hij
    have hpre : e.symm i ≠ e.symm j := fun h => hij' (e.symm.injective h)
    simpa only [section5Flatten, e] using
      hsigma.2 (e.symm i) (e.symm j) (bne_iff_ne.mpr hpre)

/-- The flattened partition refines the original family cell by cell. -/
theorem section5Flatten_refinement {N M : Nat} [NeZero N]
    (Q : Fin M → ModAP N)
    (L : Fin M → Nat) (R : (i : Fin M) → Fin (L i) → ModAP N)
    (hQ : IsPartition (fun i ↦ (Q i).carrier) Finset.univ)
    (hR : ∀ i, IsPartition (fun j ↦ (R i j).carrier) (Q i).carrier) :
    IsRefinement (fun j ↦ (section5Flatten L R j).carrier)
      (fun i ↦ (Q i).carrier) := by
  classical
  have hflat := section5Flatten_partition Q L R hQ hR
  refine ⟨fun x ↦ (hflat.1 x).symm.trans (hQ.1 x), ?_, hflat.2⟩
  intro j
  let z := (section5FlattenEquiv L).symm j
  refine ⟨z.1, ?_⟩
  simpa only [section5Flatten, z] using
    (IsPartition.cell_subset (hR z.1) z.2)

/-- Properness is preserved by dependent-family flattening. -/
theorem section5Flatten_isProper {N M : Nat} (L : Fin M → Nat)
    (R : (i : Fin M) → Fin (L i) → ModAP N)
    (hR : ∀ i j, (R i j).IsProper) :
    ∀ j, (section5Flatten L R j).IsProper := by
  intro j
  let z := (section5FlattenEquiv L).symm j
  simpa only [section5Flatten, z] using hR z.1 z.2

/-- Sums over a flattened family are the corresponding iterated sums. -/
theorem section5Flatten_sum {N M : Nat} (L : Fin M → Nat)
    (R : (i : Fin M) → Fin (L i) → ModAP N)
    {A : Type*} [AddCommMonoid A] (F : ModAP N → A) :
    ∑ j, F (section5Flatten L R j) = ∑ i, ∑ j, F (R i j) := by
  classical
  let e := section5FlattenEquiv L
  calc
    ∑ j, F (section5Flatten L R j) =
        ∑ z : Σ i : Fin M, Fin (L i), F (section5Flatten L R (e z)) :=
      (e.sum_comp _).symm
    _ = ∑ z : Σ i : Fin M, Fin (L i), F (R z.1 z.2) := by
      apply Finset.sum_congr rfl
      intro z _hz
      change F (R ((section5FlattenEquiv L).symm
        (section5FlattenEquiv L z)).1
        ((section5FlattenEquiv L).symm (section5FlattenEquiv L z)).2) =
          F (R z.1 z.2)
      exact congrArg (fun w : Σ i : Fin M, Fin (L i) ↦ F (R w.1 w.2))
        ((section5FlattenEquiv L).symm_apply_apply z)
    _ = ∑ i, ∑ j, F (R i j) := Fintype.sum_sigma _

/-! ### The global cell-count estimate -/

/-- Jensen's inequality in exactly the form needed to aggregate local cell
counts. -/
theorem section5_sum_rpow_le {M N K : Nat} (hM : 0 < M) (hK : 0 < K)
    (m : Fin M → Nat) (hsum : ∑ i, m i = N) :
    ∑ i, (m i : Real) ^ (1 - (K : Real)⁻¹) ≤
      (M : Real) ^ (K : Real)⁻¹ *
        (N : Real) ^ (1 - (K : Real)⁻¹) := by
  classical
  let q : Real := (K : Real)⁻¹
  let p : Real := 1 - q
  have hKreal : (0 : Real) < K := by exact_mod_cast hK
  have hKone : (1 : Real) ≤ K := by exact_mod_cast hK
  have hq0 : 0 ≤ q := (inv_pos.mpr hKreal).le
  have hq1 : q ≤ 1 := by
    exact inv_le_one_of_one_le₀ hKone
  have hp0 : 0 ≤ p := by dsimp only [p]; linarith
  have hp1 : p ≤ 1 := by dsimp only [p]; linarith
  have hMreal : (0 : Real) < M := by exact_mod_cast hM
  have hweights : ∑ _i : Fin M, (M : Real)⁻¹ = 1 := by
    simp [ne_of_gt hMreal]
  have hsumReal : ∑ i, (m i : Real) = (N : Real) := by
    exact_mod_cast hsum
  have hjensen := (Real.concaveOn_rpow hp0 hp1).le_map_sum
    (t := (Finset.univ : Finset (Fin M)))
    (w := fun _i : Fin M ↦ (M : Real)⁻¹)
    (p := fun i : Fin M ↦ (m i : Real))
    (fun _i _hi ↦ (inv_pos.mpr hMreal).le) hweights
    (fun i _hi ↦ (show (0 : Real) ≤ m i by positivity))
  have hjensen' :
      (M : Real)⁻¹ * ∑ i, (m i : Real) ^ p ≤
        ((M : Real)⁻¹ * (N : Real)) ^ p := by
    simpa only [smul_eq_mul, Function.comp_apply, ← Finset.mul_sum, hsumReal]
      using hjensen
  have hscaled :
      ∑ i, (m i : Real) ^ p ≤
        (M : Real) * ((M : Real)⁻¹ * (N : Real)) ^ p := by
    calc
      ∑ i, (m i : Real) ^ p =
          (M : Real) * ((M : Real)⁻¹ * ∑ i, (m i : Real) ^ p) := by
        field_simp
      _ ≤ (M : Real) * ((M : Real)⁻¹ * (N : Real)) ^ p :=
        mul_le_mul_of_nonneg_left hjensen' hMreal.le
  calc
    ∑ i, (m i : Real) ^ (1 - (K : Real)⁻¹) =
        ∑ i, (m i : Real) ^ p := by rfl
    _ ≤ (M : Real) * ((M : Real)⁻¹ * (N : Real)) ^ p := hscaled
    _ = (M : Real) ^ q * (N : Real) ^ p := by
      rw [Real.mul_rpow (inv_nonneg.mpr hMreal.le)
        (show (0 : Real) ≤ N by positivity), Real.inv_rpow hMreal.le]
      have hMpow :
          (M : Real) * ((M : Real) ^ p)⁻¹ = (M : Real) ^ q := by
        calc
          (M : Real) * ((M : Real) ^ p)⁻¹ =
              (M : Real) ^ (1 : Real) * (M : Real) ^ (-p) := by
            rw [Real.rpow_one, Real.rpow_neg hMreal.le]
          _ = (M : Real) ^ ((1 : Real) + (-p)) :=
            (Real.rpow_add hMreal 1 (-p)).symm
          _ = (M : Real) ^ q := by
            congr 1
            dsimp only [p, q]
            ring
      calc
        (M : Real) * (((M : Real) ^ p)⁻¹ * (N : Real) ^ p) =
            ((M : Real) * ((M : Real) ^ p)⁻¹) * (N : Real) ^ p := by
          ring
        _ = (M : Real) ^ q * (N : Real) ^ p := by rw [hMpow]
    _ = (M : Real) ^ (K : Real)⁻¹ *
        (N : Real) ^ (1 - (K : Real)⁻¹) := by rfl

/-! ### Lemma 5.14 -/

/-- Lemma 5.14 follows from the polynomial partition of Corollary 5.6.

The local additive error is summed over the input partition, while Jensen's
inequality turns the sum of local sublinear cell counts into the claimed
`M^(1/K) N^(1-1/K)` global bound. -/
theorem lemma_5_14_holds_of_corollary_5_6
    (h56 : corollary_5_6) : lemma_5_14 := by
  classical
  intro k alpha hk halpha
  refine ⟨section5LocalRefinementConstant k alpha,
    section5LocalRefinementConstant_pos k alpha, ?_⟩
  intro N M _inst phi f Q hphi hf hQ hphase
  have hM : 0 < M := by
    by_contra hMnot
    have hMzero : M = 0 := Nat.eq_zero_of_not_pos hMnot
    subst M
    obtain ⟨i, _hi⟩ := (hQ.1 (0 : ZMod N)).mp (Finset.mem_univ _)
    exact Fin.elim0 i
  have hdisc : DiscValued (fun s ↦ (f s : Complex)) := by
    intro s
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hf s
  choose L R hRpart hRproper hRcount hRerror using
    fun i : Fin M ↦
      section5_efficient_local_phase_refinement_arbitrary_of_corollary_5_6
        h56 (Q i) phi alpha hk hphi halpha
  refine ⟨∑ i, L i, section5Flatten L R,
    section5Flatten_refinement Q L R hQ hRpart,
    section5Flatten_isProper L R hRproper, ?_, ?_⟩
  · have hK : 0 < polynomialPartitionConstant k := by
      unfold polynomialPartitionConstant
      positivity
    have hcards : ∑ i, (Q i).carrier.card = N := by
      simpa only [Finset.card_univ, ZMod.card] using IsPartition.sum_card hQ
    have hjensen := section5_sum_rpow_le hM hK
      (fun i ↦ (Q i).carrier.card) hcards
    have hlocalCount :
        ((∑ i, L i : Nat) : Real) ≤
          section5LocalRefinementConstant k alpha *
            ∑ i, ((Q i).carrier.card : Real) ^
              (1 - (polynomialPartitionConstant k : Real)⁻¹) := by
      rw [Nat.cast_sum]
      calc
        ∑ i, (L i : Real) ≤
            ∑ i, section5LocalRefinementConstant k alpha *
              ((Q i).carrier.card : Real) ^
                (1 - (polynomialPartitionConstant k : Real)⁻¹) :=
          Finset.sum_le_sum fun i _hi ↦ hRcount i
        _ = section5LocalRefinementConstant k alpha *
            ∑ i, ((Q i).carrier.card : Real) ^
              (1 - (polynomialPartitionConstant k : Real)⁻¹) := by
          rw [Finset.mul_sum]
    calc
      ((∑ i, L i : Nat) : Real) ≤
          section5LocalRefinementConstant k alpha *
            ∑ i, ((Q i).carrier.card : Real) ^
              (1 - (polynomialPartitionConstant k : Real)⁻¹) := hlocalCount
      _ ≤ section5LocalRefinementConstant k alpha *
          ((M : Real) ^ (polynomialPartitionConstant k : Real)⁻¹ *
            (N : Real) ^
              (1 - (polynomialPartitionConstant k : Real)⁻¹)) :=
        mul_le_mul_of_nonneg_left hjensen
          (section5LocalRefinementConstant_pos k alpha).le
      _ = section5LocalRefinementConstant k alpha *
            (M : Real) ^ (polynomialPartitionConstant k : Real)⁻¹ *
          (N : Real) ^
            (1 - (polynomialPartitionConstant k : Real)⁻¹) := by ring
  · have hnormReal (A : Finset (ZMod N)) :
        ‖∑ s ∈ A, (f s : Complex)‖ = |∑ s ∈ A, f s| := by
      rw [← Complex.ofReal_sum]
      simp only [Complex.norm_real, Real.norm_eq_abs]
    have hlocalError (i : Fin M) :
        ‖∑ s ∈ (Q i).carrier,
            (f s : Complex) * exponential (-(phi s))‖ ≤
          (∑ j, |∑ s ∈ (R i j).carrier, f s|) +
            alpha / 2 * (Q i).carrier.card := by
      simpa only [hnormReal] using hRerror i (fun s ↦ (f s : Complex)) hdisc
    have hcardsReal :
        ∑ i, ((Q i).carrier.card : Real) = (N : Real) := by
      have hcardsNat : ∑ i, (Q i).carrier.card = N := by
        simpa only [Finset.card_univ, ZMod.card] using IsPartition.sum_card hQ
      exact_mod_cast hcardsNat
    have hphaseUpper :
        ∑ i, ‖∑ s ∈ (Q i).carrier,
            (f s : Complex) * exponential (-(phi s))‖ ≤
          (∑ i, ∑ j, |∑ s ∈ (R i j).carrier, f s|) +
            alpha / 2 * N := by
      calc
        ∑ i, ‖∑ s ∈ (Q i).carrier,
              (f s : Complex) * exponential (-(phi s))‖ ≤
            ∑ i, ((∑ j, |∑ s ∈ (R i j).carrier, f s|) +
              alpha / 2 * (Q i).carrier.card) :=
          Finset.sum_le_sum fun i _hi ↦ hlocalError i
        _ = (∑ i, ∑ j, |∑ s ∈ (R i j).carrier, f s|) +
              alpha / 2 * N := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, hcardsReal]
    have hplain :
        (alpha / 2) * N ≤
          ∑ i, ∑ j, |∑ s ∈ (R i j).carrier, f s| := by
      nlinarith
    calc
      (alpha / 2) * N ≤
          ∑ i, ∑ j, |∑ s ∈ (R i j).carrier, f s| := hplain
      _ = ∑ j, |∑ s ∈ (section5Flatten L R j).carrier, f s| :=
        (section5Flatten_sum L R
          (fun P ↦ |∑ s ∈ P.carrier, f s|)).symm

end LeanProofs.GowersSzemeredi
