import GowersSzemeredi.Proofs16BaseCaseCoarsePartition
import GowersSzemeredi.Proofs16BaseCaseQuantitative

/-!
# The short-box graph cover for Lemma 16.3

This module combines the proper coarse partition with the numerical slack from
the one-dimensional base case.  On a box below the Corollary 7.11 threshold,
the graph of an arbitrary function is covered cellwise by constant multilinear
maps while preserving the repaired proper-box requirements.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi.BaseCase

lemma lemma163_coarse_square_le_graphBound {gamma theta eta : Real}
    {q : Nat} (hgamma : 0 < gamma) (hgammaOne : gamma ≤ 1)
    (htheta : 0 < theta) (hthetaOne : theta ≤ 1)
    (heta : 0 < eta) (hetaOne : eta ≤ 1) (hq : 0 < q)
    (hqBound : (q : Real) * lemma163Alpha gamma theta ≤
      gamma ^ (-(2 : Int))) :
    ((lemma163CoarseCellLength eta ^ 2 : Nat) : Real) ≤
      lemma163LocalGraphBound gamma theta eta q := by
  have hg := (lemma163_local_bounds hgamma hgammaOne htheta hthetaOne
    heta hetaOne hq hqBound).2.2
  have hceil : (lemma163CoarseCellLength eta : Real) < 4096 / eta + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hinv : 1 ≤ eta⁻¹ := by
    simpa using (inv_le_inv₀ (by norm_num : (0 : Real) < 1) heta).2 hetaOne
  have hm : (lemma163CoarseCellLength eta : Real) ≤ 4097 * eta⁻¹ := by
    rw [div_eq_mul_inv] at hceil
    nlinarith
  have hmSq : ((lemma163CoarseCellLength eta ^ 2 : Nat) : Real) ≤
      (2 : Real) ^ (26 : Nat) * eta ^ (-(2 : Int)) := by
    push_cast
    rw [zpow_neg, zpow_ofNat, ← inv_pow]
    calc
      (lemma163CoarseCellLength eta : Real) ^ 2 ≤
          (4097 * eta⁻¹) ^ 2 := by gcongr
      _ ≤ (2 : Real) ^ (26 : Nat) * eta⁻¹ ^ 2 := by
        ring_nf
        gcongr
        norm_num
  have hpow : (2 : Real) ^ (26 : Nat) ≤ 2 ^ (512 : Nat) :=
    pow_le_pow_right₀ (by norm_num) (by norm_num)
  exact hmSq.trans ((mul_le_mul_of_nonneg_right hpow
    (by positivity : 0 ≤ eta ^ (-(2 : Int)))).trans hg)

lemma lemma163_width_le_coarse {gamma theta eta : Real} {q : Nat}
    (hgamma : 0 < gamma) (hgammaOne : gamma ≤ 1)
    (htheta : 0 < theta) (hthetaOne : theta ≤ 1)
    (heta : 0 < eta) (hetaOne : eta ≤ 1) (hq : 0 < q)
    (hqBound : (q : Real) * lemma163Alpha gamma theta ≤
      gamma ^ (-(2 : Int))) (L : Nat) (hL : 1 ≤ L)
    (hsmall : ¬ 1024 * Real.pi / eta <
      (L : Real) ^ lemma163CorollaryExponent eta) :
    (L : Real) ^ lemma163LocalExponent gamma theta eta q ≤
      lemma163CoarseCellLength eta := by
  have hw := lemma163_exponent_le_corollary_half hgamma hgammaOne htheta
    hthetaOne heta hetaOne hq hqBound
  have hExpNonneg : 0 ≤ lemma163LocalExponent gamma theta eta q :=
    (lemma163_local_bounds hgamma hgammaOne htheta hthetaOne
      heta hetaOne hq hqBound).1.le
  have hbase : (1 : Real) ≤ L := by exact_mod_cast hL
  have hpow :
      (L : Real) ^ lemma163LocalExponent gamma theta eta q ≤
        (L : Real) ^ lemma163CorollaryExponent eta := by
    apply Real.rpow_le_rpow_of_exponent_le hbase
    have haPos : 0 < lemma163CorollaryExponent eta := by
      unfold lemma163CorollaryExponent
      positivity
    linarith
  have hthreshold :
      (L : Real) ^ lemma163CorollaryExponent eta ≤ 1024 * Real.pi / eta :=
    le_of_not_gt hsmall
  have hpi : Real.pi ≤ 4 := Real.pi_le_four
  have hceil : 4096 / eta ≤ (lemma163CoarseCellLength eta : Real) :=
    Nat.le_ceil (4096 / eta)
  calc
    (L : Real) ^ lemma163LocalExponent gamma theta eta q ≤
        (L : Real) ^ lemma163CorollaryExponent eta := hpow
    _ ≤ 1024 * Real.pi / eta := hthreshold
    _ ≤ 4096 / eta := by
      apply (div_le_div_iff₀ heta heta).2
      nlinarith
    _ ≤ lemma163CoarseCellLength eta := hceil

lemma section16_coarse_graph_cover {N : Nat} [NeZero N]
    (gamma theta eta : Real) {q : Nat}
    (hgamma : 0 < gamma) (hgammaOne : gamma ≤ 1)
    (htheta : 0 < theta) (hthetaOne : theta ≤ 1)
    (heta : 0 < eta) (hetaOne : eta ≤ 1) (hq : 0 < q)
    (hqBound : (q : Real) * lemma163Alpha gamma theta ≤
      gamma ^ (-(2 : Int))) (B : Finset (Point N 1))
    (phi : Point N 1 → ZMod N) (P : Box N 1) (hP : P.IsProper)
    (hsmall : ¬ 1024 * Real.pi / eta <
      (P.width : Real) ^ lemma163CorollaryExponent eta) :
    ∃ M n : Nat, ∃ H : Finset (Point N 1),
      ∃ Q : Fin M → Box N 1,
        ∃ mu : Fin M → Fin n → Point N 1 → ZMod N,
          H ⊆ P.carrier ∧ (1 - eta) * P.carrier.card ≤ H.card ∧
          IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper) ∧
          (n : Real) ≤ lemma163LocalGraphBound gamma theta eta q ∧
          (∀ j, (P.width : Real) ^
              lemma163LocalExponent gamma theta eta q ≤ (Q j).width) ∧
          (∀ j i, IsMultilinear (mu j i)) ∧
          ∀ j x, x ∈ (Q j).carrier → x ∈ H → ∀ y,
            (x, y) ∈ partialGraph B phi → ∃ i, y = mu j i x := by
  classical
  by_cases hLzero : P.width = 0
  · have hcarrier : P.carrier = ∅ := by
      have hc := boxOne_card_eq_width P hP
      rw [hLzero] at hc
      exact Finset.card_eq_zero.mp hc
    refine ⟨1, 0, ∅, (fun _ : Fin 1 => P), (fun _ i => Fin.elim0 i),
      (by simp), (by simp [hcarrier]), ?_, (by simpa using hP), ?_, ?_, ?_, ?_⟩
    · constructor
      · intro x
        simp [hcarrier]
      · intro i j hij
        exact ((bne_iff_ne.mp hij) (Subsingleton.elim i j)).elim
    · have := (lemma163_local_bounds hgamma hgammaOne htheta hthetaOne
          heta hetaOne hq hqBound).2.2
      have hnonneg : (0 : Real) ≤ lemma163LocalGraphBound gamma theta eta q :=
        (by positivity : (0 : Real) ≤
          (2 : Real) ^ (512 : Nat) * eta ^ (-(2 : Int))).trans this
      simpa only [Nat.cast_zero] using hnonneg
    · intro j
      have hwPos := (lemma163_local_bounds hgamma hgammaOne htheta hthetaOne
        heta hetaOne hq hqBound).1
      simpa only [hLzero, Nat.cast_zero, Real.zero_rpow hwPos.ne'] using
        (le_rfl : (0 : Real) ≤ 0)
    · intro j i
      exact Fin.elim0 i
    · intro j x hxQ hxH
      simp at hxH
  have hL : 1 ≤ P.width := Nat.one_le_iff_ne_zero.mpr hLzero
  let m := lemma163CoarseCellLength eta
  have hm : 0 < m := by
    apply Nat.ceil_pos.mpr
    positivity
  have hwidthSelf : (P.width : Real) ^
      lemma163LocalExponent gamma theta eta q ≤ P.width := by
    have hbase : (1 : Real) ≤ P.width := by exact_mod_cast hL
    apply Real.rpow_le_self_of_one_le hbase
    have hw := lemma163_exponent_le_corollary_half hgamma hgammaOne htheta
      hthetaOne heta hetaOne hq hqBound
    have ha : lemma163CorollaryExponent eta ≤ 1 := by
      unfold lemma163CorollaryExponent
      have hetaSq : eta ^ (2 : Nat) ≤ 1 := pow_le_one₀ heta.le hetaOne
      have hcoef : (2 : Real) ^ (-(14 : Real)) ≤ 1 := by
        calc
          (2 : Real) ^ (-(14 : Real)) ≤ (2 : Real) ^ (0 : Real) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 1 := by simp
      calc
        (2 : Real) ^ (-(14 : Real)) * eta ^ (2 : Nat) ≤ 1 * 1 :=
          mul_le_mul hcoef hetaSq (sq_nonneg eta) (by norm_num)
        _ = 1 := by norm_num
    linarith
  by_cases hLm : m * m ≤ P.width
  · let M := P.width / m
    let Q : Fin M → Box N 1 := fun j => coarseChildBox P m j
    let n := 2 * m
    let mu : Fin M → Fin n → Point N 1 → ZMod N := fun j a _ =>
      if ha : (a : Nat) < coarseChunkLength m (P.width % m) j then
        phi (boxOnePoint P (coarseChunkStart m (P.width % m) j + a))
      else 0
    refine ⟨M, n, P.carrier, Q, mu, Finset.Subset.rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hc : (0 : Real) ≤ P.carrier.card := by positivity
      nlinarith
    · exact coarseChildBox_partition P hP m hm hLm
    · intro j
      exact coarseChildBox_proper P hP m hm hLm j
    · exact lemma163_coarse_count_le_graphBound hgamma hgammaOne htheta
        hthetaOne heta hetaOne hq hqBound
    · intro j
      have hw := lemma163_width_le_coarse hgamma hgammaOne htheta hthetaOne
        heta hetaOne hq hqBound P.width hL hsmall
      exact hw.trans (by
        exact_mod_cast (coarseChunk_length_bounds (L := P.width) hm j).1)
    · intro j a
      unfold mu
      split_ifs <;> apply isMultilinear_const_one
    · intro j x hxQ hxH y hxy
      have hy := (mem_partialGraph_one B phi x y).1 hxy |>.2
      rw [coarseChildBox_carrier] at hxQ
      obtain ⟨i, _hi, hix⟩ := Finset.mem_image.mp hxQ
      have hlen := (coarseChunk_length_bounds (L := P.width) hm j).2
      let a : Fin n := ⟨i, by dsimp only [n]; omega⟩
      refine ⟨a, ?_⟩
      calc
        y = phi x := hy
        _ = phi (boxOnePoint P
            (coarseChunkStart m (P.width % m) j + i)) :=
          (congrArg phi hix).symm
        _ = mu j a x := by simp [mu, a, i.isLt]
  · let n := P.width
    let mu : Fin 1 → Fin n → Point N 1 → ZMod N :=
      fun _ i _ => phi (boxOnePoint P i)
    refine ⟨1, n, P.carrier, (fun _ : Fin 1 => P), mu,
      Finset.Subset.rfl, ?_, ?_, (by simpa using hP), ?_, ?_, ?_, ?_⟩
    · have hc : (0 : Real) ≤ P.carrier.card := by positivity
      nlinarith
    · constructor
      · intro x
        simp
      · intro i j hij
        exact ((bne_iff_ne.mp hij) (Subsingleton.elim i j)).elim
    · have hn : P.width ≤ m ^ 2 := by
        have : P.width ≤ m * m := (lt_of_not_ge hLm).le
        simpa [pow_two] using this
      calc
        (n : Real) = P.width := by rfl
        _ ≤ (m ^ 2 : Nat) := by exact_mod_cast hn
        _ ≤ lemma163LocalGraphBound gamma theta eta q :=
          lemma163_coarse_square_le_graphBound hgamma hgammaOne htheta
            hthetaOne heta hetaOne hq hqBound
    · intro j
      exact hwidthSelf
    · intro j i
      exact isMultilinear_const_one _
    · intro j x hxQ hxH y hxy
      have hy := (mem_partialGraph_one B phi x y).1 hxy |>.2
      rw [boxOne_carrier_eq_image] at hxQ
      obtain ⟨i, _hi, hix⟩ := Finset.mem_image.mp hxQ
      refine ⟨i, ?_⟩
      simpa [mu, hy] using (congrArg phi hix).symm

end LeanProofs.GowersSzemeredi.BaseCase
