import GowersSzemeredi.Proofs16BaseCaseCoarseCover
import GowersSzemeredi.Proofs16BaseCaseLongBoxCover

/-!
# One extracted Freiman graph in the repaired base case

This module combines the short- and long-box covers.  On each proper ambient
box, either the extracted graph has enough active indices for one of the two
covers, or deleting its sparse base projection already leaves the required
dense set.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi.BaseCase

/-- A single extracted Freiman graph is repaired multiply-linear for its share
of the global iteration budget. -/
lemma section16_freiman_graph_multiplyLinear {N : Nat} [NeZero N]
    (gamma theta : Real) {q : Nat}
    (hgamma : 0 < gamma) (hgammaOne : gamma ≤ 1)
    (htheta : 0 < theta) (hthetaOne : theta ≤ 1)
    (hq : 0 < q)
    (hqBound : (q : Real) * lemma163Alpha gamma theta ≤
      gamma ^ (-(2 : Int))) (Nprime : N.Prime)
    (B : Finset (Point N 1)) (phi : Point N 1 → ZMod N)
    (hfreiman : FreimanHom 8 (pointOneDomain B) (pointOneMap phi)) :
    ProperMultiplyLinear gamma (lemma163StageIteration gamma theta q)
      (partialGraph B phi) := by
  intro eta heta hetaOne P hP
  let A := boxOneIndexDomain P B
  by_cases hactive : eta * P.width ≤ A.card
  · by_cases hlarge : 1024 * Real.pi / eta <
        (P.width : Real) ^ lemma163CorollaryExponent eta
    · simpa [ProperMultiplyLinear, lemma163LocalExponent,
          lemma163LocalGraphBound] using
        section16_cor711_graph_cover gamma theta eta hgamma hgammaOne
          htheta hthetaOne heta hetaOne hq hqBound Nprime B phi hfreiman
          P hP hactive hlarge
    · simpa [ProperMultiplyLinear, lemma163LocalExponent,
          lemma163LocalGraphBound] using
        section16_coarse_graph_cover gamma theta eta hgamma hgammaOne
          htheta hthetaOne heta hetaOne hq hqBound B phi P hP hlarge
  · let H := P.carrier \ B
    have hAcard : A.card = (B ∩ P.carrier).card :=
      boxOneIndexDomain_card P hP B
    have hHcardNat : H.card + (B ∩ P.carrier).card = P.carrier.card := by
      have hsub : B ∩ P.carrier ⊆ P.carrier := Finset.inter_subset_right
      have := Finset.card_sdiff_add_card_eq_card hsub
      have hdiff : P.carrier \ (B ∩ P.carrier) = H := by
        ext x
        simp [H]
      rw [hdiff] at this
      exact this
    have hHcard : (1 - eta) * (P.carrier.card : Real) ≤ H.card := by
      have hwidthCard := boxOne_card_eq_width P hP
      have hactive' : (A.card : Real) < eta * P.width := lt_of_not_ge hactive
      have hsum : (H.card : Real) + (A.card : Real) = P.carrier.card := by
        exact_mod_cast (by simpa [hAcard] using hHcardNat)
      have hsum' : (H.card : Real) + (A.card : Real) = P.width := by
        rw [← hwidthCard]
        exact hsum
      nlinarith
    have hwOne : lemma163LocalExponent gamma theta eta q ≤ 1 := by
      have hw := lemma163_exponent_le_corollary_half hgamma hgammaOne htheta
        hthetaOne heta hetaOne hq hqBound
      have ha : lemma163CorollaryExponent eta / 2 ≤ 1 := by
        unfold lemma163CorollaryExponent
        have hetaSq : eta ^ (2 : Nat) ≤ 1 := pow_le_one₀ heta.le hetaOne
        have hp : (2 : Real) ^ (-(14 : Real)) ≤ 1 := by
          calc
            (2 : Real) ^ (-(14 : Real)) ≤ (2 : Real) ^ (0 : Real) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 1 := by simp
        nlinarith
      exact hw.trans ha
    have hwidth : (P.width : Real) ^ lemma163LocalExponent gamma theta eta q ≤
        P.width := by
      by_cases hzero : P.width = 0
      · have hwPos := (lemma163_local_bounds hgamma hgammaOne htheta
          hthetaOne heta hetaOne hq hqBound).1
        simpa only [hzero, Nat.cast_zero, Real.zero_rpow hwPos.ne'] using
          (le_rfl : (0 : Real) ≤ 0)
      · exact Real.rpow_le_self_of_one_le (by exact_mod_cast
          (Nat.one_le_iff_ne_zero.mpr hzero)) hwOne
    refine ⟨1, 0, H, (fun _ : Fin 1 => P), (fun _ i => Fin.elim0 i),
      (by exact Finset.sdiff_subset), hHcard, ?_, (by simpa using hP), ?_,
      (by simpa [lemma163LocalExponent] using hwidth), ?_, ?_⟩
    · constructor
      · intro x
        simp
      · intro i j hij
        exact ((bne_iff_ne.mp hij) (Subsingleton.elim i j)).elim
    · have hg := (lemma163_local_bounds hgamma hgammaOne htheta hthetaOne
          heta hetaOne hq hqBound).2.2
      have hnonneg : (0 : Real) ≤ lemma163LocalGraphBound gamma theta eta q :=
        (by positivity : (0 : Real) ≤
          (2 : Real) ^ (512 : Nat) * eta ^ (-(2 : Int))).trans hg
      simpa only [Nat.cast_zero, lemma163LocalGraphBound] using hnonneg
    · intro j i
      exact Fin.elim0 i
    · intro j x hxQ hxH y hxy
      have hxB := (mem_partialGraph_one B phi x y).1 hxy |>.1
      exact (Finset.mem_sdiff.mp hxH).2 hxB |>.elim

end LeanProofs.GowersSzemeredi.BaseCase
