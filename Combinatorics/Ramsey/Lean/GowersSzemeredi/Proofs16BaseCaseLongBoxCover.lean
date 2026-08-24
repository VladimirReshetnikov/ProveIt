import GowersSzemeredi.Proofs16BaseCaseLongBoxTransport
import GowersSzemeredi.Proofs16BaseCaseQuantitative

/-!
# The long-box graph cover for Lemma 16.3

This module applies Corollary 7.11 on the integer index progression of a proper
one-dimensional modular box, then transports its progression partition and
affine formulas back to proper modular subboxes.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi.BaseCase

lemma section16_cor711_graph_cover {N : Nat} [NeZero N]
    (gamma theta eta : Real) {q : Nat}
    (hgamma : 0 < gamma) (hgammaOne : gamma ≤ 1)
    (htheta : 0 < theta) (hthetaOne : theta ≤ 1)
    (heta : 0 < eta) (hetaOne : eta ≤ 1) (hq : 0 < q)
    (hqBound : (q : Real) * lemma163Alpha gamma theta ≤
      gamma ^ (-(2 : Int))) (Nprime : N.Prime)
    (B : Finset (Point N 1)) (phi : Point N 1 → ZMod N)
    (hfreiman : FreimanHom 8 (pointOneDomain B) (pointOneMap phi))
    (P : Box N 1) (hP : P.IsProper)
    (hactive : eta * P.width ≤ (boxOneIndexDomain P B).card)
    (hlarge : 1024 * Real.pi / eta <
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
  letI : Fact N.Prime := ⟨Nprime⟩
  let R := boxOneIndexAP P
  let A := boxOneIndexDomain P B
  let psi := boxOneIndexMap P phi
  let aexp := lemma163CorollaryExponent eta
  let w := lemma163LocalExponent gamma theta eta q
  let X : Real := (P.width : Real) ^ aexp
  let m := Nat.floor X
  have hRlen : R.length = P.width := rfl
  have hRproper : R.IsProper := boxOneIndexAP_proper P
  have haPos : 0 < aexp := by
    dsimp only [aexp, lemma163CorollaryExponent]
    positivity
  have hRpos : 0 < R.length := by
    have hXpos : 0 < X := (by
      dsimp only [X]
      exact lt_trans (by positivity : 0 < 1024 * Real.pi / eta) hlarge)
    have hPpos : (0 : Real) < P.width := by
      by_contra h
      have : (P.width : Real) = 0 := le_antisymm (not_lt.mp h) (by positivity)
      rw [show X = 0 by
        dsimp only [X]
        rw [this, Real.zero_rpow haPos.ne']] at hXpos
      exact (lt_irrefl 0) hXpos
    exact_mod_cast hPpos
  have hXnonneg : 0 ≤ X := by dsimp only [X]; positivity
  have hmTwo : 2 ≤ m := by
    apply Nat.le_floor
    have hpi := Real.pi_gt_three
    dsimp only [X]
    have hinvEta : (1 : Real) ≤ eta⁻¹ := by
      simpa using (inv_le_inv₀ (by norm_num : (0 : Real) < 1) heta).2 hetaOne
    have hthreshold : (2 : Real) ≤ 1024 * Real.pi / eta := by
      rw [div_eq_mul_inv]
      have hpiTerm : (2 : Real) < 1024 * Real.pi := by nlinarith
      exact hpiTerm.le.trans (by
        simpa using mul_le_mul_of_nonneg_left hinvEta (by positivity :
          (0 : Real) ≤ 1024 * Real.pi))
    exact hthreshold.trans hlarge.le
  have hm : 0 < m := by omega
  have hmBound : (m : Real) ≤ (R.length : Real) ^
      ((2 : Real) ^ (-(14 : Real)) * eta ^ 2 * ((1 : Nat) : Real)⁻¹) := by
    simpa only [m, X, aexp, lemma163CorollaryExponent, hRlen,
      Nat.cast_one, inv_one, mul_one] using Nat.floor_le hXnonneg
  have hcorLarge : 1024 * Real.pi / eta <
      (R.length : Real) ^
        ((2 : Real) ^ (-(14 : Real)) * eta ^ 2 * ((1 : Nat) : Real)⁻¹) := by
    simpa only [X, aexp, lemma163CorollaryExponent, hRlen,
      Nat.cast_one, inv_one, mul_one] using hlarge
  let Avec : Fin 1 → Finset Int := fun _ => A
  let psivec : Fin 1 → Int → ZMod N := fun _ => psi
  have hAvec : ∀ i, Avec i ⊆ R.carrier ∧
      eta * R.length ≤ (Avec i).card ∧ FreimanHom 8 (Avec i) (psivec i) := by
    intro i
    refine ⟨boxOneIndexDomain_subset P B, ?_, ?_⟩
    · change eta * P.width ≤ A.card
      exact hactive
    · change FreimanHom 8 A psi
      exact boxOneIndex_freiman P B phi hfreiman
  obtain ⟨M, S, hSpart, hSproper, hSstep, hSlinear⟩ :=
    corollary_7_11_holds N 1 m R Avec psivec eta
      (by norm_num) hm heta hRpos hRproper hAvec hmBound hcorLarge
  have hSsub (j : Fin M) : (S j).carrier ⊆ R.carrier := hSpart.cell_subset j
  have hQproper (j : Fin M) : (indexCellBox P (S j)).IsProper :=
    indexCellBox_proper P hP (S j) (hSproper j).1 (hSsub j)
  choose c d hcd using fun j : Fin M => hSlinear (0 : Fin 1) j
  let Q : Fin M → Box N 1 := fun j => indexCellBox P (S j)
  let mu : Fin M → Fin 1 → Point N 1 → ZMod N :=
    fun j _ => indexCellAffine P (S j) (c j) (d j)
  have hwHalf := lemma163_exponent_le_corollary_half hgamma hgammaOne htheta
    hthetaOne heta hetaOne hq hqBound
  have hwidthM : (P.width : Real) ^ w ≤ m := by
    have hbase : (1 : Real) ≤ P.width := by exact_mod_cast hRpos
    have hyNonneg : 0 ≤ (P.width : Real) ^ w := by positivity
    have hsq : ((P.width : Real) ^ w) ^ 2 ≤ X := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul (by positivity : (0 : Real) ≤ P.width)]
      dsimp only [X]
      apply Real.rpow_le_rpow_of_exponent_le hbase
      dsimp only [w, aexp]
      exact (le_div_iff₀ (by norm_num : (0 : Real) < 2)).1 hwHalf
    have hXfour : 4 ≤ X := by
      have hpi := Real.pi_gt_three
      have hinvEta : (1 : Real) ≤ eta⁻¹ := by
        simpa using (inv_le_inv₀ (by norm_num : (0 : Real) < 1) heta).2 hetaOne
      have hpiTerm : (4 : Real) < 1024 * Real.pi := by nlinarith
      have hthreshold : (4 : Real) < 1024 * Real.pi / eta := by
        rw [div_eq_mul_inv]
        exact hpiTerm.trans_le (by
          simpa using mul_le_mul_of_nonneg_left hinvEta (by positivity :
            (0 : Real) ≤ 1024 * Real.pi))
      exact (hthreshold.trans hlarge).le
    have hy : (P.width : Real) ^ w ≤ X - 1 := by nlinarith
    have hfloor : X < (m : Real) + 1 := by
      simpa only [m] using Nat.lt_floor_add_one X
    linarith
  refine ⟨M, 1, P.carrier, Q, mu, Finset.Subset.rfl, ?_, ?_, hQproper, ?_, ?_, ?_, ?_⟩
  · have hc : (0 : Real) ≤ P.carrier.card := by positivity
    nlinarith
  · exact indexCells_partition P hP S hSpart
  · have hg := (lemma163_local_bounds hgamma hgammaOne htheta hthetaOne
        heta hetaOne hq hqBound).2.2
    have hetaSq : eta ^ (2 : Nat) ≤ 1 := pow_le_one₀ heta.le hetaOne
    have hetaInvSq : (1 : Real) ≤ eta ^ (-(2 : Int)) := by
      rw [zpow_neg]
      exact (one_le_inv₀ (pow_pos heta 2)).2 hetaSq
    have htwo : (1 : Real) ≤ 2 ^ (512 : Nat) := one_le_pow₀ (by norm_num)
    have hone : (1 : Real) ≤ 2 ^ (512 : Nat) * eta ^ (-(2 : Int)) := by
      calc
        (1 : Real) = 1 * 1 := by ring
        _ ≤ 2 ^ (512 : Nat) * eta ^ (-(2 : Int)) :=
          mul_le_mul htwo hetaInvSq (by norm_num : (0 : Real) ≤ 1)
            (by positivity : (0 : Real) ≤ (2 : Real) ^ (512 : Nat))
    simpa only [Nat.cast_one] using hone.trans hg
  · intro j
    have hmj : m ≤ (S j).length := by
      rcases (hSproper j).2 with h | h <;> omega
    exact hwidthM.trans (by exact_mod_cast hmj)
  · intro j i
    exact indexCellAffine_multilinear P (S j) (c j) (d j)
  · intro j x hxQ hxH y hxy
    have hy := (mem_partialGraph_one B phi x y).1 hxy
    rw [indexCellBox_carrier] at hxQ
    obtain ⟨z, hzS, hzx⟩ := Finset.mem_image.mp hxQ
    rw [IntAP.carrier] at hzS
    obtain ⟨i, _hi, hiz⟩ := Finset.mem_image.mp hzS
    have hzx' : boxOneIntPoint P
        ((S j).start + ((i : Nat) * (S j).step : Nat)) = x :=
      (congrArg (boxOneIntPoint P) hiz).trans hzx
    have hzA : (S j).start + ((i : Nat) * (S j).step : Nat) ∈ A := by
      change (S j).start + ((i : Nat) * (S j).step : Nat) ∈
        boxOneIndexDomain P B
      rw [boxOneIndexDomain, Finset.mem_filter]
      refine ⟨hSsub j ?_, ?_⟩
      · rw [IntAP.carrier]
        apply Finset.mem_image.mpr
        exact ⟨i, _hi, rfl⟩
      · rw [hzx']
        exact hy.1
    have hvalue := hcd j i
    have hvalue' : psi ((S j).start + ((i : Nat) * (S j).step : Nat)) =
        c j * (i : Nat) + d j := by
      apply hvalue
      simpa [Avec] using hzA
    have hstepNe : ((S j).step : ZMod N) * (P.axis 0).step ≠ 0 := by
      exact proper_modAP_step_ne_zero_of_two_le ((Q j).axis 0)
        (hQproper j 0) (by simpa [Q, indexCellBox] using hmTwo.trans (by
          rcases (hSproper j).2 with h | h <;> omega))
    refine ⟨(0 : Fin 1), ?_⟩
    rw [hy.2, ← hzx']
    change psi ((S j).start + ((i : Nat) * (S j).step : Nat)) =
      indexCellAffine P (S j) (c j) (d j)
        (boxOneIntPoint P ((S j).start + ((i : Nat) * (S j).step : Nat)))
    rw [indexCellAffine_value P (S j) (c j) (d j) i hstepNe]
    exact hvalue'

end LeanProofs.GowersSzemeredi.BaseCase
