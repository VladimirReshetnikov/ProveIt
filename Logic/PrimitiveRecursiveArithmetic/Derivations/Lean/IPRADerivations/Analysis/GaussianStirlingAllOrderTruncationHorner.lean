import IPRADerivations.Analysis.GaussianStirlingAllOrderTruncationPower
import IPRADerivations.Analysis.GaussianStirlingAllOrderLogTruncation

/-!
# Original Horner evaluation of every literal logarithmic truncation

The existing coefficient table has one exact odd term and one zero
even term at each step. Its original power-expansion program proves
equality with the literal increasing-order sum used in the remainder.
-/

set_option autoImplicit false
set_option maxHeartbeats 1050000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderTruncationHorner

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qzero qadd qmul hornerF)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qmul_zero_left qzero_canonical)
open GaussianReciprocalHorner (qadd_zero_right)
open GaussianRationalPowerExpansion (partialSum prefix_succ prefix_zero prefix_canonical terms_length power_expansion)
open GaussianStirlingExpansionCoefficients (logTable log_table_entry log_table_length logCoefficient log_coefficient_even quoted)
open GaussianStirlingExpansionFiniteError (query logPolynomial)
open GaussianStirlingAllOrderTruncationAlgebra (truncation correction)
open GaussianStirlingAllOrderTruncationPower (correction_at)
open GaussianStirlingAllOrderLogTruncation (signedF signedData errorF errorData original_logarithmic_truncation)
open GaussianStirlingNames (source)
open GaussianStirlingGlobalBounds (remainderData)
open GaussianNameEquivalence (crossEquivalent)
open LeanProofs.IPRA.Foundations.SequenceComposition (entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "expandedTerm" => GaussianOffDominantTerms.term

private theorem num_succ (k : ℕ) : Γ ⊢[PRAAx] (num (k+1) : PTm n) ≐ succ (num k) := by
  apply deriveNat
  ipra_simps
  push_cast
  ring

private theorem numeral_difference (d j : ℕ) (h : j≤d) : Γ ⊢[PRAAx]
    monus (num d : PTm n) (num j) ≐ num (d-j) := by
  have e : Γ ⊢[PRAAx] (num d : PTm n) ≐ num (d-j)+num j := by
    apply deriveNat
    ipra_simps
    rw [Nat.cast_sub h]
    ring
  exact (congrMonus e (zero_add (num j)).eqSymm).eqTrans
    ((monus_add_add _ zero _).eqTrans (monus_zero _))

private theorem coefficient_at (d j : ℕ) (h : j≤d) : Γ ⊢[PRAAx]
    GaussianBalancedRadiusSyntax.coefficient (logTable (n := n) d) (num d) (num j) ≐ quoted (logCoefficient j) := by
  have e := log_table_entry (Γ := Γ) d (d-j) (by omega)
  have k : d-(d-j)=j := by omega
  exact (entry_congr (.eqRefl _) (numeral_difference d j h)).eqTrans (by simpa only [k] using e)

theorem even_term (d j : ℕ) (h : 2*j≤d) (A B : PTm n) : Γ ⊢[PRAAx]
    expandedTerm (logTable d) (num d) (query A B) (num (2*j)) ≐ qzero := by
  have c : Γ ⊢[PRAAx] GaussianBalancedRadiusSyntax.coefficient (logTable (n := n) d) (num d) (num (2*j)) ≐ qzero := by
    simpa [log_coefficient_even,quoted] using coefficient_at (Γ := Γ) d (2*j) h
  exact (qmul_congr c (.eqRefl _)).eqTrans (qmul_zero_left _)

theorem odd_term (d j : ℕ) (h : 2*j+1≤d) (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) :
    Γ ⊢[PRAAx] expandedTerm (logTable d) (num d) (query A B) (num (2*j+1)) ≐ correction j A B :=
  (qmul_congr (coefficient_at d _ h) (.eqRefl _)).eqTrans (correction_at j A B hA)

private theorem append_term (d j : ℕ) (h : j≤d) (A B : PTm n) : Γ ⊢[PRAAx]
    partialSum (logTable d) (num d) (query A B) (num (j+1)) ≐
      qadd (partialSum (logTable d) (num d) (query A B) (num j)) (expandedTerm (logTable d) (num d) (query A B) (num j)) :=
  (congrAp3 hornerF (num_succ j) (.eqRefl _) (.eqRefl _)).eqTrans
    (prefix_succ _ _ _ _ (Foundations.NumeralPrimes.num_le h))

theorem even_prefix (d j : ℕ) (h : 2*j≤d) (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) :
    Γ ⊢[PRAAx] partialSum (logTable d) (num d) (query A B) (num (2*j+1)) ≐ truncation j A B := by
  induction j with
  | zero =>
    exact (append_term d 0 (by omega) A B).eqTrans
      ((qadd_congr (prefix_zero _ _ _) (even_term d 0 (by omega) A B)).eqTrans
        (qadd_zero_right _ qzero_canonical))
  | succ j ih =>
    let L := logTable (n := n) d
    let N : PTm n := num d
    let Q := query A B
    have a : Γ ⊢[PRAAx] partialSum L N Q (num (2*j+2)) ≐ truncation (j+1) A B :=
      (append_term d (2*j+1) (by omega) A B).eqTrans (qadd_congr (ih (by omega)) (odd_term d j (by omega) A B hA))
    have b : Γ ⊢[PRAAx] partialSum L N Q (num (2*j+3)) ≐ truncation (j+1) A B :=
      (append_term d (2*j+2) (by omega) A B).eqTrans ((qadd_congr (.eqRefl _) (even_term d (j+1) (by omega) A B)).eqTrans
        ((qadd_zero_right _ (prefix_canonical _ _ _ _)).eqTrans a))
    simpa only [show 2*(j+1)+1=2*j+3 by omega] using b

private theorem polynomial_full (d : ℕ) (A B : PTm n) : Γ ⊢[PRAAx]
    logPolynomial d A B ≐ partialSum (logTable d) (num d) (query A B) (num (d+1)) :=
  (power_expansion _ _ _ (log_table_length d)).eqTrans
    (congrAp3 hornerF ((terms_length _ _ _).eqTrans (num_succ d).eqSymm) (.eqRefl _) (.eqRefl _))

theorem truncation_even_horner (m : ℕ) (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) :
    Γ ⊢[PRAAx] truncation m A B ≐ logPolynomial (2*m) A B :=
  ((polynomial_full (2*m) A B).eqTrans (even_prefix _ _ (by omega) A B hA)).eqSymm

theorem truncation_odd_horner (m : ℕ) (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) :
    Γ ⊢[PRAAx] truncation (m+1) A B ≐ logPolynomial (2*m+1) A B :=
  ((polynomial_full (2*m+1) A B).eqTrans ((append_term _ _ (by omega) A B).eqTrans
    (qadd_congr (even_prefix _ _ (by omega) A B hA) (odd_term _ _ (by omega) A B hA)))).eqSymm

def hornerErrorData (d : ℕ) (A B x : PTm n) : PTm n :=
  GaussianNamedDifference.data (remainderData A B x) (logPolynomial d A B)

private theorem change_truncation (m d : ℕ) (A B x : PTm n) (hs : Γ ⊢[PRAAx] source A B)
    (h : Γ ⊢[PRAAx] truncation m A B ≐ logPolynomial d A B) : Γ ⊢[PRAAx]
    crossEquivalent (signedF m) errorF (signedData m A B) (hornerErrorData d A B x) := by
  let z := signedData m A B
  let r := remainderData A B x
  let f : Fm PTm 3 := crossEquivalent (signedF m) errorF (var 0) (GaussianNamedDifference.data (var 1) (var 2))
  have v := Prf.eqSubst (Ax := PRAAx) (Γ := Γ) f ![z,r,truncation m A B] ![z,r,logPolynomial d A B]
    (fun i => by fin_cases i; exact .eqRefl _; exact .eqRefl _; exact h)
    (by simpa only [f,z,r,errorData,GaussianNameEquivalence.subst_crossEquivalent,GaussianNamedDifference.subst_data,
      Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
      using original_logarithmic_truncation m A B x hs)
  simpa only [f,hornerErrorData,z,r,GaussianNameEquivalence.subst_crossEquivalent,GaussianNamedDifference.subst_data,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using v

theorem even_horner_cross (m : ℕ) (A B x : PTm n) (hs : Γ ⊢[PRAAx] source A B) : Γ ⊢[PRAAx]
    crossEquivalent (signedF m) errorF (signedData m A B) (hornerErrorData (2*m) A B x) :=
  change_truncation m _ A B x hs (truncation_even_horner m A B hs.andE₁)

theorem odd_horner_cross (m : ℕ) (A B x : PTm n) (hs : Γ ⊢[PRAAx] source A B) : Γ ⊢[PRAAx]
    crossEquivalent (signedF (m+1)) errorF (signedData (m+1) A B) (hornerErrorData (2*m+1) A B x) :=
  change_truncation (m+1) _ A B x hs (truncation_odd_horner m A B hs.andE₁)

theorem actual_original_logarithmic_horner_truncations_closed (m : ℕ) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (source (var 0) (var 1) ⟶
        crossEquivalent (signedF m) errorF (signedData m (var 0) (var 1)) (hornerErrorData (2*m) (var 0) (var 1) (var 2)) ⋏
        crossEquivalent (signedF (m+1)) errorF (signedData (m+1) (var 0) (var 1))
          (hornerErrorData (2*m+1) (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (.andI (even_horner_cross m _ _ _ Prf.hyp0) (odd_horner_cross m _ _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderTruncationHorner
