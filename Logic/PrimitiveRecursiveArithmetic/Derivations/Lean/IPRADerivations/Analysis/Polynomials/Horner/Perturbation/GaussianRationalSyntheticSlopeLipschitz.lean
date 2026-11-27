import IPRADerivations.Analysis.Polynomials.Taylor.GaussianRational.GaussianRationalUniformFirstOrderPolynomial
import IPRADerivations.Analysis.Polynomials.Horner.Perturbation.GaussianRationalHornerPerturbation

/-!
# Uniform continuity of the original rational synthetic slope

Changing the anchor changes both the quotient coefficients and the
Horner argument. The coefficients are original Horner prefixes.
The two checked Horner estimates give a uniform bound for the
difference of the original slopes, including at zero.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianRationalSyntheticSlopeLipschitz

open_ipra
open GaussianRationalFirstOrderPolynomial (paddedQuotient padded_length slope)
open GaussianRationalHorner (evaluate horner positive_product)
open GaussianRationalHornerPerturbation (coefficientErrors)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalSyntheticDivision (quotient quotient_length quotient_lookup)
open GaussianRationalUniformFirstOrderPolynomial (mass quotient_coefficients)
open GaussianRationalVariableHornerBudget (denominator denominator_positive variation variation_index_congr variation_succ)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def valueGain (C U : PTm n) : PTm n := variation C U (length C)
def slopeGain (C N U : PTm n) : PTm n :=
  GaussianRationalUniformFirstOrderPolynomial.constant C N U+(N*pw U (pred N))*valueGain C U

@[simp] theorem subst_valueGain {m : ℕ} (σ : Fin n → PTm m) (C U : PTm n) :
    Syn.subst σ (valueGain C U) = valueGain (Syn.subst σ C) (Syn.subst σ U) := by simp [valueGain]

@[simp] theorem subst_slopeGain {m : ℕ} (σ : Fin n → PTm m) (C N U : PTm n) :
    Syn.subst σ (slopeGain C N U) = slopeGain (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ U) := by
  simp [slopeGain]

private theorem variation_increases (C U k : PTm n) (hU : Γ ⊢[PRAAx] le one U) :
    Γ ⊢[PRAAx] le (variation C U k) (variation C U (succ k)) := by
  let V := variation C U k
  have grow : Γ ⊢[PRAAx] le V (U*V) :=
    le_congr (one_mul V) (.eqRefl _) (mul_le_mul_right V hU)
  exact le_trans grow (le_congr (.eqRefl _) (variation_succ C U k).eqSymm (le_add_right _ _))

private def forwardLaw (C U k j : PTm n) : Fm PTm n := le (variation C U k) (variation C U (k+j))

@[simp] private theorem subst_forwardLaw {m : ℕ} (σ : Fin n → PTm m) (C U k j : PTm n) :
    (forwardLaw C U k j).subst σ = forwardLaw (Syn.subst σ C) (Syn.subst σ U) (Syn.subst σ k) (Syn.subst σ j) := by
  simp [forwardLaw]

private theorem variation_forward (C U k j : PTm n) (hU : Γ ⊢[PRAAx] le one U) : Γ ⊢[PRAAx] forwardLaw C U k j := by
  have us : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift U) := by simpa [Fm.shift,Syn.shift,one] using hU.shift
  have all : Γ ⊢[PRAAx] .all (forwardLaw (Syn.shift C) (Syn.shift U) (Syn.shift k) (var 0)) := by
    ipra_qfind (le_QF _ _) [subst_forwardLaw]
    · exact le_congr (.eqRefl _) (variation_index_congr C U (add_zero k)).eqSymm (le_refl _)
    · exact le_trans Prf.hyp0 (le_congr (.eqRefl _)
        (variation_index_congr _ _ (add_succ (Syn.shift k) (var 0))).eqSymm (variation_increases _ _ _ us.wk))
  simpa only [subst_forwardLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j

private theorem variation_cap (C U k : PTm n) (hU : Γ ⊢[PRAAx] le one U)
    (hk : Γ ⊢[PRAAx] le k (length C)) : Γ ⊢[PRAAx] le (variation C U k) (valueGain C U) :=
  le_congr (.eqRefl _) (variation_index_congr C U (eq_add_of_le hk).eqSymm)
    (variation_forward C U k (monus (length C) k) hU)

private theorem remove_denominator (G V A E F : PTm n)
    (hv : Γ ⊢[PRAAx] le V G) (hf : Γ ⊢[PRAAx] le one F) :
    Γ ⊢[PRAAx] le ((V*A)*E) ((G*A)*(F*E)) := by
  have p := mul_le_mul_right (A*E) hv
  have q := mul_le_mul_right (G*A*E) hf
  have stage : Γ ⊢[PRAAx] le ((V*A)*E) ((G*A)*E) :=
    le_congr (by ipra_ring) (by ipra_ring) p
  exact le_trans stage (le_congr (by ipra_ring) (by ipra_ring) q)

theorem prefix_rate (C t s U A E k : PTm n) (hU : Γ ⊢[PRAAx] le one U)
    (ht : Γ ⊢[PRAAx] bounded t U one) (hs : Γ ⊢[PRAAx] bounded s U one)
    (hE : Γ ⊢[PRAAx] le one E) (hd : Γ ⊢[PRAAx] distanceBounded t s A E)
    (hk : Γ ⊢[PRAAx] le k (length C)) : Γ ⊢[PRAAx]
    distanceBounded (horner C t k) (horner C s k) (valueGain C U*A) E :=
  distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (denominator_positive C) hE) hE
    (remove_denominator _ _ A E _ (variation_cap C U k hU hk) (denominator_positive C))
    (GaussianRationalVariableHornerBudget.variation_prefix C U t s A E k ht hs hE hd hk)

theorem value_rate (C t s U A E : PTm n) (hU : Γ ⊢[PRAAx] le one U)
    (ht : Γ ⊢[PRAAx] bounded t U one) (hs : Γ ⊢[PRAAx] bounded s U one)
    (hE : Γ ⊢[PRAAx] le one E) (hd : Γ ⊢[PRAAx] distanceBounded t s A E) : Γ ⊢[PRAAx]
    distanceBounded (evaluate C t) (evaluate C s) (valueGain C U*A) E :=
  prefix_rate C t s U A E (length C) hU ht hs hE hd (le_refl _)

private theorem padded_row (C t N i : PTm n) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] entry (paddedQuotient C t N) (succ i) ≐ horner C t (succ i) :=
  ((Foundations.SequenceComposition.entry_congr (.eqRefl _) (show Γ ⊢[PRAAx] succ i ≐ one+i by ipra_ring)).eqTrans
    (GaussianRationalPolynomialBuffers.pad_tail (quotient C t N) one i
      (lt_congr (.eqRefl _) (quotient_length C t N).eqSymm hi))).eqTrans (quotient_lookup C t N i hi)

private theorem coefficients_rate (C t s N U A E : PTm n)
    (hLen : Γ ⊢[PRAAx] length C ≐ succ N) (hU : Γ ⊢[PRAAx] le one U)
    (ht : Γ ⊢[PRAAx] bounded t U one) (hs : Γ ⊢[PRAAx] bounded s U one)
    (hE : Γ ⊢[PRAAx] le one E) (hd : Γ ⊢[PRAAx] distanceBounded t s A E) :
    Γ ⊢[PRAAx] coefficientErrors (paddedQuotient C t N) (paddedQuotient C s N) N (valueGain C U*A) E := by
  refine .allI (.impI ?_)
  let sh (x : PTm n) := Syn.shift x
  let i : PTm (n+1) := var 0
  let Δ := lt i (sh N) :: Γ.map Fm.shift
  have ls : Δ ⊢[PRAAx] length (sh C) ≐ succ (sh N) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hLen.shift.wk
  have us : Δ ⊢[PRAAx] le one (sh U) := by simpa [Δ,sh,Fm.shift,Syn.shift,one] using hU.shift.wk
  have ts : Δ ⊢[PRAAx] bounded (sh t) (sh U) one := by simpa [Δ,sh,Fm.shift,Syn.shift,one] using ht.shift.wk
  have ss : Δ ⊢[PRAAx] bounded (sh s) (sh U) one := by simpa [Δ,sh,Fm.shift,Syn.shift,one] using hs.shift.wk
  have es : Δ ⊢[PRAAx] le one (sh E) := by simpa [Δ,sh,Fm.shift,Syn.shift,one] using hE.shift.wk
  have ds : Δ ⊢[PRAAx] distanceBounded (sh t) (sh s) (sh A) (sh E) := by
    simpa [Δ,sh,Fm.shift,Syn.shift] using hd.shift.wk
  have hi : Δ ⊢[PRAAx] lt i (sh N) := Prf.hyp0
  have hk : Δ ⊢[PRAAx] le (succ i) (length (sh C)) :=
    le_trans hi (le_congr (.eqRefl _) ls.eqSymm (le_succ_self (sh N)))
  have pre := prefix_rate (sh C) (sh t) (sh s) (sh U) (sh A) (sh E) (succ i) us ts ss es ds hk
  simpa only [Syn.shift,sh,Δ,i,GaussianRationalFirstOrderPolynomial.subst_paddedQuotient,PTm.subst_mul,subst_valueGain] using
    distance_congr (padded_row (sh C) (sh t) (sh N) i hi).eqSymm
      (padded_row (sh C) (sh s) (sh N) i hi).eqSymm (.eqRefl _) (.eqRefl _) pre

theorem slope_rate (C t s N U A E : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N)
    (hU : Γ ⊢[PRAAx] le one U) (ht : Γ ⊢[PRAAx] bounded t U one) (hs : Γ ⊢[PRAAx] bounded s U one)
    (hE : Γ ⊢[PRAAx] le one E) (hd : Γ ⊢[PRAAx] distanceBounded t s A E) : Γ ⊢[PRAAx]
    distanceBounded (slope C t N) (slope C s N) (slopeGain C N U*A) E := by
  let P := paddedQuotient C t N
  let Q := paddedQuotient C s N
  have errors := coefficients_rate C t s N U A E hLen hU ht hs hE hd
  have leading : Γ ⊢[PRAAx] entry P zero ≐ entry Q zero :=
    (GaussianRationalPolynomialBuffers.pad_leading (quotient C t N) one zero (zero_lt_succ zero)).eqTrans
      (GaussianRationalPolynomialBuffers.pad_leading (quotient C s N) one zero (zero_lt_succ zero)).eqSymm
  have anchor := GaussianRationalHornerPerturbation.evaluation_bound P Q s N U (valueGain C U*A) E
    (padded_length C t N) (padded_length C s N) leading hU hE errors hs
  have query := GaussianRationalHornerLipschitz.evaluation_bound P t s N U (mass C U) A E
    (padded_length C t N) (quotient_coefficients C t N U hLen hU ht) ht hs hE hd
  have sum := distance_triangle_same _ _ _ _ _ _ hE query anchor
  exact distance_congr (GaussianRationalPolynomialBuffers.pad_evaluation (quotient C t N) one t)
    (GaussianRationalPolynomialBuffers.pad_evaluation (quotient C s N) one s)
    (by dsimp only [slopeGain,GaussianRationalUniformFirstOrderPolynomial.constant,GaussianRationalHornerPerturbation.budget]; ipra_ring) (.eqRefl _) sum

theorem actual_rational_synthetic_slope_lipschitz_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      (let C := var 0
       let t := var 1
       let s := var 2
       let N := var 3
       let U := var 4
       let A := var 5
       let E := var 6
       (length C ≐ succ N ⋏ (le one U ⋏ (bounded t U one ⋏
         (bounded s U one ⋏ (le one E ⋏ distanceBounded t s A E))))) ⟶
           distanceBounded (slope C t N) (slope C s N) (slopeGain C N U*A) E) :=
  closeUniv 7 (.impI (slope_rate _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianRationalSyntheticSlopeLipschitz
