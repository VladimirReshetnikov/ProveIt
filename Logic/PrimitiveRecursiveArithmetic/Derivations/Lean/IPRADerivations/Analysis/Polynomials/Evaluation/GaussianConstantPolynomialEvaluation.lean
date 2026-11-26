import IPRADerivations.Analysis.Polynomials.Coefficients.GaussianConstantCoefficientNames
import IPRADerivations.Analysis.Polynomials.RootFinding.FundamentalTheorem.GaussianGeneralFTAValueZero

/-!
# The constant-name FTA program evaluates the original numerical polynomial

Double truncated subtraction identifies every sampled coefficient with the
original entry. A guarded QF induction identifies actual Horner prefixes,
without asserting equality of arbitrary outer list codes. The general value
program consequently names the original polynomial evaluated at its actual
point program and computed precision. Canonical recoding is retained.

For a list of length N+1 with a nonzero positive-degree coefficient, the
constant-name compiler supplies genuine coefficient names and its own dyadic
apartness. The concrete FTA then gives a root point name and a fast zero name
of evaluations of this original list. All numerical inputs, including N and
the selected nonzero coefficient index, remain object-language variables.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianConstantPolynomialEvaluation

open_ipra
open LeanProofs.IPRA.Analysis.GaussianConstantCoefficientNames (coefficientF data apartPrecision)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (horner hornerF evaluate)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (bounded)
open LeanProofs.IPRA.Analysis.GaussianCoefficientNameBounds (unit subst_unit)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qadd_congr qmul_congr)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (pointCN)
open LeanProofs.IPRA.Analysis.GaussianRootApproximationWitness (pointBounds)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def sample (C N s : PTm n) : PTm n :=
  GaussianGeneralPolynomialSamples.sample coefficientF N s (data C N)
def prefixLaw (C N z s r : PTm n) : Fm PTm n :=
  le r (succ N) ⟶ horner (sample C N s) z r ≐ horner C z r

ipra_subst sample
ipra_subst prefixLaw

/-- Actual entry codes, including raw noncanonical original coefficients. -/
theorem sample_entry (C N s i : PTm n) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    entry (sample C N s) i ≐ entry C i :=
  (GaussianGeneralPolynomialSamples.sample_lookup coefficientF N s (data C N) i hi).eqTrans
    ((GaussianConstantCoefficientNames.coefficient_at C N (PTm.monus N i) s).eqTrans
      (entry_congr (.eqRefl _) (Foundations.BoundedSyntaxBackwardInduction.reverse_complement N i hi)))

theorem prefix_zero (C N z s : PTm n) : Γ ⊢[PRAAx]
    horner (sample C N s) z zero ≐ horner C z zero :=
  (GaussianRationalHorner.horner_zero _ _).eqTrans (GaussianRationalHorner.horner_zero _ _).eqSymm

theorem prefix_step (C N z s r : PTm n) (hr : Γ ⊢[PRAAx] le r N)
    (ih : Γ ⊢[PRAAx] horner (sample C N s) z r ≐ horner C z r) : Γ ⊢[PRAAx]
    horner (sample C N s) z (succ r) ≐ horner C z (succ r) :=
  (GaussianRationalHorner.horner_succ _ _ _).eqTrans
    ((qadd_congr (qmul_congr ih (.eqRefl _)) (sample_entry C N s r hr)).eqTrans
      (GaussianRationalHorner.horner_succ _ _ _).eqSymm)

/-- The induction formula is a guarded equality of actual PR Horner prefixes. -/
theorem horner_prefix (C N z s r : PTm n) (hr : Γ ⊢[PRAAx] le r (succ N)) : Γ ⊢[PRAAx]
    horner (sample C N s) z r ≐ horner C z r := by
  have all : Γ ⊢[PRAAx] .all
      (prefixLaw (Syn.shift C) (Syn.shift N) (Syn.shift z) (Syn.shift s) (var 0)) := by
    ipra_qfind (⟨le_QF _ _,trivial⟩) [subst_prefixLaw]
    · exact .impI (prefix_zero C N z s).wk
    · refine .impI ?_
      have inside : le (succ (var 0)) (succ (Syn.shift N)) ::
          prefixLaw (Syn.shift C) (Syn.shift N) (Syn.shift z) (Syn.shift s) (var 0) :: Γ.map Fm.shift
          ⊢[PRAAx] le (var 0) (Syn.shift N) :=
        (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
      exact prefix_step _ _ _ _ _ inside
        (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0))
  have rule : Γ ⊢[PRAAx] prefixLaw C N z s r := by
    simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE r
  exact .impE rule hr

/-- Length and entry equations give the original evaluation, without list-code extensionality. -/
theorem sample_evaluation (C N z s : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N) : Γ ⊢[PRAAx]
    evaluate (sample C N s) z ≐ evaluate C z :=
  (congrAp3 hornerF (GaussianGeneralPolynomialSamples.sample_length coefficientF N s (data C N))
    (.eqRefl _) (.eqRefl _)).eqTrans
    ((horner_prefix C N z s (succ N) (le_refl _)).eqTrans
      (congrAp3 hornerF hLen.eqSymm (.eqRefl _) (.eqRefl _)))

theorem observation_original (point : PR 2) (C N y s : PTm n)
    (hLen : Γ ⊢[PRAAx] length C ≐ succ N) : Γ ⊢[PRAAx]
    GaussianGeneralPolynomialEvaluation.observation coefficientF point N (data C N) y s ≐
      evaluate C (ap2 point s y) := sample_evaluation C N _ s hLen

def precision (C N U t : PTm n) : PTm n :=
  GaussianGeneralPolynomialValueName.exponent coefficientF N U (data C N) t
def originalValue (point : PR 2) (C N U y t : PTm n) : PTm n :=
  GaussianFastValueCut.recode (evaluate C (ap2 point (precision C N U t) y))

ipra_subst precision
ipra_subst originalValue

theorem recode_congr {z w : PTm n} (h : Γ ⊢[PRAAx] z ≐ w) : Γ ⊢[PRAAx]
    GaussianFastValueCut.recode z ≐ GaussianFastValueCut.recode w := by
  ipra_congr (GaussianFastValueCut.recode (var 0) : PTm 1) with [h]

/-- The exact generic normalizer is a recoding of the ORIGINAL evaluation. -/
theorem value_original (point : PR 2) (C N U y t : PTm n)
    (hLen : Γ ⊢[PRAAx] length C ≐ succ N) : Γ ⊢[PRAAx]
    GaussianGeneralPolynomialValueName.value coefficientF point N U (data C N) y t ≐
      originalValue point C N U y t :=
  (GaussianGeneralPolynomialValueName.value_observation coefficientF point N U (data C N) y t).eqTrans
    (recode_congr (observation_original point C N y (precision C N U t) hLen))

theorem name_original (point : PR 2) (C N U y t : PTm n)
    (hLen : Γ ⊢[PRAAx] length C ≐ succ N) : Γ ⊢[PRAAx]
    ap2 (GaussianGeneralPolynomialValueName.nameF coefficientF point) t
      (GaussianGeneralPolynomialValueName.nameData coefficientF N U (data C N) y) ≐
      originalValue point C N U y t :=
  (GaussianGeneralPolynomialValueName.name_at coefficientF point N U (data C N) y t).eqTrans
    (value_original point C N U y t hLen)

def rootF : PR 2 := GaussianGeneralFTATrajectory.nameF coefficientF
def rootData (C N k : PTm n) : PTm n :=
  GaussianGeneralFTATrajectory.nameData N (apartPrecision C N k) (data C N)
def radius (C N k : PTm n) : PTm n :=
  GaussianGeneralFTAConstants.R coefficientF N (apartPrecision C N k) (data C N)
def valueF : PR 2 := GaussianGeneralFTAValueZero.valueNameF coefficientF
def valueData (C N k : PTm n) : PTm n :=
  GaussianGeneralFTAValueZero.valueNameData coefficientF N (apartPrecision C N k) (data C N)
def input (C N k : PTm n) : Fm PTm n := length C ≐ succ N ⋏
  (le one k ⋏ (le k N ⋏ le one (GaussianBalancedRadiusSyntax.numerator C N k)))
def originalZero (C N k : PTm n) : Fm PTm n := .all
  (bounded (evaluate (Syn.shift C) (ap2 rootF
    (precision (Syn.shift C) (Syn.shift N) (radius (Syn.shift C) (Syn.shift N) (Syn.shift k)) (var 0))
    (rootData (Syn.shift C) (Syn.shift N) (Syn.shift k)))) one (unit (var 0)))

ipra_subst rootData
ipra_subst radius
ipra_subst valueData
ipra_subst input
ipra_subst originalZero [Syn.subst_shift, Syn.shift_subst]

theorem source_input (C N k : PTm n) (h : Γ ⊢[PRAAx] input C N k) : Γ ⊢[PRAAx]
    GaussianGeneralPolynomialSamples.sourceInput coefficientF N k (apartPrecision C N k) (data C N) :=
  GaussianConstantCoefficientNames.source_input C N k (.andE₁ (.andE₂ h))
    (.andE₁ (.andE₂ (.andE₂ h))) (.andE₂ (.andE₂ (.andE₂ h)))

/-- The actual value program query is the canonical original-polynomial evaluation. -/
theorem original_program_at (C N k t : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N) : Γ ⊢[PRAAx]
    ap2 valueF t (valueData C N k) ≐ originalValue rootF C N (radius C N k) (rootData C N k) t :=
  name_original rootF C N (radius C N k) (rootData C N k) t hLen

theorem original_zero_at (C N k t : PTm n) (h : Γ ⊢[PRAAx] input C N k) : Γ ⊢[PRAAx]
    bounded (evaluate C (ap2 rootF (precision C N (radius C N k) t) (rootData C N k))) one (unit t) := by
  have program := GaussianGeneralFTAValueZero.value_name_zero_bound coefficientF N k
    (apartPrecision C N k) (data C N) t (source_input C N k h)
  have recoded := GaussianRationalReciprocal.bound_congr (original_program_at C N k t (.andE₁ h))
    (.eqRefl _) (.eqRefl _) program
  exact (GaussianFastValueCut.recode_bound_iff _ one (unit t)
    (GaussianCoefficientNameBounds.unit_positive t)).iffMp recoded

theorem original_zero (C N k : PTm n) (h : Γ ⊢[PRAAx] input C N k) : Γ ⊢[PRAAx] originalZero C N k := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] input (Syn.shift C) (Syn.shift N) (Syn.shift k) := by
    simpa only [Fm.shift,subst_input,Syn.shift] using h.shift
  exact original_zero_at (Syn.shift C) (Syn.shift N) (Syn.shift k) (var 0) hs

theorem concrete_root (C N k : PTm n) (h : Γ ⊢[PRAAx] input C N k) : Γ ⊢[PRAAx]
    pointCN rootF (rootData C N k) ⋏
      (pointBounds rootF (radius C N k) (rootData C N k) ⋏
        (pointCN valueF (valueData C N k) ⋏
          (GaussianGeneralPolynomialValueName.programZero valueF (valueData C N k) ⋏ originalZero C N k))) := by
  have main := GaussianGeneralFTAValueZero.general_fta coefficientF N k
    (apartPrecision C N k) (data C N) (source_input C N k h)
  exact .andI (.andE₁ main) (.andI (.andE₁ (.andE₂ main))
    (.andI (.andE₁ (.andE₂ (.andE₂ main)))
      (.andI (.andE₂ (.andE₂ (.andE₂ main))) (original_zero C N k h))))

/-! Every numerical list, degree, index, point and precision is internal. -/

theorem actual_constant_sample_entry_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (var 3) (var 1) ⟶ entry (sample (var 0) (var 1) (var 2)) (var 3) ≐ entry (var 0) (var 3)) :=
  closeUniv 4 (.impI (sample_entry _ _ _ _ Prf.hyp0))

theorem actual_original_horner_prefix_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (var 4) (succ (var 1)) ⟶
      horner (sample (var 0) (var 1) (var 3)) (var 2) (var 4) ≐ horner (var 0) (var 2) (var 4)) :=
  closeUniv 5 (.impI (horner_prefix _ _ _ _ _ Prf.hyp0))

theorem actual_original_polynomial_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (var 0) ≐ succ (var 1) ⟶
      evaluate (sample (var 0) (var 1) (var 3)) (var 2) ≐ evaluate (var 0) (var 2)) :=
  closeUniv 4 (.impI (sample_evaluation _ _ _ _ Prf.hyp0))

theorem actual_original_polynomial_value_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (var 0) ≐ succ (var 1) ⟶
      ap2 valueF (var 3) (valueData (var 0) (var 1) (var 2)) ≐
        originalValue rootF (var 0) (var 1) (radius (var 0) (var 1) (var 2))
          (rootData (var 0) (var 1) (var 2)) (var 3)) :=
  closeUniv 4 (.impI (original_program_at _ _ _ _ Prf.hyp0))

theorem concrete_original_polynomial_root_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (input (var 0) (var 1) (var 2) ⟶
      (pointCN rootF (rootData (var 0) (var 1) (var 2)) ⋏
      (pointBounds rootF (radius (var 0) (var 1) (var 2)) (rootData (var 0) (var 1) (var 2)) ⋏
      (pointCN valueF (valueData (var 0) (var 1) (var 2)) ⋏
      (GaussianGeneralPolynomialValueName.programZero valueF (valueData (var 0) (var 1) (var 2)) ⋏
        originalZero (var 0) (var 1) (var 2)))))) :=
  closeUniv 3 (.impI (concrete_root _ _ _ Prf.hyp0))

theorem concrete_original_polynomial_zero_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (input (var 0) (var 1) (var 2) ⟶
      bounded (evaluate (var 0) (ap2 rootF (precision (var 0) (var 1) (radius (var 0) (var 1) (var 2)) (var 3))
        (rootData (var 0) (var 1) (var 2)))) one (unit (var 3))) :=
  closeUniv 4 (.impI (original_zero_at _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianConstantPolynomialEvaluation
