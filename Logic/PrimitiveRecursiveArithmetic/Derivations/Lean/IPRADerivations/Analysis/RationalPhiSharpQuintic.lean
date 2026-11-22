import IPRADerivations.Analysis.RationalPhiSharpFamily
import IPRADerivations.Analysis.RationalBivariateGridCoefficients
import IPRADerivations.Foundations.BoundedDecision

/-!
# The literal expanded quintic sharpness example

The coefficient arrays and five named rational pairs are literal inputs.
Finite object Horner certificates use signed-integer representations, rather
than evaluating enormous sequence codes in the metatheory. Genuine grid
reflection links the expanded array to the checked general-Q construction.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalPhiSharpQuintic

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ConciseIPRA.PTm (zero succ app)
open LeanProofs.IPRA.PTm (num)
open RationalPolynomialGaussianEmbedding (horner hornerF horner_zero horner_succ evaluate embed_congr)
open RationalGaussianEmbedding (scalarZero scalarOne embed)
open RationalArithmetic (represents)
open GaussianRationalHorner (scalar_congr)
open GaussianRationalMonicReduction (singleton singleton_length singleton_lookup)
open LeanProofs.IPRA.Foundations.SequenceComposition (length append append_length append_left append_right entry_congr)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Only fixed literal coefficient lists use this finite proof generator. -/
def buffer : List (PTm n) → PTm n
  | [] => pairT zero zero
  | a::as => append (singleton a) (buffer as)
def signed (z : ℤ) : ZT n := if 0 ≤ z then ZT.ofNat (num z.toNat) else -ZT.ofNat (num (-z).toNat)
def integer (z : ℤ) : PTm n := RationalIntegerNormalization.normalize (signed z) one
def literal (cs : List ℤ) : PTm n := buffer (cs.map integer)
def model (cs : List ℤ) (a : ZT n) : ℕ → ZT n
  | 0 => ZT.ofNat zero
  | j+1 => model cs a j*a+signed (cs[j]?.getD 0)

theorem numeral_le (a b : ℕ) (h : a ≤ b) : Γ ⊢[PRAAx] le (num a) (num b) := by
  induction h with
  | refl => exact le_refl _
  | step h ih => exact le_trans ih (le_succ_self _)
theorem numeral_lt (a b : ℕ) (h : a < b) : Γ ⊢[PRAAx] lt (num a) (num b) := numeral_le _ _ h

theorem buffer_length (xs : List (PTm n)) : Γ ⊢[PRAAx] length (buffer xs) ≐ num xs.length := by
  induction xs with
  | nil => exact fst_pair _ _
  | cons a as ih => exact (append_length _ _).eqTrans ((congrAdd (singleton_length a) ih).eqTrans (by apply deriveNat; ipra_simps; simp only [List.length_cons,Nat.cast_add,Nat.cast_one]; ring))

theorem buffer_lookup (xs : List (PTm n)) (j : ℕ) (hj : j < xs.length) : Γ ⊢[PRAAx]
    entry (buffer xs) (num j) ≐ xs[j] := by
  induction xs generalizing j with
  | nil => simp at hj
  | cons a as ih =>
    cases j with
    | zero => exact (append_left (lt_congr (.eqRefl _) (singleton_length a).eqSymm (zero_lt_succ zero))).eqTrans (singleton_lookup a)
    | succ j =>
      have small : j < as.length := by simpa using hj
      have bound : Γ ⊢[PRAAx] lt (num j) (length (buffer as)) := lt_congr (.eqRefl _) (buffer_length as).eqSymm (numeral_lt j as.length small)
      have position : Γ ⊢[PRAAx] length (singleton a)+num j ≐ num (j+1) := (congrAdd (singleton_length a) (.eqRefl _)).eqTrans (by apply deriveNat; ipra_simps; simp only [Nat.cast_add,Nat.cast_one]; ring)
      exact (entry_congr (.eqRefl _) position.eqSymm).eqTrans ((append_right bound).eqTrans (ih j small))

theorem integer_represents (z : ℤ) : Γ ⊢[PRAAx] represents (integer z) (signed z) one :=
  RationalIntegerNormalization.normalize_preserves_value _ _ (le_refl one)

theorem add_represents_one (q r : PTm n) (a b : ZT n) (hq : Γ ⊢[PRAAx] represents q a one) (hr : Γ ⊢[PRAAx] represents r b one) :
    Γ ⊢[PRAAx] represents (RationalArithmetic.add q r) (a+b) one :=
  scalar_congr (.eqRefl _) (by apply ZT.derive; simp only [ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat,Q.mk_one,map_one]; ring)
    (one_mul one) (RationalRepresentations.represents_add q r a b one one hq hr)
theorem multiply_represents_one (q r : PTm n) (a b : ZT n) (hq : Γ ⊢[PRAAx] represents q a one) (hr : Γ ⊢[PRAAx] represents r b one) :
    Γ ⊢[PRAAx] represents (RationalArithmetic.multiply q r) (a*b) one :=
  scalar_congr (.eqRefl _) (ZT.derive rfl) (one_mul one) (RationalRepresentations.represents_multiply q r a b one one hq hr)

/-- The induction here unrolls a fixed literal's finite numeral certificate;
no interpreted value equality is substituted for an object derivation. -/
theorem horner_represents (cs : List ℤ) (C x : PTm n) (a : ZT n)
    (hx : Γ ⊢[PRAAx] represents x a one)
    (hc : ∀ j (hj : j < cs.length), Γ ⊢[PRAAx] represents (entry C (num j)) (signed cs[j]) one)
    (j : ℕ) (hj : j ≤ cs.length) : Γ ⊢[PRAAx] represents (horner C x (num j)) (model cs a j) one := by
  induction j with
  | zero => exact scalar_congr (horner_zero C x).eqSymm (ZT.derive rfl) (.eqRefl _) (RationalGaussianEmbedding.scalar_zero_represents one)
  | succ j ih =>
    have small : j < cs.length := by omega
    have coeff : Γ ⊢[PRAAx] represents (entry C (num j)) (signed (cs[j]?.getD 0)) one := by
      simpa only [List.getElem?_eq_getElem small,Option.getD_some] using hc j small
    exact scalar_congr (horner_succ C x (num j)).eqSymm (ZT.derive rfl) (.eqRefl _)
      (add_represents_one _ _ _ _ (multiply_represents_one _ _ _ _ (ih (by omega)) hx) coeff)

theorem literal_length (cs : List ℤ) : Γ ⊢[PRAAx] length (literal cs) ≐ num cs.length := by
  simpa [literal] using buffer_length (Γ := Γ) (cs.map integer)
theorem literal_lookup (cs : List ℤ) (j : ℕ) (hj : j < cs.length) : Γ ⊢[PRAAx] entry (literal cs) (num j) ≐ integer cs[j] := by
  have h := buffer_lookup (Γ := Γ) (cs.map (integer (n := n))) j (by simpa using hj)
  rw [List.getElem_map] at h
  exact h
theorem literal_evaluation_represents (cs : List ℤ) (x : PTm n) : Γ ⊢[PRAAx]
    represents (evaluate (literal cs) (GaussianRationalSyntheticBounds.natCode x)) (model cs (ZT.ofNat x) cs.length) one := by
  have actual : Γ ⊢[PRAAx] represents (horner (literal cs) (GaussianRationalSyntheticBounds.natCode x) (num cs.length)) (model cs (ZT.ofNat x) cs.length) one :=
    horner_represents cs (literal cs) (GaussianRationalSyntheticBounds.natCode x) (ZT.ofNat x)
    (GaussianRationalSyntheticBounds.natCode_represents x)
    (fun j hj => scalar_congr (literal_lookup cs j hj).eqSymm (ZT.derive rfl) (.eqRefl _) (integer_represents _)) cs.length (Nat.le_refl _)
  exact scalar_congr (congrAp3 hornerF (literal_length cs) (.eqRefl _) (.eqRefl _)).eqSymm (ZT.derive rfl) (.eqRefl _) actual

def Q : PTm n := literal [1,0,1]
def quintic : PTm n := literal [1,-14,85,-223,274,-119]
def family : PTm n := RationalPhiSharpFamily.polynomial Q (num 2) (num 2) (num 5)

theorem horner_step_represents (C x j : PTm n) (a b c : ZT n)
    (hx : Γ ⊢[PRAAx] represents x a one) (hb : Γ ⊢[PRAAx] represents (horner C x j) b one)
    (hc : Γ ⊢[PRAAx] represents (entry C j) c one) : Γ ⊢[PRAAx] represents (horner C x (succ j)) (b*a+c) one :=
  scalar_congr (horner_succ C x j).eqSymm (ZT.derive rfl) (.eqRefl _)
    (add_represents_one _ _ _ _ (multiply_represents_one _ _ _ _ hb hx) hc)

theorem linear_represents (j x : PTm n) : Γ ⊢[PRAAx]
    represents (evaluate (RationalConsecutiveFactorProduct.linear j) (GaussianRationalSyntheticBounds.natCode x))
      (ZT.ofNat x-ZT.ofNat (succ j)) one := by
  let C := RationalConsecutiveFactorProduct.linear j
  let z := GaussianRationalSyntheticBounds.natCode x
  have hx : Γ ⊢[PRAAx] represents z (ZT.ofNat x) one := GaussianRationalSyntheticBounds.natCode_represents x
  have base : Γ ⊢[PRAAx] represents (horner C z zero) (ZT.ofNat zero) one :=
    scalar_congr (horner_zero C z).eqSymm (ZT.derive rfl) (.eqRefl _) (RationalGaussianEmbedding.scalar_zero_represents one)
  have head : Γ ⊢[PRAAx] represents (entry C zero) (ZT.ofNat one) one :=
    scalar_congr (RationalConsecutiveFactorProduct.linear_head j).eqSymm (ZT.derive rfl) (.eqRefl _)
      (RationalIntegerNormalization.normalize_preserves_value _ _ (le_refl one))
  have oneStep : Γ ⊢[PRAAx] represents (horner C z one) (ZT.ofNat one) one :=
    scalar_congr (.eqRefl _) (by apply ZT.derive; simp only [ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat,Q.mk_zero,map_zero]; ring) (.eqRefl _)
      (horner_step_represents C z zero _ _ _ hx base head)
  have tail : Γ ⊢[PRAAx] represents (entry C one) (-ZT.ofNat (succ j)) one :=
    scalar_congr (RationalConsecutiveFactorProduct.linear_tail j).eqSymm (ZT.derive rfl) (.eqRefl _)
      (RationalRepresentations.represents_negative _ _ _ (GaussianRationalSyntheticBounds.natCode_represents (succ j)))
  have twoSteps : Γ ⊢[PRAAx] represents (horner C z (num 2)) (ZT.ofNat x-ZT.ofNat (succ j)) one :=
    scalar_congr (.eqRefl _) (by apply ZT.derive; simp only [ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat,ZT.toZ_neg,ZT.toZ_sub,Q.mk_one,map_one]; ring) (.eqRefl _)
      (horner_step_represents C z one _ _ _ hx oneStep tail)
  exact scalar_congr (congrAp3 hornerF (RationalConsecutiveFactorProduct.linear_length j) (.eqRefl _) (.eqRefl _)).eqSymm
    (ZT.derive rfl) (.eqRefl _) twoSteps

def consecutiveModel (x : PTm n) : ℕ → ZT n
  | 0 => ZT.ofNat one
  | j+1 => consecutiveModel x j * (ZT.ofNat x-ZT.ofNat (num (j+1)))

theorem consecutive_represents (k : ℕ) (x : PTm n) : Γ ⊢[PRAAx]
    represents (evaluate (RationalConsecutiveFactorProduct.consecutive (num k)) (GaussianRationalSyntheticBounds.natCode x)) (consecutiveModel x k) one := by
  let z := GaussianRationalSyntheticBounds.natCode x
  induction k with
  | zero =>
    have singletonCode : Γ ⊢[PRAAx] evaluate (singleton scalarOne) z ≐ scalarOne :=
      RationalPolynomialBuffersGaussianEmbedding.canonical_equal_of_embedding _ _ (RationalPolynomialGaussianEmbedding.horner_canonical _ _ _)
        (RationalNormalForm.normalize_well_formed _ _ (le_refl one))
        ((RationalPolynomialPowers.singleton_evaluation z).eqTrans RationalGaussianEmbedding.embed_one.eqSymm)
    have code := (RationalPolynomialPowers.evaluation_congr (RationalConsecutiveFactorProduct.consecutive_zero (Γ := Γ)) (.eqRefl z)).eqTrans singletonCode
    exact scalar_congr code.eqSymm (ZT.derive rfl) (.eqRefl _)
      (RationalIntegerNormalization.normalize_preserves_value _ _ (le_refl one))
  | succ k ih =>
    have code := (RationalPolynomialPowers.evaluation_congr (RationalConsecutiveFactorProduct.consecutive_succ (Γ := Γ) (num k)) (.eqRefl z)).eqTrans
      (RationalPolynomialProductGaussianEmbedding.product_evaluation _ _ _ _ _
        (RationalConsecutiveFactorProduct.consecutive_length (num k)) (RationalConsecutiveFactorProduct.linear_length (num k)))
    exact scalar_congr code.eqSymm (ZT.derive rfl) (.eqRefl _)
      (multiply_represents_one _ _ _ _ ih (linear_represents (num k) x))

theorem Q_length : Γ ⊢[PRAAx] length (Q : PTm n) ≐ num 3 := literal_length [1,0,1]
theorem quintic_length : Γ ⊢[PRAAx] length (quintic : PTm n) ≐ num 6 := literal_length [1,-14,85,-223,274,-119]
theorem Q_value (x : PTm n) : Γ ⊢[PRAAx]
    represents (evaluate Q (GaussianRationalSyntheticBounds.natCode x)) (ZT.ofNat (x*x+one)) one :=
  scalar_congr (.eqRefl _) (by apply ZT.derive; simp [model,signed,ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat,Q.mk_add,Q.mk_mul]) (.eqRefl _)
    (literal_evaluation_represents [1,0,1] x)

theorem square_represents (q : PTm n) (a : ZT n) (hq : Γ ⊢[PRAAx] represents q a one) : Γ ⊢[PRAAx]
    represents (RationalScalarPowerGaussianEmbedding.power q (num 2)) (a*a) one := by
  have base : Γ ⊢[PRAAx] represents (RationalScalarPowerGaussianEmbedding.power q zero) (ZT.ofNat one) one :=
    scalar_congr (RationalScalarPowerGaussianEmbedding.power_zero q).eqSymm (ZT.derive rfl) (.eqRefl _)
      (RationalIntegerNormalization.normalize_preserves_value _ _ (le_refl one))
  have first : Γ ⊢[PRAAx] represents (RationalScalarPowerGaussianEmbedding.power q one) a one :=
    scalar_congr (RationalScalarPowerGaussianEmbedding.power_succ q zero).eqSymm
      (by apply ZT.derive; simp only [ZT.toZ_mul,ZT.toZ_ofNat,Q.mk_one,map_one]; ring) (.eqRefl _)
      (multiply_represents_one _ _ _ _ base hq)
  exact scalar_congr (RationalScalarPowerGaussianEmbedding.power_succ q one).eqSymm (ZT.derive rfl) (.eqRefl _)
    (multiply_represents_one _ _ _ _ first hq)

theorem family_natural_value (x : PTm n) : Γ ⊢[PRAAx]
    represents (evaluate family (GaussianRationalSyntheticBounds.natCode x))
      (ZT.ofNat (x*x+one)*ZT.ofNat (x*x+one)+consecutiveModel x 5) one := by
  let z := GaussianRationalSyntheticBounds.natCode x
  have budget : Γ ⊢[PRAAx] le ((num 2)*(num 2)) (num 5) := by
    exact le_congr (by ipra_ring : Γ ⊢[PRAAx] num 4 ≐ num 2*num 2) (.eqRefl _) (numeral_le 4 5 (by decide))
  have code := (RationalPolynomialBuffersGaussianEmbedding.added_evaluation
    (RationalPhiSharpFamily.powered Q (num 2) (num 2) (num 5)) (RationalConsecutiveFactorProduct.consecutive (num 5)) (num 6) z
    (RationalPhiSharpFamily.powered_length _ _ _ _ budget) (RationalConsecutiveFactorProduct.consecutive_length (num 5))).eqTrans
      (RationalAlgebra.add_congr ((RationalPolynomialBuffersGaussianEmbedding.pad_evaluation _ _ _).eqTrans
        (RationalPolynomialPowers.power_evaluation Q (num 2) (num 2) z Q_length)) (.eqRefl _))
  exact scalar_congr code.eqSymm (ZT.derive rfl) (.eqRefl _)
    (add_represents_one _ _ _ _ (square_represents _ _ (Q_value x)) (consecutive_represents 5 x))

/-- The six-step signed-integer Horner certificate proves the literal
expanded identity at every original natural query, without computing codes. -/
theorem expanded_natural_evaluation (x : PTm n) : Γ ⊢[PRAAx]
    evaluate family (GaussianRationalSyntheticBounds.natCode x) ≐ evaluate quintic (GaussianRationalSyntheticBounds.natCode x) := by
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (RationalPolynomialGaussianEmbedding.horner_canonical _ _ _)
    (RationalPolynomialGaussianEmbedding.horner_canonical _ _ _) (family_natural_value x)
    (literal_evaluation_represents [1,-14,85,-223,274,-119] x) (le_refl one) (le_refl one)
  apply ZT.derive
  simp [model,consecutiveModel,signed,ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat,ZT.toZ_neg,ZT.toZ_sub,Q.mk_add,Q.mk_mul,Q.mk_num]
  norm_num [map_ofNat]
  ring

@[simp] theorem subst_signed {m : ℕ} (σ : Fin n → PTm m) (z : ℤ) : (signed z : ZT n).subst σ = signed z := by
  by_cases h : 0 ≤ z
  · simp [signed,h,ZT.subst,ZT.ofNat]
  · simp only [signed,if_neg h]
    change (⟨Syn.subst σ zero,Syn.subst σ (num (-z).toNat)⟩ : ZT m) = ⟨zero,num (-z).toNat⟩
    simp
@[simp] theorem subst_integer {m : ℕ} (σ : Fin n → PTm m) (z : ℤ) : Syn.subst σ (integer z : PTm n) = integer z := by simp [integer]
@[simp] theorem subst_literal {m : ℕ} (σ : Fin n → PTm m) (cs : List ℤ) : Syn.subst σ (literal cs : PTm n) = literal cs := by
  induction cs with
  | nil => simp [literal,buffer]
  | cons a as ih =>
    change Syn.subst σ (append (singleton (integer a)) (literal as)) = append (singleton (integer a)) (literal as)
    simp only [Foundations.SequenceComposition.subst_append,GaussianRationalMonicReduction.subst_singleton,subst_integer,ih]
@[simp] theorem subst_Q {m : ℕ} (σ : Fin n → PTm m) : Syn.subst σ (Q : PTm n) = Q := subst_literal σ _
@[simp] theorem subst_quintic {m : ℕ} (σ : Fin n → PTm m) : Syn.subst σ (quintic : PTm n) = quintic := subst_literal σ _
@[simp] theorem subst_family {m : ℕ} (σ : Fin n → PTm m) : Syn.subst σ (family : PTm n) = family := by simp [family]

theorem family_length : Γ ⊢[PRAAx] length (family : PTm n) ≐ num 6 := RationalPhiSharpFamily.polynomial_length _ _ _ _

theorem embedded_grid_evaluation (C : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ num 6) (x : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalHorner.evaluate (RationalPolynomialGaussianEmbedding.coefficients C (num 6)) (GaussianRationalFiniteGridIdentity.gridPoint x) ≐
      embed (evaluate C (GaussianRationalSyntheticBounds.natCode x)) :=
  (GaussianRationalMonicReduction.evaluate_congr (.eqRefl _) (RationalBivariateGridCoefficients.grid_point_embedding x).eqSymm).eqTrans
    (RationalPolynomialBuffersGaussianEmbedding.evaluation_at_width C (num 6) (GaussianRationalSyntheticBounds.natCode x) hC).eqSymm

theorem expanded_grid_equal : Γ ⊢[PRAAx] GaussianRationalGridCoefficientEquality.gridEqual
    (RationalPolynomialGaussianEmbedding.coefficients family (num 6)) (RationalPolynomialGaussianEmbedding.coefficients quintic (num 6)) (num 5) := by
  refine .allI (.impI ?_)
  let Δ := le (var 0) (num 5) :: Γ.map Fm.shift
  have e : Δ ⊢[PRAAx] GaussianRationalHorner.evaluate (RationalPolynomialGaussianEmbedding.coefficients family (num 6)) (GaussianRationalFiniteGridIdentity.gridPoint (var 0)) ≐
      GaussianRationalHorner.evaluate (RationalPolynomialGaussianEmbedding.coefficients quintic (num 6)) (GaussianRationalFiniteGridIdentity.gridPoint (var 0)) :=
    (embedded_grid_evaluation family family_length (var 0)).eqTrans
      ((embed_congr (expanded_natural_evaluation (var 0))).eqTrans (embedded_grid_evaluation quintic quintic_length (var 0)).eqSymm)
  simpa [Δ,Syn.shift] using e

theorem expanded_coefficient_embedding (k : PTm n) (hk : Γ ⊢[PRAAx] le k (num 5)) : Γ ⊢[PRAAx]
    embed (entry family k) ≐ embed (entry quintic k) := by
  have bound : Γ ⊢[PRAAx] lt k (num 6) := (succ_monus_succ k (num 5)).eqTrans hk
  have actual := GaussianRationalGridCoefficientEquality.coefficient_equal
    (RationalPolynomialGaussianEmbedding.coefficients family (num 6)) (RationalPolynomialGaussianEmbedding.coefficients quintic (num 6)) (num 5) k
    (RationalPolynomialGaussianEmbedding.coefficients_length _ _) (RationalPolynomialGaussianEmbedding.coefficients_length _ _)
    (RationalPolynomialGaussianEmbedding.coefficients_canonical _ _) (RationalPolynomialGaussianEmbedding.coefficients_canonical _ _) expanded_grid_equal hk
  exact (RationalPolynomialGaussianEmbedding.coefficient_lookup family (num 6) k bound).eqSymm.eqTrans
    (actual.eqTrans (RationalPolynomialGaussianEmbedding.coefficient_lookup quintic (num 6) k bound))

theorem well_formed_congr {q r : PTm n} (h : Γ ⊢[PRAAx] q ≐ r) (hr : Γ ⊢[PRAAx] RationalNormalForm.wellFormed r) : Γ ⊢[PRAAx]
    RationalNormalForm.wellFormed q := by
  let φ := RationalNormalForm.wellFormed (var 0 : PTm (n+1))
  have a : Γ ⊢[PRAAx] φ.subst (Syn.inst r) := by simpa [φ] using hr
  simpa [φ] using Prf.eqSubst1 φ h.eqSymm a

theorem family_coefficient_canonical (k : PTm n) (hk : Γ ⊢[PRAAx] le k (num 5)) : Γ ⊢[PRAAx] RationalNormalForm.wellFormed (entry family k) :=
  well_formed_congr (RationalPolynomialBuffersGaussianEmbedding.added_lookup _ _ _ _ ((succ_monus_succ _ _).eqTrans hk)) (RationalArithmetic.add_guard _ _)
theorem quintic_coefficient_canonical (k : PTm n) (hk : Γ ⊢[PRAAx] le k (num 5)) : Γ ⊢[PRAAx] RationalNormalForm.wellFormed (entry quintic k) := by
  refine Foundations.BoundedDecision.cases_num 5 hk (fun j hj => .impI ?_)
  have small : j < ([1,-14,85,-223,274,-119] : List ℤ).length := by simp; omega
  have code := (entry_congr (.eqRefl (quintic : PTm n)) (Prf.hyp0 : (k ≐ num j) :: Γ ⊢[PRAAx] k ≐ num j)).eqTrans
    (literal_lookup [1,-14,85,-223,274,-119] j small)
  exact well_formed_congr code (RationalNormalForm.normalize_well_formed _ _ (le_refl one))
theorem expanded_coefficient (k : PTm n) (hk : Γ ⊢[PRAAx] le k (num 5)) : Γ ⊢[PRAAx] entry family k ≐ entry quintic k :=
  RationalPolynomialBuffersGaussianEmbedding.canonical_equal_of_embedding _ _ (family_coefficient_canonical k hk) (quintic_coefficient_canonical k hk)
    (expanded_coefficient_embedding k hk)

/-- Grid reflection has derived all coefficients; it now transports actual
Horner evaluation at every original rational query. -/
theorem expanded_evaluation (z : PTm n) : Γ ⊢[PRAAx] evaluate family z ≐ evaluate quintic z := by
  have entries : Γ ⊢[PRAAx] RationalPolynomialBuffersGaussianEmbedding.embeddedEntries family
      (RationalPolynomialGaussianEmbedding.coefficients quintic (num 6)) (num 6) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (num 6) :: Γ.map Fm.shift
    have bound : Δ ⊢[PRAAx] le (var 0) (num 5) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
    have e := (expanded_coefficient_embedding (var 0) bound).eqTrans
      (RationalPolynomialGaussianEmbedding.coefficient_lookup quintic (num 6) (var 0) (Γ := Δ) Prf.hyp0).eqSymm
    simpa [Δ,Syn.shift] using e
  exact RationalPolynomialBuffersGaussianEmbedding.canonical_equal_of_embedding _ _ (RationalPolynomialGaussianEmbedding.horner_canonical _ _ _)
    (RationalPolynomialGaussianEmbedding.horner_canonical _ _ _)
    ((RationalPolynomialBuffersGaussianEmbedding.evaluation_transport _ _ _ z family_length
      (RationalPolynomialGaussianEmbedding.coefficients_length _ _) entries).eqTrans
        (RationalPolynomialBuffersGaussianEmbedding.evaluation_at_width quintic (num 6) z quintic_length).eqSymm)

theorem Q_evaluation_code (x : PTm n) : Γ ⊢[PRAAx] evaluate Q (GaussianRationalSyntheticBounds.natCode x) ≐
    GaussianRationalSyntheticBounds.natCode (x*x+one) := by
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (RationalPolynomialGaussianEmbedding.horner_canonical _ _ _)
    (RationalNormalForm.normalize_well_formed _ _ (le_refl one)) (Q_value x) (GaussianRationalSyntheticBounds.natCode_represents _)
    (le_refl one) (le_refl one)
  exact ZT.derive rfl

theorem natCode_congr {x y : PTm n} (h : Γ ⊢[PRAAx] x ≐ y) : Γ ⊢[PRAAx] GaussianRationalSyntheticBounds.natCode x ≐ GaussianRationalSyntheticBounds.natCode y := by
  simpa only [GaussianRationalSyntheticBounds.subst_natCode,Syn.subst_var,Matrix.cons_val_zero] using
    Prf.eqCongr (Γ := Γ) (GaussianRationalSyntheticBounds.natCode (var 0) : PTm 1) (σ := ![x]) (σ' := ![y]) (fun i => by fin_cases i; exact h)
theorem integer_natural (k : ℕ) : (integer (k : ℤ) : PTm n) = GaussianRationalSyntheticBounds.natCode (num k) := by
  simp [integer,signed,GaussianRationalSyntheticBounds.natCode]

def pointList : PTm n := RationalPhiSharpFamily.points Q (num 5)
def witness : PTm n := RationalPhiSharpFamily.hyperplane Q (num 2)
def point1 : PTm n := pairT (integer 1) (integer 2)
def point2 : PTm n := pairT (integer 2) (integer 5)
def point3 : PTm n := pairT (integer 3) (integer 10)
def point4 : PTm n := pairT (integer 4) (integer 17)
def point5 : PTm n := pairT (integer 5) (integer 26)
@[simp] theorem subst_pointList {m : ℕ} (σ : Fin n → PTm m) : Syn.subst σ (pointList : PTm n) = pointList := by simp [pointList]
@[simp] theorem subst_witness {m : ℕ} (σ : Fin n → PTm m) : Syn.subst σ (witness : PTm n) = witness := by simp [witness]

theorem named_point (j : ℕ) (hj : j < 5) : Γ ⊢[PRAAx] entry pointList (num j) ≐
    pairT (integer ((j+1 : ℕ) : ℤ)) (integer (((j+1)*(j+1)+1 : ℕ) : ℤ)) := by
  rw [integer_natural,integer_natural]
  have number : Γ ⊢[PRAAx] succ (num j)*succ (num j)+one ≐ num ((j+1)*(j+1)+1) := by
    apply deriveNat
    ipra_simps
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_one]
    ring
  exact (RationalPhiSharpFamily.point_lookup Q (num 5) (num j) (numeral_lt j 5 hj)).eqTrans
    (congrPairT (.eqRefl _) ((Q_evaluation_code (succ (num j))).eqTrans (natCode_congr number)))

theorem first_point : Γ ⊢[PRAAx] entry (pointList : PTm n) zero ≐ point1 := named_point 0 (by decide)
theorem second_point : Γ ⊢[PRAAx] entry (pointList : PTm n) one ≐ point2 := named_point 1 (by decide)
theorem third_point : Γ ⊢[PRAAx] entry (pointList : PTm n) (num 2) ≐ point3 := named_point 2 (by decide)
theorem fourth_point : Γ ⊢[PRAAx] entry (pointList : PTm n) (num 3) ≐ point4 := named_point 3 (by decide)
theorem fifth_point : Γ ⊢[PRAAx] entry (pointList : PTm n) (num 4) ≐ point5 := named_point 4 (by decide)
theorem pointList_length : Γ ⊢[PRAAx] length (pointList : PTm n) ≐ num 5 := RationalPhiSharpFamily.points_length _ _
theorem pointList_distinct : Γ ⊢[PRAAx] RationalCurvePointsGaussianEmbedding.distinct (pointList : PTm n) := RationalPhiSharpFamily.points_distinct _ _

theorem budget : Γ ⊢[PRAAx] le ((num 2)*(num 2) : PTm n) (num 5) :=
  le_congr (by ipra_ring : Γ ⊢[PRAAx] num 4 ≐ num 2*num 2) (.eqRefl _) (numeral_le 4 5 (by decide))
theorem strict_budget : Γ ⊢[PRAAx] lt ((num 2)*(num 2) : PTm n) (num 5) :=
  lt_congr (by ipra_ring : Γ ⊢[PRAAx] num 4 ≐ num 2*num 2) (.eqRefl _) (numeral_lt 4 5 (by decide))
theorem quintic_head : Γ ⊢[PRAAx] entry (quintic : PTm n) zero ≐ scalarOne := literal_lookup _ 0 (by decide)
theorem quintic_curve_input : Γ ⊢[PRAAx] RationalPhiSectionNonzero.curveInput (quintic : PTm n) (num 2) (num 2) (num 5) := by
  have nonzero : Γ ⊢[PRAAx] neg (RationalArgmin.rationalEq (entry (quintic : PTm n) zero) scalarZero) :=
    .impI (.impE RationalPhiSection.unit_nonzero (RationalArgmin.rationalEq_congr quintic_head.wk (.eqRefl _) Prf.hyp0))
  exact .andI (numeral_le 1 2 (by decide)) (.andI quintic_length (.andI nonzero strict_budget))

theorem points_on_quintic : Γ ⊢[PRAAx] RationalSuperellipticNormDegree.pointPowers (quintic : PTm n) (num 2) pointList := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (length (pointList : PTm (n+1))) :: Γ.map Fm.shift
  have j : Δ ⊢[PRAAx] lt (var 0) (num 5) := lt_congr (.eqRefl _) pointList_length Prf.hyp0
  have source := RationalPhiSharpFamily.curve_point_at (Γ := Δ) Q (num 2) (num 2) (num 5) (var 0) Q_length budget j
  have result := RationalArgmin.rationalEq_congr (.eqRefl _) (expanded_evaluation (GaussianRationalFiberGrouping.abscissa pointList (var 0))) source
  simpa [Δ,Syn.shift,pointList,family] using result

theorem witness_length : Γ ⊢[PRAAx] length (witness : PTm n) ≐ num 4 := RationalPhiSharpFamily.hyperplane_length _ _
theorem witness_nonzero : Γ ⊢[PRAAx] RationalPhiSectionZero.nonzero (witness : PTm n) (num 2) := RationalPhiSharpFamily.hyperplane_nonzero _ _
theorem feature_dot_zero : Γ ⊢[PRAAx] RationalPhiSection.dotEquations (witness : PTm n) (num 2) pointList := RationalPhiSharpFamily.points_dot _ _ _ Q_length

theorem negative_integer_certificate (z : ℤ) (h : Γ ⊢[PRAAx] ZT.eq (-(signed z : ZT n)) (signed (-z))) : Γ ⊢[PRAAx]
    RationalArithmetic.negative (integer z) ≐ integer (-z) := by
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (RationalArithmetic.negative_guard _)
    (RationalNormalForm.normalize_well_formed _ _ (le_refl one))
    (RationalRepresentations.represents_negative _ _ _ (integer_represents z)) (integer_represents (-z)) (le_refl one) (le_refl one)
  apply ZT.derive
  have e := ZT.toZ_eq h
  simp only [ZT.toZ_mul,ZT.toZ_ofNat,Q.mk_one,map_one,mul_one]
  exact e

theorem negative_one_code : Γ ⊢[PRAAx] RationalArithmetic.negative (integer (1 : ℤ) : PTm n) ≐ integer (-1) :=
  negative_integer_certificate 1 (by apply ZT.derive; simp [signed,ZT.toZ_neg,ZT.toZ_ofNat,map_one])
theorem negative_zero_code : Γ ⊢[PRAAx] RationalArithmetic.negative (integer (0 : ℤ) : PTm n) ≐ integer 0 :=
  negative_integer_certificate 0 (by apply ZT.derive; simp [signed,ZT.toZ_neg,ZT.toZ_ofNat,map_zero])

theorem witness_first : Γ ⊢[PRAAx] entry (witness : PTm n) zero ≐ integer (-1) :=
  (RationalPhiSharpFamily.hyperplane_old Q (num 2) zero (zero_le _)).eqTrans
    ((RationalAlgebra.negative_congr ((entry_congr (.eqRefl Q) (monus_zero (num 2))).eqTrans
      (literal_lookup [1,0,1] 2 (by decide)))).eqTrans negative_one_code)
theorem witness_second : Γ ⊢[PRAAx] entry (witness : PTm n) one ≐ integer 0 := by
  have whereIndex : Γ ⊢[PRAAx] LeanProofs.IPRA.PTm.monus (num 2) one ≐ one := (succ_monus_succ one zero).eqTrans (monus_zero one)
  exact (RationalPhiSharpFamily.hyperplane_old Q (num 2) one (le_succ_self one)).eqTrans
    ((RationalAlgebra.negative_congr ((entry_congr (.eqRefl Q) whereIndex).eqTrans
      (literal_lookup [1,0,1] 1 (by decide)))).eqTrans negative_zero_code)
theorem witness_third : Γ ⊢[PRAAx] entry (witness : PTm n) (num 2) ≐ integer (-1) :=
  (RationalPhiSharpFamily.hyperplane_old Q (num 2) (num 2) (le_refl _)).eqTrans
    ((RationalAlgebra.negative_congr ((entry_congr (.eqRefl Q) (monus_self (num 2))).eqTrans
      (literal_lookup [1,0,1] 0 (by decide)))).eqTrans negative_one_code)
theorem witness_fourth : Γ ⊢[PRAAx] entry (witness : PTm n) (num 3) ≐ integer 1 := RationalPhiSharpFamily.hyperplane_last Q (num 2)

theorem quintic_degree : Γ ⊢[PRAAx] RationalPolynomialDegreeGaussianEmbedding.degree (quintic : PTm n) (num 5) ≐ num 5 := by
  have head := (embed_congr (quintic_head (Γ := Γ))).eqTrans RationalGaussianEmbedding.embed_one
  have ne : Γ ⊢[PRAAx] neg (RationalArithmetic.recode (entry (quintic : PTm n) zero) ≐ scalarZero) := by
    refine .impI (.impE GaussianRationalCurveFibers.gaussian_one_nonzero ?_)
    exact head.wk.eqSymm.eqTrans ((RationalGaussianEmbedding.embed_recode _).eqSymm.eqTrans
      ((embed_congr Prf.hyp0).eqTrans RationalGaussianEmbedding.embed_zero))
  have small := RationalPolynomialDegreeGaussianEmbedding.first_from_witness quintic (num 5) zero (zero_lt_succ (num 5)) ne
  have first := le_antisymm small (zero_le _)
  exact (congrMonus (.eqRefl _) first).eqTrans (monus_zero _)

/-- The actual generic construction, its literal expansion, point list
and explicitly checked integer feature vector are returned together. -/
def output : PTm n := pairT family (pairT quintic (pairT pointList witness))
def outputF : PR 0 := PTm.toPR (output : PTm 0)
def run : PTm n := app outputF Fin.elim0
@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) : Syn.subst σ (output : PTm n) = output := by simp [output]
theorem program_at : Γ ⊢[PRAAx] (run : PTm n) ≐ output := by
  simpa only [run,outputF,subst_output] using toPR_eq (Γ := Γ) (output : PTm 0) (Fin.elim0 : Fin 0 → PTm n)
theorem returned_family : Γ ⊢[PRAAx] fstT (run : PTm n) ≐ family := (congrFst program_at).eqTrans (fst_pair _ _)
theorem returned_tail : Γ ⊢[PRAAx] sndT (run : PTm n) ≐ pairT quintic (pairT pointList witness) := (congrSnd program_at).eqTrans (snd_pair _ _)
theorem returned_quintic : Γ ⊢[PRAAx] fstT (sndT (run : PTm n)) ≐ quintic := (congrFst returned_tail).eqTrans (fst_pair _ _)
theorem returned_data : Γ ⊢[PRAAx] sndT (sndT (run : PTm n)) ≐ pairT pointList witness := (congrSnd returned_tail).eqTrans (snd_pair _ _)
theorem returned_points : Γ ⊢[PRAAx] fstT (sndT (sndT (run : PTm n))) ≐ pointList := (congrFst returned_data).eqTrans (fst_pair _ _)
theorem returned_witness : Γ ⊢[PRAAx] sndT (sndT (sndT (run : PTm n))) ≐ witness := (congrSnd returned_data).eqTrans (snd_pair _ _)

theorem actual_quintic_expanded_coefficients_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] .all
    (le (var 0) (num 5) ⟶ entry (family : PTm 1) (var 0) ≐ entry (quintic : PTm 1) (var 0)) :=
  .allI (.impI (expanded_coefficient _ Prf.hyp0))
theorem actual_quintic_expanded_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (evaluate (family : PTm 1) (var 0) ≐ evaluate (quintic : PTm 1) (var 0)) := closeUniv 1 (expanded_evaluation _)
theorem actual_quintic_degree_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx]
    (length (quintic : PTm 0) ≐ num 6 ⋏ RationalPolynomialDegreeGaussianEmbedding.degree quintic (num 5) ≐ num 5) :=
  .andI quintic_length quintic_degree

theorem actual_quintic_five_named_points_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx]
    (length (pointList : PTm 0) ≐ num 5 ⋏ (entry pointList zero ≐ point1 ⋏ (entry pointList one ≐ point2 ⋏
      (entry pointList (num 2) ≐ point3 ⋏ (entry pointList (num 3) ≐ point4 ⋏ entry pointList (num 4) ≐ point5))))) :=
  .andI pointList_length (.andI first_point (.andI second_point (.andI third_point (.andI fourth_point fifth_point))))

theorem actual_quintic_curve_points_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx]
    (RationalPhiSectionNonzero.curveInput (quintic : PTm 0) (num 2) (num 2) (num 5) ⋏
      (RationalCurvePointsGaussianEmbedding.distinct pointList ⋏ RationalSuperellipticNormDegree.pointPowers quintic (num 2) pointList)) :=
  .andI quintic_curve_input (.andI pointList_distinct points_on_quintic)

theorem actual_quintic_feature_witness_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx]
    (length (witness : PTm 0) ≐ num 4 ⋏ (RationalPhiSectionZero.nonzero witness (num 2) ⋏
      (entry witness zero ≐ integer (-1) ⋏ (entry witness one ≐ integer 0 ⋏
        (entry witness (num 2) ≐ integer (-1) ⋏ (entry witness (num 3) ≐ integer 1 ⋏
          RationalPhiSection.dotEquations witness (num 2) pointList)))))) :=
  .andI witness_length (.andI witness_nonzero (.andI witness_first (.andI witness_second (.andI witness_third (.andI witness_fourth feature_dot_zero)))))

theorem actual_quintic_example_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] (run : PTm 0) ≐ output := program_at

end LeanProofs.IPRA.Analysis.RationalPhiSharpQuintic
