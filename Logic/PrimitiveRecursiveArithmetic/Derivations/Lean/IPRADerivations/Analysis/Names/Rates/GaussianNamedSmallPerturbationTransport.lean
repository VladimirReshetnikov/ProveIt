import IPRADerivations.Analysis.Exponential.GaussianExponentialSmallPerturbation

/-!
# Exact named transport of a small multiplicative perturbation

The original prefactor observations are canonical, uniformly bounded by
M, and regular. Every actual correction observation is within 3A/B of
one. If Q is cross-equivalent to the actual normalized product program,
independent observations Q(p),H(q) are within 3MA/B+2^(-p)+2^(-q).

The proof retains the literal product query and normalization. An
arbitrary intermediate precision t contributes at most 2/2^t. Only
this vanishing auxiliary error is removed by the existing rational
slack theorem. The prefactor may vanish. No nonzero assumption,
desired global error, positivity of A or M, or regularity of the
correction/comparison programs is required.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianNamedSmallPerturbationTransport

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qmul canonical positive_product)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalSyntheticDivision (qone)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

def prefactorSamples (H : PR 2) (x M : PTm n) : Fm PTm n := .all
  (canonical (ap2 H (var 0) (Syn.shift x)) ⋏ bounded (ap2 H (var 0) (Syn.shift x)) (Syn.shift M) one)
def correctionSamples (E : PR 2) (y A B : PTm n) : Fm PTm n := .all
  (distanceBounded (ap2 E (var 0) (Syn.shift y)) qone (num 3*Syn.shift A) (Syn.shift B))
def productClock (H E : PR 2) (x y t : PTm n) : PTm n :=
  GaussianFastValueCut.exponent (GaussianNameArithmetic.multiplyModulus H E x y) t
def productSample (H E : PR 2) (x y t : PTm n) : PTm n :=
  ap2 (GaussianNameArithmetic.multiplyF H E) t (GaussianNameArithmetic.multiplyData H E x y)
def budgetNumerator (p q A B M : PTm n) : PTm n := num 3*M*A*unit p*unit q+B*(unit p+unit q)
def budgetDenominator (p q B : PTm n) : PTm n := B*unit p*unit q

@[simp] theorem subst_prefactorSamples {m : ℕ} (σ : Fin n → PTm m) (H : PR 2) (x M : PTm n) :
    (prefactorSamples H x M).subst σ = prefactorSamples H (Syn.subst σ x) (Syn.subst σ M) := by simp [prefactorSamples,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_correctionSamples {m : ℕ} (σ : Fin n → PTm m) (E : PR 2) (y A B : PTm n) :
    (correctionSamples E y A B).subst σ = correctionSamples E (Syn.subst σ y) (Syn.subst σ A) (Syn.subst σ B) := by simp [correctionSamples,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_productClock {m : ℕ} (σ : Fin n → PTm m) (H E : PR 2) (x y t : PTm n) :
    Syn.subst σ (productClock H E x y t) = productClock H E (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ t) := by simp [productClock]
@[simp] theorem subst_productSample {m : ℕ} (σ : Fin n → PTm m) (H E : PR 2) (x y t : PTm n) :
    Syn.subst σ (productSample H E x y t) = productSample H E (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ t) := by simp [productSample]
@[simp] theorem subst_budgetNumerator {m : ℕ} (σ : Fin n → PTm m) (p q A B M : PTm n) :
    Syn.subst σ (budgetNumerator p q A B M) = budgetNumerator (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ M) := by simp [budgetNumerator]
@[simp] theorem subst_budgetDenominator {m : ℕ} (σ : Fin n → PTm m) (p q B : PTm n) :
    Syn.subst σ (budgetDenominator p q B) = budgetDenominator (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ B) := by simp [budgetDenominator]

theorem prefactor_at (H : PR 2) (x M s : PTm n) (h : Γ ⊢[PRAAx] prefactorSamples H x M) : Γ ⊢[PRAAx]
    canonical (ap2 H s x) ⋏ bounded (ap2 H s x) M one := by simpa [prefactorSamples] using h.allE s
theorem correction_at (E : PR 2) (y A B s : PTm n) (h : Γ ⊢[PRAAx] correctionSamples E y A B) : Γ ⊢[PRAAx]
    distanceBounded (ap2 E s y) qone (num 3*A) B := by simpa [correctionSamples] using h.allE s

theorem recode_fixed (q : PTm n) (hq : Γ ⊢[PRAAx] canonical q) : Γ ⊢[PRAAx] GaussianFastValueCut.recode q ≐ q :=
  GaussianRationalHorner.canonical_unique _ _ _ _ (GaussianFastValueCut.recode_canonical q) hq
    (GaussianRationalL1.raw_den_positive q) (GaussianFastValueCut.recode_represents q) (GaussianRationalL1.raw_represents q)

/-- Literal normalization disappears only after actual canonicality of qmul has been proved. -/
theorem product_at (H E : PR 2) (x y t : PTm n) : Γ ⊢[PRAAx]
    productSample H E x y t ≐ qmul (ap2 H (productClock H E x y t) x) (ap2 E (productClock H E x y t) y) :=
  (GaussianNameArithmetic.multiply_at H E x y t).eqTrans (recode_fixed _ (GaussianRationalHorner.qmul_canonical _ _))

theorem product_prefactor_error (H E : PR 2) (x y A B M t : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hH : Γ ⊢[PRAAx] prefactorSamples H x M) (hE : Γ ⊢[PRAAx] correctionSamples E y A B) : Γ ⊢[PRAAx]
    distanceBounded (productSample H E x y t) (ap2 H (productClock H E x y t) x) (num 3*M*A) B := by
  have h := prefactor_at H x M (productClock H E x y t) hH
  have first := GaussianNameRingLaws.product_left_error _ _ _ (num 3*A) B M one hB
    (correction_at E y A B (productClock H E x y t) hE) h.andE₂ GaussianRationalReciprocal.qone_bounded
  exact distance_congr ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans (product_at H E x y t).eqSymm)
    (GaussianPolynomialDeterminantTerms.one_mul_canonical _ h.andE₁) (by ipra_ring) (.eqRefl _) first

theorem prefactor_query_error (H E : PR 2) (x y q t : PTm n) (hc : Γ ⊢[PRAAx] pointCN H x) : Γ ⊢[PRAAx]
    distanceBounded (ap2 H (productClock H E x y t) x) (ap2 H q x) (unit t+unit q) (unit t*unit q) := by
  have later : Γ ⊢[PRAAx] le (unit t) (unit (productClock H E x y t)) :=
    GaussianFactorBudget.power_monotone_length two t _ (le_succ_self one) (le_add_right _ _)
  apply distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive _) (unit_positive q))
    (positive_product _ _ (unit_positive t) (unit_positive q)) _
    (GaussianNameEquivalence.point_at H x (productClock H E x y t) q hc)
  ipra_le 𝔞 (unit q)*𝔞 (unit q)*sl later

theorem denominator_positive (p q B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] le one (budgetDenominator p q B) :=
  positive_product _ _ (positive_product _ _ hB (unit_positive p)) (unit_positive q)

/-- The only removable slack is the displayed auxiliary 2/2^t. -/
theorem independent_slack (H E Q : PR 2) (x y z M A B p q t : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hc : Γ ⊢[PRAAx] pointCN H x)
    (hH : Γ ⊢[PRAAx] prefactorSamples H x M) (hE : Γ ⊢[PRAAx] correctionSamples E y A B)
    (he : Γ ⊢[PRAAx] crossEquivalent Q (GaussianNameArithmetic.multiplyF H E) z (GaussianNameArithmetic.multiplyData H E x y)) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (qsub (ap2 Q p z) (ap2 H q x))
      (budgetNumerator p q A B M) (budgetDenominator p q B) two t := by
  have pt := positive_product (Γ := Γ) _ _ (unit_positive p) (unit_positive t)
  have tq := positive_product (Γ := Γ) _ _ (unit_positive t) (unit_positive q)
  have middle := GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ hB tq
    (product_prefactor_error H E x y A B M t hB hH hE) (prefactor_query_error H E x y q t hc)
  have chain := GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ pt (positive_product _ _ hB tq)
    (GaussianNameEquivalence.cross_at Q (GaussianNameArithmetic.multiplyF H E) z (GaussianNameArithmetic.multiplyData H E x y) p t he) middle
  change Γ ⊢[PRAAx] distanceBounded (ap2 Q p z) (ap2 H q x)
    (budgetNumerator p q A B M*unit t+two*budgetDenominator p q B) (budgetDenominator p q B*unit t)
  apply distance_radius_mono _ _ _ _ _ _ (positive_product _ _ pt (positive_product _ _ hB tq))
    (positive_product _ _ (denominator_positive p q B hB) (unit_positive t)) _ chain
  exact le_of_eq_add (d := zero) (by unfold budgetNumerator budgetDenominator; ipra_ring)

/-- Exact independent observation bound 3MA/B+2^(-p)+2^(-q). -/
theorem independent_error (H E Q : PR 2) (x y z M A B p q : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hc : Γ ⊢[PRAAx] pointCN H x)
    (hH : Γ ⊢[PRAAx] prefactorSamples H x M) (hE : Γ ⊢[PRAAx] correctionSamples E y A B)
    (he : Γ ⊢[PRAAx] crossEquivalent Q (GaussianNameArithmetic.multiplyF H E) z (GaussianNameArithmetic.multiplyData H E x y)) : Γ ⊢[PRAAx]
    distanceBounded (ap2 Q p z) (ap2 H q x) (budgetNumerator p q A B M) (budgetDenominator p q B) := by
  apply GaussianRationalSlackRemoval.slack_removal _ _ _ two (denominator_positive p q B hB)
  refine .allI ?_
  have bs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hB.shift
  have cs : Γ.map Fm.shift ⊢[PRAAx] pointCN H (Syn.shift x) := by simpa [Fm.shift,Syn.shift] using hc.shift
  have hs : Γ.map Fm.shift ⊢[PRAAx] prefactorSamples H (Syn.shift x) (Syn.shift M) := by simpa [Fm.shift,Syn.shift] using hH.shift
  have es : Γ.map Fm.shift ⊢[PRAAx] correctionSamples E (Syn.shift y) (Syn.shift A) (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hE.shift
  have eq : Γ.map Fm.shift ⊢[PRAAx] crossEquivalent Q (GaussianNameArithmetic.multiplyF H E) (Syn.shift z)
      (GaussianNameArithmetic.multiplyData H E (Syn.shift x) (Syn.shift y)) := by simpa [Fm.shift,Syn.shift] using he.shift
  simpa only [GaussianRationalSlackRemoval.allSlack,GaussianRationalMetric.subst_qsub,subst_ap2,subst_budgetNumerator,
    subst_budgetDenominator,Syn.shift,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    independent_slack H E Q (Syn.shift x) (Syn.shift y) (Syn.shift z) (Syn.shift M) (Syn.shift A) (Syn.shift B)
      (Syn.shift p) (Syn.shift q) (var 0) bs cs hs es eq

theorem actual_normalized_named_product_closed (H E : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (productSample H E (var 0) (var 1) (var 2) ≐ qmul (ap2 H (productClock H E (var 0) (var 1) (var 2)) (var 0))
      (ap2 E (productClock H E (var 0) (var 1) (var 2)) (var 1))) := closeUniv 3 (product_at H E _ _ _)
theorem original_named_small_perturbation_transport_closed (H E Q : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (le one (var 5) ⟶ pointCN H (var 0) ⟶ prefactorSamples H (var 0) (var 3) ⟶ correctionSamples E (var 1) (var 4) (var 5) ⟶
      crossEquivalent Q (GaussianNameArithmetic.multiplyF H E) (var 2) (GaussianNameArithmetic.multiplyData H E (var 0) (var 1)) ⟶
        distanceBounded (ap2 Q (var 6) (var 2)) (ap2 H (var 7) (var 0))
          (budgetNumerator (var 6) (var 7) (var 4) (var 5) (var 3)) (budgetDenominator (var 6) (var 7) (var 5))) :=
  closeUniv 8 (.impI (.impI (.impI (.impI (.impI (independent_error H E Q _ _ _ _ _ _ _ _ hyp2.wk.wk hyp2.wk hyp2 Prf.hyp1 Prf.hyp0))))))

end LeanProofs.IPRA.Analysis.GaussianNamedSmallPerturbationTransport
