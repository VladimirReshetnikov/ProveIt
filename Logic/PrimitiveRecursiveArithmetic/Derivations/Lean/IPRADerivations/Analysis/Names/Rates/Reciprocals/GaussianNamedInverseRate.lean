import IPRADerivations.Analysis.Names.Rates.Reciprocals.GaussianApproximateInverseDistance
import IPRADerivations.Analysis.Exponential.Names.GaussianExponentialSmallPerturbation

/-!
# The exact C15 rate for bounded inverse names

Actual regular names P,Q have independent observation error D/N plus
their ordinary dyadic errors. Actual inverse candidates I,J are regular,
their samples have the exact rational bound A/B, and their original
multiplication programs are cross-equivalent to one. Then independent
I(p),J(q) have error (A/B)²D/N+2^(-p)+2^(-q).

The product identities first yield finite raw residuals, with explicit
constants computed from the actual multiplication moduli. The finite
inverse-distance theorem retains the exact fractional factor. Only the
remaining auxiliary dyadic errors are removed by rational slack removal.
No nonzero-value or inverse-distance law is supplied as a premise.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianNamedInverseRate

open_ipra
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalSyntheticDivision (qone)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same distance_symmetric)
open GaussianExponentialSmallPerturbation (smallSamples small_samples_at)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def rateNumerator (D N p q : PTm n) : PTm n := D*unit p*unit q+N*(unit p+unit q)
def rateDenominator (N p q : PTm n) : PTm n := N*unit p*unit q
def independentRate (F G : PR 2) (x y D N : PTm n) : Fm PTm n := .all (.all
  (distanceBounded (ap2 F (var 1) (Syn.shift (Syn.shift x))) (ap2 G (var 0) (Syn.shift (Syn.shift y)))
    (rateNumerator (Syn.shift (Syn.shift D)) (Syn.shift (Syn.shift N)) (var 1) (var 0))
    (rateDenominator (Syn.shift (Syn.shift N)) (var 1) (var 0))))
def inverseLaw (F G : PR 2) (x y : PTm n) : Fm PTm n :=
  crossEquivalent (GaussianNameArithmetic.multiplyF F G) GaussianNameRingLaws.oneF (GaussianNameArithmetic.multiplyData F G x y) x
def residualCost (F G : PR 2) (x y : PTm n) : PTm n := (GaussianNameArithmetic.multiplyModulus F G x y+one)+two
def auxiliaryCost (P Q I J : PR 2) (x y u v A : PTm n) : PTm n :=
  GaussianApproximateInverseDistance.errorCost A (residualCost P I x u) (residualCost Q J y v)
def input (P Q I J : PR 2) (x y u v A B D N : PTm n) : Fm PTm n :=
  le one B ⋏ (le one N ⋏ ((pointCN P x ⋏ pointCN Q y) ⋏ ((pointCN I u ⋏ pointCN J v) ⋏
    ((smallSamples I u A B ⋏ smallSamples J v A B) ⋏ ((inverseLaw P I x u ⋏ inverseLaw Q J y v) ⋏ independentRate P Q x y D N)))))

ipra_subst rateNumerator
ipra_subst rateDenominator
ipra_subst independentRate [Syn.subst_shift, Syn.shift_subst]
ipra_subst inverseLaw
ipra_subst residualCost
ipra_subst auxiliaryCost
ipra_subst input

theorem denominator_positive (N p q : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] le one (rateDenominator N p q) :=
  positive_product _ _ (positive_product _ _ hN (unit_positive p)) (unit_positive q)

theorem rate_at (F G : PR 2) (x y D N p q : PTm n) (h : Γ ⊢[PRAAx] independentRate F G x y D N) : Γ ⊢[PRAAx]
    distanceBounded (ap2 F p x) (ap2 G q y) (rateNumerator D N p q) (rateDenominator N p q) := by
  have pair : Γ ⊢[PRAAx] .all (distanceBounded (ap2 F (Syn.shift p) (Syn.shift x)) (ap2 G (var 0) (Syn.shift y))
      (rateNumerator (Syn.shift D) (Syn.shift N) (Syn.shift p) (var 0)) (rateDenominator (Syn.shift N) (Syn.shift p) (var 0))) := by
    simpa only [independentRate,Fm.subst_all,GaussianRationalMetric.subst_distanceBounded,subst_ap2,subst_rateNumerator,
      subst_rateDenominator,Syn.subst_var,Syn.up_zero,Syn.up_one,Syn.up_succ,Foundations.BoundedFormulas.subst_up_shift',
      Syn.inst_zero,Syn.inst_succ,Syn.subst_inst_shift,Syn.shift_var] using h.allE p
  simpa only [GaussianRationalMetric.subst_distanceBounded,subst_ap2,subst_rateNumerator,subst_rateDenominator,
    Syn.subst_var,Syn.inst_zero,Syn.inst_succ,Syn.subst_inst_shift] using pair.allE q

/-- An independent rate with a later second clock fits the diagonal budget
with two observation allowances at the first clock. -/
theorem diagonal_of_later_rate (x y A N p r : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hpr : Γ ⊢[PRAAx] le p r)
    (h : Γ ⊢[PRAAx] distanceBounded x y (rateNumerator A N p r) (rateDenominator N p r)) :
    Γ ⊢[PRAAx] distanceBounded x y (A*unit p+two*N) (N*unit p) := by
  let U := unit p
  let W := unit r
  have grow : Γ ⊢[PRAAx] le U W :=
    GaussianFactorBudget.power_monotone_length two p r (le_succ_self one) hpr
  apply distance_radius_mono _ _ _ _ _ _ (denominator_positive N p r hN)
    (positive_product _ _ hN (unit_positive p)) ?_ h
  change Γ ⊢[PRAAx] le ((A*U*W+N*(U+W))*(N*U)) ((A*U+two*N)*(N*U*W))
  ipra_le (Groth.ι (Q.mk Γ N))^2*(Groth.ι (Q.mk Γ U))*sl grow

theorem diagonal_rate (F G : PR 2) (x y D N t : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (h : Γ ⊢[PRAAx] independentRate F G x y D N) : Γ ⊢[PRAAx]
    distanceBounded (ap2 F t x) (ap2 G t y) (D*unit t+two*N) (N*unit t) :=
  diagonal_of_later_rate _ _ D N t t hN (le_refl t) (rate_at F G x y D N t t h)

theorem raw_inverse_residual (F G : PR 2) (x y t : PTm n) (hf : Γ ⊢[PRAAx] pointCN F x)
    (hg : Γ ⊢[PRAAx] pointCN G y) (he : Γ ⊢[PRAAx] inverseLaw F G x y) : Γ ⊢[PRAAx]
    distanceBounded (qmul (ap2 F t x) (ap2 G t y)) qone (residualCost F G x y) (unit t) := by
  have close := GaussianNameEquivalence.diagonal_at _ _ _ _ t (GaussianNameEquivalence.cross_to_diagonal _ _ _ _ he)
  exact distance_triangle_same _ _ _ _ _ _ (unit_positive t)
    (distance_symmetric _ _ _ _ (unit_positive t) (GaussianNameRingLaws.multiply_sample_error F G x y t hf hg))
    (distance_congr (.eqRefl _) (GaussianNameRingLaws.one_at t x) (.eqRefl _) (.eqRefl _) close)

theorem diagonal_inverse_slack (P Q I J : PR 2) (x y u v A B D N t : PTm n)
    (h : Γ ⊢[PRAAx] input P Q I J x y u v A B D N) : Γ ⊢[PRAAx]
    distanceBounded (ap2 I t u) (ap2 J t v)
      ((A*A*D)*unit t+auxiliaryCost P Q I J x y u v A*(B*B*N)) ((B*B*N)*unit t) := by
  have b := h.andE₁
  have n := h.andE₂.andE₁
  have f := h.andE₂.andE₂.andE₁
  have g := h.andE₂.andE₂.andE₂.andE₁
  have bounds := h.andE₂.andE₂.andE₂.andE₂.andE₁
  have laws := h.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁
  have rate := h.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂
  exact GaussianApproximateInverseDistance.finite_inverse_error _ _ _ _ A B D N (unit t) _ _ b n (unit_positive t)
    (small_samples_at I u A B t bounds.andE₁) (small_samples_at J v A B t bounds.andE₂) (diagonal_rate P Q x y D N t n rate)
    (raw_inverse_residual P I x u t f.andE₁ g.andE₁ laws.andE₁) (raw_inverse_residual Q J y v t f.andE₂ g.andE₂ laws.andE₂)

theorem independent_inverse_slack (P Q I J : PR 2) (x y u v A B D N p q t : PTm n)
    (h : Γ ⊢[PRAAx] input P Q I J x y u v A B D N) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (qsub (ap2 I p u) (ap2 J q v))
      (rateNumerator (A*A*D) (B*B*N) p q) (rateDenominator (B*B*N) p q)
      (auxiliaryCost P Q I J x y u v A+two) t := by
  let V := B*B*N
  let Z := rateDenominator V p q*unit t
  have n : Γ ⊢[PRAAx] le one V := positive_product _ _ (positive_product _ _ h.andE₁ h.andE₁) h.andE₂.andE₁
  have z : Γ ⊢[PRAAx] le one Z := positive_product _ _ (denominator_positive V p q n) (unit_positive t)
  have reg := h.andE₂.andE₂.andE₂.andE₁
  have left := distance_radius_mono _ _ _ _ ((unit p+unit t)*(V*unit q)) Z
    (positive_product _ _ (unit_positive p) (unit_positive t)) z
    (le_of_eq_add (d := zero) (by dsimp only [Z,V,rateDenominator]; ipra_ring))
    (GaussianNameEquivalence.point_at I u p t reg.andE₁)
  have middle := distance_radius_mono _ _ _ _
    (((A*A*D)*unit t+auxiliaryCost P Q I J x y u v A*V)*(unit p*unit q)) Z
    (positive_product _ _ n (unit_positive t)) z
    (le_of_eq_add (d := zero) (by dsimp only [Z,V,rateDenominator]; ipra_ring))
    (diagonal_inverse_slack P Q I J x y u v A B D N t h)
  have right := distance_radius_mono _ _ _ _ ((unit t+unit q)*(V*unit p)) Z
    (positive_product _ _ (unit_positive t) (unit_positive q)) z
    (le_of_eq_add (d := zero) (by dsimp only [Z,V,rateDenominator]; ipra_ring))
    (GaussianNameEquivalence.point_at J v t q reg.andE₂)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [V,rateNumerator,rateDenominator,unit]; ipra_ring)
    (.eqRefl _) (distance_triangle_same _ _ _ _ _ _ z (distance_triangle_same _ _ _ _ _ _ z left middle) right)

theorem inverse_error_at (P Q I J : PR 2) (x y u v A B D N p q : PTm n)
    (h : Γ ⊢[PRAAx] input P Q I J x y u v A B D N) : Γ ⊢[PRAAx]
    distanceBounded (ap2 I p u) (ap2 J q v) (rateNumerator (A*A*D) (B*B*N) p q) (rateDenominator (B*B*N) p q) := by
  have n : Γ ⊢[PRAAx] le one (B*B*N) := positive_product _ _ (positive_product _ _ h.andE₁ h.andE₁) h.andE₂.andE₁
  apply GaussianRationalSlackRemoval.slack_removal _ _ _ (auxiliaryCost P Q I J x y u v A+two) (denominator_positive _ p q n)
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] input P Q I J (Syn.shift x) (Syn.shift y) (Syn.shift u) (Syn.shift v)
      (Syn.shift A) (Syn.shift B) (Syn.shift D) (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using h.shift
  simpa only [GaussianRationalSlackRemoval.allSlack,GaussianRationalMetric.subst_qsub,subst_ap2,subst_rateNumerator,
    subst_rateDenominator,PTm.subst_mul,PTm.subst_add,subst_auxiliaryCost,Syn.shift,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    independent_inverse_slack P Q I J (Syn.shift x) (Syn.shift y) (Syn.shift u) (Syn.shift v) (Syn.shift A) (Syn.shift B)
      (Syn.shift D) (Syn.shift N) (Syn.shift p) (Syn.shift q) (var 0) hs

theorem inverse_rate (P Q I J : PR 2) (x y u v A B D N : PTm n)
    (h : Γ ⊢[PRAAx] input P Q I J x y u v A B D N) : Γ ⊢[PRAAx]
    independentRate I J u v (A*A*D) (B*B*N) := by
  refine .allI (.allI ?_)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] input P Q I J (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift y))
      (Syn.shift (Syn.shift u)) (Syn.shift (Syn.shift v)) (Syn.shift (Syn.shift A)) (Syn.shift (Syn.shift B))
      (Syn.shift (Syn.shift D)) (Syn.shift (Syn.shift N)) := by simpa [Fm.shift,Syn.shift] using h.shift.shift
  simpa only [independentRate,Syn.shift,PTm.subst_mul] using inverse_error_at P Q I J
    (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift y)) (Syn.shift (Syn.shift u)) (Syn.shift (Syn.shift v))
    (Syn.shift (Syn.shift A)) (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift D)) (Syn.shift (Syn.shift N)) (var 1) (var 0) hs

theorem original_exact_fractional_named_inverse_rate_closed (P Q I J : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input P Q I J (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      independentRate I J (var 2) (var 3) (var 4*var 4*var 6) (var 5*var 5*var 7)) :=
  closeUniv 8 (.impI (inverse_rate P Q I J _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedInverseRate
