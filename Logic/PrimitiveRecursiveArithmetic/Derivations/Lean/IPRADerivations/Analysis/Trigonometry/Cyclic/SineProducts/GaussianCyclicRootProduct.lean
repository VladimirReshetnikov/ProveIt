import IPRADerivations.Analysis.Trigonometry.Cyclic.ExponentialRoots.GaussianCyclicExponentialSeparation
import IPRADerivations.Analysis.Trigonometry.Cyclic.ExponentialRoots.GaussianCyclicGeometricPolynomial
import IPRADerivations.Analysis.RationalArithmetic.Representations.GaussianRationalSeparatedReconstruction

/-!
# Reconstruction of the nontrivial cyclic root product

The root list consists of the actual original exponential samples at
indices 1 through `N`, with modulus `N+1`. Their separated geometric
polynomial residuals yield a uniform error for the product at one.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianCyclicRootProduct

open_ipra
open GaussianCyclicExponentialRoots (sample sample_zero sample_bound sampleRadius source power_residual powerBudget)
open GaussianCyclicExponentialSeparation (clock fine clock_fine denominator denominator_positive pair_margin_at)
open GaussianCyclicGeometricPolynomial (coefficients coefficients_length coefficients_monic evaluation_at_one
  geometric_factorization)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameReciprocal (lower_norm_positive)
open GaussianRationalHorner (horner_canonical positive_product qmul evaluate represents_congr)
open GaussianRationalL1 (rawDen rawGaussian raw_den_positive raw_represents)
open GaussianRationalLowerBounds (lower lower_to_cleared lower_from_representation name_lower)
open GaussianRationalMetric (bounded distanceBounded qsub qnegative_represents)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianRationalReciprocal (qone qone_bounded bounded_product bounded_difference bound_congr
  reciprocal reciprocal_identity)
open GaussianRationalDistanceOrder (distance_congr reversed_difference)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalSyntheticDivision (qsub_congr qmul_congr)
open GaussianReciprocalHorner (qmul_one_right qmul_associative)
open GaussianRationalMonicReduction (evaluate_congr)
open GaussianRationalReconstruction (product)
open GaussianRationalSeparatedDeflation (separation separationFrom laterResiduals)
open GaussianRationalSeparatedReconstruction (differencesBounded errorNumerator reconstruction_distance)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def data (p N x : PTm n) : PTm n := pairT p (pairT N x)
def body : PTm 2 := sample (fstT (var 1)) (succ (var 0)) (succ (fstT (sndT (var 1)))) (sndT (sndT (var 1)))
def roots (p N x : PTm n) : PTm n := sequence body N (data p N x)

ipra_subst data

ipra_subst roots

theorem roots_length (p N x : PTm n) : Γ ⊢[PRAAx] length (roots p N x) ≐ N := sequence_length _ _ _

theorem body_at (p N x j : PTm n) :
    Γ ⊢[PRAAx] LeanProofs.IPRA.inst2 body j (data p N x) ≐ sample p (succ j) (succ N) x := by
  simpa [body,LeanProofs.IPRA.inst2] using Prf.eqCongr (Γ := Γ)
    (sample (var 0) (succ (var 1)) (succ (var 2)) (var 3) : PTm 4)
    (σ := ![fstT (data p N x),j,fstT (sndT (data p N x)),sndT (sndT (data p N x))])
    (σ' := ![p,j,N,x]) (fun k => by
      fin_cases k
      · exact fst_pair _ _
      · exact .eqRefl _
      · exact (snd_pair _ _).fstE
      · exact (snd_pair _ _).sndE)

theorem roots_at (p N x j : PTm n) (hj : Γ ⊢[PRAAx] lt j N) :
    Γ ⊢[PRAAx] entry (roots p N x) j ≐ sample p (succ j) (succ N) x :=
  (sequence_decode body hj).eqTrans (body_at p N x j)

private theorem reverse_lower (a b D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] lower (qsub a b) one D) :
    Γ ⊢[PRAAx] lower (qsub b a) one D := by
  let q := qsub a b
  let z := rawGaussian q
  let E := rawDen q
  have hE := raw_den_positive (Γ := Γ) q
  have hb := lower_to_cleared _ _ _ _ _ hE hD (raw_represents q) h
  exact lower_from_representation _ _ E _ _ hE hD
    (represents_congr (reversed_difference a b) (GaussianRootAlgebra.equal_refl _)
      (.eqRefl _) (qnegative_represents _ _ _ (raw_represents q)))
    (le_congr (.eqRefl _) (congrMul (.eqRefl _) (ComplexLogarithmRemainder.normSq_neg z).eqSymm) hb)

private theorem sample_one_lower (p r m x : PTm n) (hr : Γ ⊢[PRAAx] lt zero r) (hm : Γ ⊢[PRAAx] lt r m)
    (hf : Γ ⊢[PRAAx] fine m p) :
    Γ ⊢[PRAAx] lower (qsub (sample p r m x) qone) one (denominator m) := by
  have hpos : Γ ⊢[PRAAx] le one m := le_trans hr (le_of_lt hm)
  have margin := reverse_lower _ _ _ (denominator_positive m hpos) (pair_margin_at p zero r m x hr hm hf)
  exact GaussianRationalLowerBounds.lower_congr (qsub_congr (.eqRefl _) (sample_zero p m x hpos))
    (.eqRefl _) (.eqRefl _) margin

theorem geometric_residual (p r m x : PTm n) (hr : Γ ⊢[PRAAx] lt zero r) (hm : Γ ⊢[PRAAx] lt r m)
    (hf : Γ ⊢[PRAAx] fine m p) :
    Γ ⊢[PRAAx] bounded (evaluate (coefficients m) (sample p r m x)) (denominator m*powerBudget m) (unit p) := by
  let z := sample p r m x
  let d := qsub z qone
  let E := denominator m
  let a := evaluate (coefficients m) z
  have hE : Γ ⊢[PRAAx] le one E := denominator_positive m (le_trans hr (le_of_lt hm))
  have hlow := name_lower d one E (le_refl _) hE (sample_one_lower p r m x hr hm hf)
  have ib := GaussianNameReciprocal.inverse_bound d E hE hlow
  have hinv : Γ ⊢[PRAAx] qmul (reciprocal d) d ≐ qone :=
    (qmul_commutative _ _).eqTrans (reciprocal_identity d (lower_norm_positive d E hE hlow))
  have residual : Γ ⊢[PRAAx] bounded (qmul d a) (powerBudget m) (unit p) :=
    bound_congr (geometric_factorization m z).eqSymm (.eqRefl _) (.eqRefl _)
      (power_residual p r m x (.andI (le_trans hr (le_of_lt hm)) (le_of_lt hm)))
  have reassemble : Γ ⊢[PRAAx] qmul (reciprocal d) (qmul d a) ≐ a :=
    (qmul_associative _ _ _).eqSymm.eqTrans ((qmul_congr hinv (.eqRefl _)).eqTrans
      ((qmul_commutative _ _).eqTrans (qmul_one_right _ (horner_canonical _ _ _))))
  exact bound_congr reassemble (.eqRefl _) (one_mul _)
    (bounded_product _ _ _ _ _ _ (le_refl one) (unit_positive p) ib residual)

private theorem succ_lt_congr (i j : PTm n) (h : Γ ⊢[PRAAx] lt i j) :
    Γ ⊢[PRAAx] lt (succ i) (succ j) :=
  le_congr (succ_eq_add_one _).eqSymm (succ_eq_add_one _).eqSymm (add_le_add_right one h)

private theorem shifted_fine (p N : PTm n) (hf : Γ ⊢[PRAAx] fine (succ N) p) :
    Γ.map Fm.shift ⊢[PRAAx] fine (succ (Syn.shift N)) (Syn.shift p) := by
  simpa [Fm.shift,Syn.shift,fine] using hf.shift

private theorem separation_from (p N x i : PTm n) (hf : Γ ⊢[PRAAx] fine (succ N) p) :
    Γ ⊢[PRAAx] separationFrom (roots p N x) (denominator (succ N)) i := by
  refine .allI (.impI (.impI ?_))
  let P := Syn.shift p
  let J := Syn.shift N
  let X := Syn.shift x
  let I := Syn.shift i
  let r : PTm (n+1) := var 0
  let Δ := lt I r :: lt r (length (roots P J X)) :: Γ.map Fm.shift
  have hr : Δ ⊢[PRAAx] lt r J := lt_congr (.eqRefl _) (roots_length P J X) Prf.hyp1
  have hij : Δ ⊢[PRAAx] lt I r := Prf.hyp0
  have hi := lt_of_lt_of_le hij (le_of_lt hr)
  have hsep := pair_margin_at P (succ I) (succ r) (succ J) X
    (succ_lt_congr I r hij) (succ_lt_congr r J hr) (shifted_fine p N hf).wk.wk
  have h := reverse_lower _ _ _ (denominator_positive (succ J) (zero_lt_succ J)) hsep
  have cast := qsub_congr (roots_at P J X r hr).eqSymm (roots_at P J X I hi).eqSymm
  have h' := name_lower _ one _ (le_refl one) (denominator_positive (succ J) (zero_lt_succ J)) h
  simpa [separationFrom,Δ,Syn.shift,P,J,X,I,r] using GaussianNameReciprocal.lower_congr cast (.eqRefl _) h'

theorem separated_roots (p N x : PTm n) (hf : Γ ⊢[PRAAx] fine (succ N) p) :
    Γ ⊢[PRAAx] separation (roots p N x) (denominator (succ N)) := by
  refine .allI ?_
  simpa only [separation,subst_roots,GaussianCyclicExponentialSeparation.subst_denominator,
    ConciseIPRA.PTm.subst_succ,Syn.shift] using
    separation_from (Syn.shift p) (Syn.shift N) (Syn.shift x) (var 0) (shifted_fine p N hf)

def residualBudget (N : PTm n) : PTm n := denominator (succ N)*powerBudget (succ N)

ipra_subst residualBudget

theorem root_residuals (p N x : PTm n) (hf : Γ ⊢[PRAAx] fine (succ N) p) :
    Γ ⊢[PRAAx] laterResiduals (coefficients (succ N)) (roots p N x) zero (residualBudget N) (unit p) := by
  refine .allI (.impI (.impI ?_))
  let P := Syn.shift p
  let J := Syn.shift N
  let X := Syn.shift x
  let j : PTm (n+1) := var 0
  let Δ := le zero j :: lt j (length (roots P J X)) :: Γ.map Fm.shift
  have hj : Δ ⊢[PRAAx] lt j J := lt_congr (.eqRefl _) (roots_length P J X) Prf.hyp1
  have rate := geometric_residual P (succ j) (succ J) X (zero_lt_succ j)
    (succ_lt_congr j J hj) (shifted_fine p N hf).wk.wk
  have cast := evaluate_congr (.eqRefl (coefficients (succ J))) (roots_at P J X j hj).eqSymm
  simpa [laterResiduals,residualBudget,Δ,Syn.shift,P,J,X,j] using bound_congr cast (.eqRefl _) (.eqRefl _) rate

theorem root_differences (p N x : PTm n) :
    Γ ⊢[PRAAx] differencesBounded (roots p N x) qone (one+sampleRadius) := by
  refine .allI (.impI ?_)
  let P := Syn.shift p
  let J := Syn.shift N
  let X := Syn.shift x
  let j : PTm (n+1) := var 0
  let Δ := lt j (length (roots P J X)) :: Γ.map Fm.shift
  have hj : Δ ⊢[PRAAx] lt j J := lt_congr (.eqRefl _) (roots_length P J X) Prf.hyp0
  have rad := sample_bound P (succ j) (succ J) X (.andI (zero_lt_succ J) (le_of_lt (succ_lt_congr j J hj)))
  have hr := bound_congr (roots_at P J X j hj).eqSymm (.eqRefl _) (.eqRefl _) rad
  have h : Δ ⊢[PRAAx] bounded (qsub qone (entry (roots P J X) j)) (one+sampleRadius) one :=
    bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring)
      (bounded_difference _ _ _ _ _ _ (le_refl one) (le_refl one) qone_bounded hr)
  simpa [differencesBounded,Δ,Syn.shift,P,J,X,j] using h

def budget (N : PTm n) : PTm n := errorNumerator (residualBudget N) (denominator (succ N)) N (one+sampleRadius) N

ipra_subst budget

theorem reconstruction_at (p N x : PTm n) (hf : Γ ⊢[PRAAx] fine (succ N) p) :
    Γ ⊢[PRAAx] distanceBounded (naturalPoint (succ N)) (product (roots p N x) N qone)
      (budget N) (unit p) :=
  distance_congr (evaluation_at_one (succ N)) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (reconstruction_distance _ _ _ _ _ _ _ _
      (coefficients_length (succ N)) (roots_length p N x) (coefficients_monic _ (zero_lt_succ N))
      (unit_positive p) (denominator_positive _ (zero_lt_succ N))
      (root_residuals p N x hf) (separated_roots p N x hf) (root_differences p N x))

theorem reconstruction (p N x : PTm n) :
    Γ ⊢[PRAAx] distanceBounded (naturalPoint (succ N)) (product (roots (clock (succ N) p) N x) N qone)
      (budget N) (unit (clock (succ N) p)) :=
  reconstruction_at _ N x (clock_fine _ _)

theorem actual_cyclic_root_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (distanceBounded (naturalPoint (succ (var 1)))
      (product (roots (clock (succ (var 1)) (var 2)) (var 1) (var 0)) (var 1) qone)
      (budget (var 1)) (unit (clock (succ (var 1)) (var 2)))) :=
  closeUniv 3 (reconstruction _ _ _)

end LeanProofs.IPRA.Analysis.GaussianCyclicRootProduct
