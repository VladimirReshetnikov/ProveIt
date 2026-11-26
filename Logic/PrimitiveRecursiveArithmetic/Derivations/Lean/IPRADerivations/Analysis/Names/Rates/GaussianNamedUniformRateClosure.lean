import IPRADerivations.Analysis.Names.FiniteOperations.Products.GaussianNamedMultiplyRate
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateComposition
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateRadius

/-!
# Uniform rates for products and equality from vanishing dyadic rates

The bounds for one fixed pair of regular names also control products
with any varying approximating pair. A separately quantified vanishing
dyadic rate then gives exact agreement of two fixed names.
-/

set_option autoImplicit false
set_option maxHeartbeats 700000

namespace LeanProofs.IPRA.Analysis.GaussianNamedUniformRateClosure

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameArithmetic (multiplyF multiplyData)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open GaussianNamedMultiplyRate (sampleBound leadingNumerator leadingDenominator)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded distanceBounded qsub)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

private theorem derived_sample_bound (F G : PR 2) (x y M A N p : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hM : Γ ⊢[PRAAx] sampleBound G y M) (hr : Γ ⊢[PRAAx] independentRate F G x y A N) :
    Γ ⊢[PRAAx] bounded (ap2 F p x) (M+A+two) one := by
  have h := GaussianNamedInverseRate.diagonal_rate F G x y A N p hN hr
  have hg := GaussianNamedMultiplyRate.sample_bound_at G y M p hM
  have hp : Γ ⊢[PRAAx] le one (unit p) := unit_positive p
  have hd : Γ ⊢[PRAAx] le one (N*unit p) := positive_product _ _ hN hp
  have c := distance_radius_mono _ _ _ _ (A+two) one hd (le_refl one)
    (by ipra_le 𝔞 A*𝔞 (unit p)*sl hN+2*𝔞 N*sl hp) h
  have b := GaussianReconstructionRoots.norm_from_distance _ _ (A+two) one M one (le_refl one) (le_refl one) c hg
  exact GaussianRationalReciprocal.bound_congr (.eqRefl _) (by ipra_ring) (one_mul one) b

theorem sample_bound_of_rate (F G : PR 2) (x y M A N : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hM : Γ ⊢[PRAAx] sampleBound G y M) (hr : Γ ⊢[PRAAx] independentRate F G x y A N) :
    Γ ⊢[PRAAx] sampleBound F x (M+A+two) := by
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let sh (u : PTm n) := Syn.shift u
  have hn : Δ ⊢[PRAAx] le one (sh N) := by simpa [Δ,sh,Fm.shift,Syn.shift,one] using hN.shift
  have hm : Δ ⊢[PRAAx] sampleBound G (sh y) (sh M) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hM.shift
  have hh : Δ ⊢[PRAAx] independentRate F G (sh x) (sh y) (sh A) (sh N) :=
    by simpa [Δ,sh,Fm.shift,Syn.shift] using hr.shift
  simpa only [sampleBound,Δ,sh,Syn.shift,PTm.subst_add,two,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    derived_sample_bound F G (sh x) (sh y) (sh M) (sh A) (sh N) (var 0) hn hm hh

def productBudget (A C M R : PTm n) : PTm n := M*A+(R+A+two)*C

theorem same_denominator_product (F G H K : PR 2) (x y u v A C N M R : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hF : Γ ⊢[PRAAx] pointCN F x) (hG : Γ ⊢[PRAAx] pointCN G y)
    (hH : Γ ⊢[PRAAx] pointCN H u) (hK : Γ ⊢[PRAAx] pointCN K v)
    (hM : Γ ⊢[PRAAx] sampleBound G y M) (hR : Γ ⊢[PRAAx] sampleBound F x R)
    (h₁ : Γ ⊢[PRAAx] independentRate F H x u A N) (h₂ : Γ ⊢[PRAAx] independentRate G K y v C N) :
    Γ ⊢[PRAAx] independentRate (multiplyF F G) (multiplyF H K) (multiplyData F G x y) (multiplyData H K u v)
      (productBudget A C M R) N := by
  have hs := sample_bound_of_rate H F u x R A N hN hR (GaussianNamedRateComposition.symmetric F H x u A N hN h₁)
  have h := GaussianNamedMultiplyRate.independent_rate F G H K x y u v A N C N M (R+A+two) hN hN hF hG hH hK hM hs h₁ h₂
  exact GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ (positive_product _ _ hN hN) hN
    (le_of_eq_add (d := zero) (by dsimp only [leadingNumerator,leadingDenominator,productBudget]; ipra_ring)) h

def family (F G : PR 2) (x y C : PTm n) : Fm PTm n :=
  .all (independentRate F G (Syn.shift x) (Syn.shift y) (Syn.shift C) (unit (var 0)))

ipra_subst family [Syn.subst_shift, Syn.shift_subst]

theorem family_at (F G : PR 2) (x y C p : PTm n) (h : Γ ⊢[PRAAx] family F G x y C) : Γ ⊢[PRAAx]
    independentRate F G x y C (unit p) := by
  simpa only [family,GaussianNamedInverseRate.subst_independentRate,GaussianCoefficientNameBounds.subst_unit,
    Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE p

theorem cofinal_at (F G : PR 2) (x y C p q : PTm n) (h : Γ ⊢[PRAAx] family F G x y C) : Γ ⊢[PRAAx]
    distanceBounded (ap2 F p x) (ap2 G q y) (unit p+unit q) (unit p*unit q) := by
  let z := qsub (ap2 F p x) (ap2 G q y)
  let A := unit p+unit q
  let B := unit p*unit q
  let k := GaussianRationalSlackRemoval.precision z A B C
  apply GaussianRationalSlackRemoval.slack_removal_at z A B C (positive_product _ _ (unit_positive p) (unit_positive q))
  change Γ ⊢[PRAAx] distanceBounded (ap2 F p x) (ap2 G q y) (A*unit k+C*B) (B*unit k)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [rateNumerator,A,B]; ipra_ring)
    (by dsimp only [rateDenominator,B]; ipra_ring)
    (GaussianNamedInverseRate.rate_at F G x y C (unit k) p q (family_at F G x y C k h))

theorem equivalent (F G : PR 2) (x y C : PTm n) (h : Γ ⊢[PRAAx] family F G x y C) : Γ ⊢[PRAAx]
    crossEquivalent F G x y := by
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] family F G (sh x) (sh y) (sh C) :=
    by simpa [Fm.shift,Syn.shift,sh] using h.shift.shift
  exact .allI (.allI (cofinal_at F G (sh x) (sh y) (sh C) (var 1) (var 0) hs))

end LeanProofs.IPRA.Analysis.GaussianNamedUniformRateClosure
