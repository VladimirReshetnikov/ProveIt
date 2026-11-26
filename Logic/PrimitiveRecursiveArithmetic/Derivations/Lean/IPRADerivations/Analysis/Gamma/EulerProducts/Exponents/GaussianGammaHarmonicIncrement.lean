import IPRADerivations.Analysis.Gamma.EulerProducts.CanonicalProducts.GaussianGammaCanonicalExponent
import IPRADerivations.Analysis.RationalArithmetic.Representations.RationalRepresentations

/-!
# The exact harmonic increment in the original Gamma exponent

The original `harmonic N` is normalized from S(N,N!)/N!. Its successor
is proved equal as a literal canonical rational code to H_N+1/(N+1).
The real-axis embedding carries the identity to the original
`harmonicPoint`, with the Gaussian rational 1/(N+1) in its actual native
representation. The proof uses the original harmonic sum recurrence,
exact factorial rebasing and quotient cancellation. All indices,
including N=0, are internal, and no value law for the output is assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaHarmonicIncrement

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicLogSquareSum (S_succ)
open LeanProofs.IPRA.AnalyticNumberTheory.MeshChange (S_denom)
open GammaEulerMesh (factorial_positive factorial_quotient)
open GaussianGammaCanonicalExponent (harmonic harmonicPoint harmonic_represents harmonic_canonical)
open GaussianRationalHorner (ofGaussian qadd positive_product)
open RationalGaussianEmbedding (embed)
open Products (fact)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

def reciprocal (N : PTm n) : PTm n :=
  RationalIntegerNormalization.normalize (ZT.ofNat one) (succ N)
def reciprocalPoint (N : PTm n) : PTm n :=
  ofGaussian ComplexLogarithmRemainder.oneCode (succ N)

ipra_subst reciprocal
ipra_subst reciprocalPoint

theorem reciprocal_represents (N : PTm n) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (reciprocal N) (ZT.ofNat one) (succ N) :=
  RationalIntegerNormalization.normalize_preserves_value _ _ (zero_lt_succ N)

theorem reciprocal_canonical (N : PTm n) : Γ ⊢[PRAAx] RationalNormalForm.wellFormed (reciprocal N) :=
  RationalNormalForm.normalize_well_formed _ _ (zero_lt_succ N)

theorem harmonic_increment (N : PTm n) : Γ ⊢[PRAAx]
    harmonic (succ N) ≐ RationalArithmetic.add (harmonic N) (reciprocal N) := by
  have sum := RationalRepresentations.represents_add _ _ _ _ _ _
    (harmonic_represents (Γ := Γ) N) (reciprocal_represents N)
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (harmonic_canonical _)
    (RationalArithmetic.add_guard _ _) (harmonic_represents _) sum
    (factorial_positive _) (RationalAlgebra.positive_product (factorial_positive N) (zero_lt_succ N))
  ipra_lc 𝔞 (fact N)*(𝔞 N+1)*natEq (S_succ (Γ := Γ) N (fact (succ N)))+
    (𝔞 N+1)*natEq (S_denom (Γ := Γ) (le_refl N) (le_succ_self N))+
    𝔞 (fact N)*natEq (factorial_quotient (Γ := Γ) (succ N) (succ N) (zero_lt_succ N) (le_refl _))

theorem embedded_reciprocal (N : PTm n) : Γ ⊢[PRAAx] embed (reciprocal N) ≐ reciprocalPoint N :=
  GaussianRationalHorner.canonical_unique _ _ _ _ (RationalGaussianEmbedding.embed_canonical _)
    (GaussianRationalHorner.ofGaussian_canonical _ _ (zero_lt_succ N)) (zero_lt_succ N)
    (RationalGaussianEmbedding.embed_from_representation _ _ _ (reciprocal_represents N))
    (GaussianRationalHorner.ofGaussian_represents _ _ (zero_lt_succ N))

theorem harmonic_point_increment (N : PTm n) : Γ ⊢[PRAAx]
    harmonicPoint (succ N) ≐ qadd (harmonicPoint N) (reciprocalPoint N) := by
  have e := Prf.eqCongr (Γ := Γ) (embed (var 0) : PTm 1)
    (σ := ![harmonic (succ N)]) (σ' := ![RationalArithmetic.add (harmonic N) (reciprocal N)])
    (fun i => by fin_cases i; exact harmonic_increment N)
  have e' : Γ ⊢[PRAAx] harmonicPoint (succ N) ≐
      embed (RationalArithmetic.add (harmonic N) (reciprocal N)) := by simpa [harmonicPoint] using e
  exact e'.eqTrans ((RationalGaussianEmbedding.embed_add _ _).eqTrans
    (GaussianRationalSyntheticDivision.qadd_congr (.eqRefl _) (embedded_reciprocal N)))

theorem actual_original_harmonic_increment_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (harmonic (succ (var 0)) ≐ RationalArithmetic.add (harmonic (var 0)) (reciprocal (var 0))) :=
  closeUniv 1 (harmonic_increment _)
theorem actual_gaussian_reciprocal_embedding_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (embed (reciprocal (var 0)) ≐ reciprocalPoint (var 0)) := closeUniv 1 (embedded_reciprocal _)
theorem actual_original_gaussian_harmonic_increment_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (harmonicPoint (succ (var 0)) ≐ qadd (harmonicPoint (var 0)) (reciprocalPoint (var 0))) :=
  closeUniv 1 (harmonic_point_increment _)

end LeanProofs.IPRA.Analysis.GaussianGammaHarmonicIncrement
