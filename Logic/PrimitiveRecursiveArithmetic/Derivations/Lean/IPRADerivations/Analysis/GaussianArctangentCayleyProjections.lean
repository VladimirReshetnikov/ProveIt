import IPRADerivations.Analysis.GaussianArctangentNamedCayley
import IPRADerivations.Analysis.GaussianArctangentCayleyTrig
import IPRADerivations.Analysis.GaussianImaginaryCoordinateName
import IPRADerivations.Analysis.GaussianGammaRealValues

/-!
# Literal trigonometric coordinates at the original Cayley clock

The cosine and sine reference names project the real and imaginary
coordinates of the actual Cayley name. Both readbacks retain the same
literal clipped numerator, denominator, and source observation precision.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianArctangentCayleyProjections

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (re im eval_re_code eval_im_code)
open GaussianArctangentCayleyStep (conjugateValue)
open GaussianArctangentCayleyTrig (sineCode cosineCode sinePoint cosinePoint)
open GaussianArctangentCayleyValues (value numerator denominator denominator_positive)
open GaussianArctangentNamedCayley (nameF data queryPrecision modulus)
open GaussianRationalHorner (canonical_unique represents_congr ofGaussian_canonical ofGaussian_represents)
open GaussianRootAlgebra (equal equal_of_values)
open RationalGaussianEmbedding (embed native embed_canonical embed_from_representation)
open RationalGaussianRealPart (embed_congr)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem sine_projection (B A : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] embed (sndT (value B A)) ≐ sinePoint B A := by
  let a := numerator B A
  let d := denominator B A
  have hd := denominator_positive B A hB
  have r := embed_from_representation (sndT (value B A)) (im a) d (ofGaussian_represents a d hd).andE₂
  have eq : Γ ⊢[PRAAx] equal (native (im a)) (sineCode B A) := by
    dsimp only [a]
    apply equal_of_values <;> simp only [native, numerator, sineCode, eval_re_code, eval_im_code]
  exact canonical_unique _ _ _ d (embed_canonical _) (ofGaussian_canonical _ _ hd) hd
    (represents_congr (.eqRefl _) eq (.eqRefl _) r) (ofGaussian_represents _ _ hd)

theorem cosine_projection (B A : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] embed (fstT (value B A)) ≐ cosinePoint B A := by
  let a := numerator B A
  let d := denominator B A
  have hd := denominator_positive B A hB
  have r := embed_from_representation (fstT (value B A)) (re a) d (ofGaussian_represents a d hd).andE₁
  have eq : Γ ⊢[PRAAx] equal (native (re a)) (cosineCode B A) := by
    dsimp only [a]
    apply equal_of_values <;> simp only [native, numerator, cosineCode, eval_re_code, eval_im_code]
  exact canonical_unique _ _ _ d (embed_canonical _) (ofGaussian_canonical _ _ hd) hd
    (represents_congr (.eqRefl _) eq (.eqRefl _) r) (ofGaussian_represents _ _ hd)

def samplePrecision (p : PTm n) : PTm n := queryPrecision (GaussianFastValueCut.exponent modulus p)

@[simp] theorem subst_samplePrecision {m : ℕ} (σ : Fin n → PTm m) (p : PTm n) :
    Syn.subst σ (samplePrecision p) = samplePrecision (Syn.subst σ p) := by simp [samplePrecision, modulus]

def sineProjectionF (f : PR 2) : PR 2 := GaussianImaginaryCoordinateName.nameF (nameF f)
def cosineProjectionF (f : PR 2) : PR 2 := GaussianGammaRealValues.axisF (nameF f)

theorem sine_sample_at (f : PR 2) (p x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sineProjectionF f) p (data x) ≐ sinePoint
      (GaussianArctangentNamedExtension.denominator f (samplePrecision p) x)
      (GaussianArctangentNamedExtension.numerator f (samplePrecision p) x) :=
  (GaussianImaginaryCoordinateName.sample_at (nameF f) p (data x)).eqTrans
    ((embed_congr (congrSnd (GaussianArctangentNamedCayley.sample_at f p x))).eqTrans
      (sine_projection _ _ (GaussianArctangentNamedExtension.denominator_positive _ _ _)))

theorem cosine_sample_at (f : PR 2) (p x : PTm n) :
    Γ ⊢[PRAAx] ap2 (cosineProjectionF f) p (data x) ≐ cosinePoint
      (GaussianArctangentNamedExtension.denominator f (samplePrecision p) x)
      (GaussianArctangentNamedExtension.numerator f (samplePrecision p) x) :=
  (GaussianGammaRealValues.axis_sample_at (nameF f) p (data x)).eqTrans
    ((embed_congr (congrFst (GaussianArctangentNamedCayley.sample_at f p x))).eqTrans
      (cosine_projection _ _ (GaussianArctangentNamedExtension.denominator_positive _ _ _)))

theorem conjugate_sample_at (f : PR 2) (p x : PTm n) :
    Γ ⊢[PRAAx] ap2 (GaussianNameConjugation.nameF (nameF f)) p (data x) ≐ conjugateValue
      (GaussianArctangentNamedExtension.denominator f (samplePrecision p) x)
      (GaussianArctangentNamedExtension.numerator f (samplePrecision p) x) := by
  let B := GaussianArctangentNamedExtension.denominator f (samplePrecision p) x
  let A := GaussianArctangentNamedExtension.numerator f (samplePrecision p) x
  have hd := denominator_positive B A (GaussianArctangentNamedExtension.denominator_positive (Γ := Γ) _ _ _)
  exact (GaussianNameConjugation.sample_at (nameF f) p (data x)).eqTrans
    ((GaussianRationalConjugation.point_congr (GaussianArctangentNamedCayley.sample_at f p x)).eqTrans
      (GaussianRationalConjugation.of_gaussian _ _ hd))

theorem actual_named_Cayley_trigonometric_samples_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((ap2 (sineProjectionF f) (var 0) (data (var 1)) ≐ sinePoint
        (GaussianArctangentNamedExtension.denominator f (samplePrecision (var 0)) (var 1))
        (GaussianArctangentNamedExtension.numerator f (samplePrecision (var 0)) (var 1))) ⋏
      (ap2 (cosineProjectionF f) (var 0) (data (var 1)) ≐ cosinePoint
        (GaussianArctangentNamedExtension.denominator f (samplePrecision (var 0)) (var 1))
        (GaussianArctangentNamedExtension.numerator f (samplePrecision (var 0)) (var 1)))) :=
  closeUniv 2 (.andI (sine_sample_at f _ _) (cosine_sample_at f _ _))

end LeanProofs.IPRA.Analysis.GaussianArctangentCayleyProjections
