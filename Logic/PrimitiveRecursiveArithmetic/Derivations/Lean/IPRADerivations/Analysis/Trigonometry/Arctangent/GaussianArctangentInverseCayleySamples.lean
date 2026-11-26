import IPRADerivations.Analysis.Trigonometry.Arctangent.GaussianArctangentNamedInverse
import IPRADerivations.Analysis.Trigonometry.Arctangent.GaussianArctangentCayleyProjections

/-!
# Literal Cayley samples of the normalized inverse parameter

The positive clipping preserves the represented fraction for each raw
inverse observation. Homogeneity of the Cayley code recovers the values
on the original common mesh, including its sine projection.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianArctangentInverseCayleySamples

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (scale eval_re_code eval_im_code)
open GaussianRootAlgebra (equal equal_of_values re_scale im_scale)
open GaussianRationalHorner (canonical_unique positive_product ofGaussian_canonical ofGaussian_represents
  represents_rescale represents_congr)
open GaussianArctangentCayleyValues (denominator denominator_positive numerator value)
open GaussianArctangentCayleyTrig (sinePoint)
open GaussianArctangentCayleyProjections (samplePrecision sineProjectionF sine_projection)
open GaussianArctangentInverseSampler (index mesh mesh_positive index_le)
open GaussianArctangentNamedCayley (data raw queryPrecision)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

theorem cayley_homogeneous (A B C D : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] A*D ≐ C*B) :
    Γ ⊢[PRAAx] value B A ≐ value D C := by
  let E := denominator B A
  let F := denominator D C
  let X := numerator B A
  let Y := numerator D C
  have hE := denominator_positive B A hB
  have hF := denominator_positive D C hD
  have eq := natEq h
  have same : Γ ⊢[PRAAx] equal (scale F X) (scale E Y) := by
    apply equal_of_values <;>
      simp only [E,F,X,Y,numerator,denominator,re_scale,im_scale,eval_re_code,eval_im_code,ZT.toZ_sub,ZT.toZ_ofNat] <;>
      ipra_simps
    · linear_combination (-2*(𝔞 A*𝔞 D+𝔞 C*𝔞 B))*eq
    · linear_combination (2*(𝔞 B*𝔞 D-𝔞 A*𝔞 C))*eq
  exact canonical_unique _ _ (scale E Y) (E*F) (ofGaussian_canonical X E hE) (ofGaussian_canonical Y F hF)
    (positive_product _ _ hE hF)
    (represents_congr (.eqRefl _) same (.eqRefl _) (represents_rescale _ _ E F (ofGaussian_represents X E hE)))
    (represents_congr (.eqRefl _) (GaussianRootAlgebra.equal_refl _) (mul_comm F E)
      (represents_rescale _ _ F E (ofGaussian_represents Y F hF)))

def inversePrecision (r : PTm n) : PTm n :=
  GaussianArctangentNamedInverse.precision (GaussianArctangentNamedExtension.clock r)

theorem partial_parameter (f : PR 2) (r x : PTm n) :
    Γ ⊢[PRAAx] GaussianArctangentNamedExtension.numerator (GaussianArctangentNamedInverse.nameF f) r
        (GaussianArctangentNamedInverse.data x)*mesh (inversePrecision r) ≐
      index f (inversePrecision r) x*
        GaussianArctangentNamedExtension.denominator (GaussianArctangentNamedInverse.nameF f) r
          (GaussianArctangentNamedInverse.data x) :=
  GaussianArctangentNamedExtension.parameter_specialization _ _ _ _ _ (index_le f (inversePrecision r) x)
    (GaussianArctangentNamedInverse.name_represents f (GaussianArctangentNamedExtension.clock r) x)

theorem raw_at (f : PR 2) (p x : PTm n) :
    Γ ⊢[PRAAx] raw (GaussianArctangentNamedInverse.nameF f) p (GaussianArctangentNamedInverse.data x) ≐
      value (mesh (inversePrecision (queryPrecision p))) (index f (inversePrecision (queryPrecision p)) x) :=
  cayley_homogeneous _ _ _ _
    (GaussianArctangentNamedExtension.denominator_positive _ _ _) (mesh_positive _) (partial_parameter f (queryPrecision p) x)

theorem sine_at (f : PR 2) (p x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sineProjectionF (GaussianArctangentNamedInverse.nameF f)) p
        (data (GaussianArctangentNamedInverse.data x)) ≐
      sinePoint (mesh (inversePrecision (samplePrecision p))) (index f (inversePrecision (samplePrecision p)) x) := by
  let F := GaussianArctangentNamedInverse.nameF f
  let X := GaussianArctangentNamedInverse.data x
  let r := samplePrecision p
  let A := GaussianArctangentNamedExtension.numerator F r X
  let B := GaussianArctangentNamedExtension.denominator F r X
  let M := mesh (inversePrecision r)
  let i := index f (inversePrecision r) x
  have hB := GaussianArctangentNamedExtension.denominator_positive (Γ := Γ) F r X
  have hM := mesh_positive (Γ := Γ) (inversePrecision r)
  have e := cayley_homogeneous A B i M hB hM (partial_parameter f r x)
  have s := (sine_projection B A hB).eqSymm.eqTrans
    ((RationalGaussianRealPart.embed_congr (congrSnd e)).eqTrans (sine_projection M i hM))
  exact (GaussianArctangentCayleyProjections.sine_sample_at F p X).eqTrans s

end LeanProofs.IPRA.Analysis.GaussianArctangentInverseCayleySamples
