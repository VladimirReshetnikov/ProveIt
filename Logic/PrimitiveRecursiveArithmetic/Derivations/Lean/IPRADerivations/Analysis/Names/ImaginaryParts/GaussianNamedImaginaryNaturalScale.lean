import IPRADerivations.Analysis.Trigonometry.GaussianNamedSineTaylor
import IPRADerivations.Analysis.Names.GaussianNameConjugation

/-!
# Imaginary rotation and natural scaling of Gaussian names

Both observation programs act on the same Gaussian rational at the
same scale clock. Commutativity and associativity identify the samples
exactly, including at scale zero.
-/

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace LeanProofs.IPRA.Analysis.GaussianNamedImaginaryNaturalScale

open_ipra
open GaussianArctangentCayleyValues (imaginaryPoint)
open GaussianNameConjugation (pointwiseEqual equal_samples_cross)
open GaussianNameEquivalence (crossEquivalent cross_symm)
open GaussianNamedNaturalScale (clock data exponential_input nameF radius sample_at subst_data)
open GaussianNamedSineFromExponential (sineF sineData sine_proper)
open GaussianNamedSineTaylor (imaginaryArgument imaginaryF imaginary_at imaginary_input)
open GaussianRadiusExponentialName (input)
open GaussianRationalHorner (qmul)
open GaussianRationalNaturalScale (naturalPoint natScale natScale_as_product natScale_congr)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianReciprocalHorner (qmul_associative)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem rational_commutes (m q : PTm n) :
    Γ ⊢[PRAAx] natScale m (imaginaryArgument q) ≐ imaginaryArgument (natScale m q) := by
  let M := naturalPoint m
  let I : PTm n := imaginaryPoint
  exact (natScale_as_product m (imaginaryArgument q)).eqTrans
    ((qmul_associative M I q).eqSymm.eqTrans
      ((qmul_congr (qmul_commutative M I) (.eqRefl q)).eqTrans
        ((qmul_associative I M q).eqTrans (qmul_congr (.eqRefl I) (natScale_as_product m q).eqSymm))))

theorem sample_commutes (f : PR 2) (p E m x : PTm n) :
    Γ ⊢[PRAAx] ap2 (nameF (imaginaryF f)) p (data E m x) ≐
      ap2 (imaginaryF (nameF f)) p (data E m x) := by
  let q := ap2 f (clock p E) x
  have left : Γ ⊢[PRAAx] ap2 (nameF (imaginaryF f)) p (data E m x) ≐ natScale m (imaginaryArgument q) :=
    (sample_at (imaginaryF f) p E m x).eqTrans
      (natScale_congr (.eqRefl m) (imaginary_at f (clock p E) x))
  have right : Γ ⊢[PRAAx] ap2 (imaginaryF (nameF f)) p (data E m x) ≐ imaginaryArgument (natScale m q) :=
    (imaginary_at (nameF f) p (data E m x)).eqTrans (qmul_congr (.eqRefl _) (sample_at f p E m x))
  exact left.eqTrans ((rational_commutes m q).eqTrans right.eqSymm)

theorem scaled_imaginary_input (f : PR 2) (E m R x : PTm n) (hf : Γ ⊢[PRAAx] input f R x)
    (hm : Γ ⊢[PRAAx] le m E) :
    Γ ⊢[PRAAx] input (nameF (imaginaryF f)) (radius E R) (data E m x) :=
  exponential_input (imaginaryF f) E m R x (imaginary_input f R x hf) hm

theorem imaginary_scaled_input (f : PR 2) (E m R x : PTm n) (hf : Γ ⊢[PRAAx] input f R x)
    (hm : Γ ⊢[PRAAx] le m E) :
    Γ ⊢[PRAAx] input (imaginaryF (nameF f)) (radius E R) (data E m x) :=
  imaginary_input (nameF f) (radius E R) (data E m x) (exponential_input f E m R x hf hm)

theorem scale_imaginary_cross (f : PR 2) (E m R x : PTm n) (hf : Γ ⊢[PRAAx] input f R x)
    (hm : Γ ⊢[PRAAx] le m E) :
    Γ ⊢[PRAAx] crossEquivalent (nameF (imaginaryF f)) (imaginaryF (nameF f)) (data E m x) (data E m x) := by
  apply equal_samples_cross _ _ _ _ (scaled_imaginary_input f E m R x hf hm).andE₁
    (imaginary_scaled_input f E m R x hf hm).andE₁
  refine .allI ?_
  simpa only [pointwiseEqual,Syn.shift,subst_data] using
    sample_commutes (Γ := Γ.map Fm.shift) f (var 0) (Syn.shift E) (Syn.shift m) (Syn.shift x)

theorem sine_cross (f : PR 2) (E m R x : PTm n) (hf : Γ ⊢[PRAAx] input f R x)
    (hm : Γ ⊢[PRAAx] le m E) :
    Γ ⊢[PRAAx] crossEquivalent (sineF (imaginaryF (nameF f))) (sineF (nameF (imaginaryF f)))
      (sineData (imaginaryF (nameF f)) (radius E R) (data E m x))
      (sineData (nameF (imaginaryF f)) (radius E R) (data E m x)) :=
  sine_proper _ _ _ _ _ _ (imaginary_scaled_input f E m R x hf hm) (scaled_imaginary_input f E m R x hf hm)
    (cross_symm _ _ _ _ (scale_imaginary_cross f E m R x hf hm))

theorem actual_imaginary_natural_scaling_sine_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (input f (var 2) (var 3) ⟶ le (var 1) (var 0) ⟶
      crossEquivalent (sineF (imaginaryF (nameF f))) (sineF (nameF (imaginaryF f)))
        (sineData (imaginaryF (nameF f)) (radius (var 0) (var 2)) (data (var 0) (var 1) (var 3)))
        (sineData (nameF (imaginaryF f)) (radius (var 0) (var 2)) (data (var 0) (var 1) (var 3)))) :=
  closeUniv 4 (.impI (.impI (sine_cross f _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianNamedImaginaryNaturalScale
