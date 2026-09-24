import Surreal.Algebra.PredicateIdealReconstruction

/-!
# Ring formulas reconstructing an ideal's multiplier ring

The fraction-pair formulas in `odg:def:cor:internal`. The ideal is
defined by the quadratic test; all witnesses belong to the original
ring, even when the represented fraction belongs only to its field.
-/

namespace Surreal.IdealReconstruction

noncomputable section

variable {R F : Type*} [CommRing R] [Field F]

/-- The parameter-free quadratic ideal test. -/
def Inf (x : R) : Prop := ∃ y : R, x ^ 2 = 2 * y ^ 2

/-- The printed multiplier formula on a fraction pair. -/
def Mult (a b : R) : Prop :=
  b ≠ 0 ∧ ∀ x : R, Inf x → ∃ y : R, Inf y ∧ a * x = b * y

/-- The printed coefficient formula, with a separate zero case. -/
def Coeff (a b : R) : Prop := b ≠ 0 ∧ (a = 0 ∨ (a ≠ 0 ∧ Mult a b ∧ Mult b a))

/-- Membership of a fraction in the original ideal, with an original-ring representative. -/
def IdealFraction (a b : R) : Prop := b ≠ 0 ∧ ∃ y : R, Inf y ∧ a = b * y

/-- The reconstructed coefficient graph on two fraction pairs. -/
def Graph (a b c d : R) : Prop :=
  Mult a b ∧ Coeff c d ∧ IdealFraction (a * d - c * b) (b * d)

/-- The semantic multiplier condition in the ambient field. -/
def Preserves (I : F → Prop) (f : F) : Prop := ∀ x, I x → I (f * x)

/-- A quadratic ideal definition and representatives for all ideal elements suffice. -/
theorem mult_iff (ι : R →+* F) (hι : Function.Injective ι) (I : F → Prop)
    (htest : ∀ x : R, Inf x ↔ I (ι x))
    (hrep : ∀ x : F, I x → ∃ y : R, ι y = x) (a b : R) :
    Mult a b ↔ b ≠ 0 ∧ Preserves I (ι a / ι b) :=
  PredicateIdealReconstruction.mult_iff Inf ι hι I htest hrep a b

/-- Zero and invertible multipliers give exactly the printed Coeff formula. -/
theorem coeff_iff (ι : R →+* F) (hι : Function.Injective ι) (I C : F → Prop)
    (htest : ∀ x : R, Inf x ↔ I (ι x))
    (hrep : ∀ x : F, I x → ∃ y : R, ι y = x)
    (hC : ∀ f : F, C f ↔ f = 0 ∨ (f ≠ 0 ∧ Preserves I f ∧ Preserves I f⁻¹))
    (a b : R) : Coeff a b ↔ b ≠ 0 ∧ C (ι a / ι b) :=
  PredicateIdealReconstruction.coeff_iff Inf ι hι I C htest hrep hC a b

/-- Mult depends only on the represented fraction, stated entirely by cross multiplication. -/
theorem mult_congr {a b c d : R} [IsDomain R] (hb : b ≠ 0) (hd : d ≠ 0)
    (h : a * d = c * b) : Mult a b ↔ Mult c d :=
  PredicateIdealReconstruction.mult_congr Inf hb hd h

/-- Coeff is likewise invariant under nonzero-denominator changes of representative. -/
theorem coeff_congr {a b c d : R} [IsDomain R] (hb : b ≠ 0) (hd : d ≠ 0)
    (h : a * d = c * b) : Coeff a b ↔ Coeff c d :=
  PredicateIdealReconstruction.coeff_congr Inf hb hd h

/-- The ideal fraction formula denotes exactly the ambient ideal predicate. -/
theorem idealFraction_iff (ι : R →+* F) (hι : Function.Injective ι) (I : F → Prop)
    (htest : ∀ x : R, Inf x ↔ I (ι x))
    (hrep : ∀ x : F, I x → ∃ y : R, ι y = x) (a b : R) :
    IdealFraction a b ↔ b ≠ 0 ∧ I (ι a / ι b) :=
  PredicateIdealReconstruction.idealFraction_iff Inf ι hι I htest hrep a b

/-- Ideal membership of a fraction is independent of its representative. -/
theorem idealFraction_congr {a b c d : R} [IsDomain R] (hb : b ≠ 0) (hd : d ≠ 0)
    (h : a * d = c * b) : IdealFraction a b ↔ IdealFraction c d :=
  PredicateIdealReconstruction.idealFraction_congr Inf hb hd h

/-- The reconstructed graph descends in both fraction coordinates. -/
theorem graph_congr [IsDomain R] {a b c d a' b' c' d' : R}
    (hb : b ≠ 0) (hd : d ≠ 0) (hb' : b' ≠ 0) (hd' : d' ≠ 0)
    (ha : a * b' = a' * b) (hc : c * d' = c' * d) :
    Graph a b c d ↔ Graph a' b' c' d' :=
  PredicateIdealReconstruction.graph_congr Inf hb hd hb' hd' ha hc

/-- The full pair formula reconstructs the coefficient graph by subtraction into the ideal. -/
theorem graph_iff [IsDomain R] (ι : R →+* F) (hι : Function.Injective ι) (I C : F → Prop)
    (htest : ∀ x : R, Inf x ↔ I (ι x))
    (hrep : ∀ x : F, I x → ∃ y : R, ι y = x)
    (hC : ∀ f : F, C f ↔ f = 0 ∨ (f ≠ 0 ∧ Preserves I f ∧ Preserves I f⁻¹))
    (a b c d : R) : Graph a b c d ↔ b ≠ 0 ∧ d ≠ 0 ∧
      Preserves I (ι a / ι b) ∧ C (ι c / ι d) ∧ I (ι a / ι b - ι c / ι d) :=
  PredicateIdealReconstruction.graph_iff Inf ι hι I C htest hrep hC a b c d

end
end Surreal.IdealReconstruction
