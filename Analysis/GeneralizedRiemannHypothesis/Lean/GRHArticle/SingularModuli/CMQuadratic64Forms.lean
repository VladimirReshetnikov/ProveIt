import GRHArticle.SingularModuli.CMHeckeDiagonal
import GRHArticle.SingularModuli.ClassPolynomialRootEnclosure

/-!
# Two analytic CM values of discriminant −64

The forms [1,0,16] and [4,4,5] each have a cyclic self-correspondence of
degree seventeen. Rational q-parameter enclosures separate their j-values.
-/

namespace GRHArticle.SingularModuli

def quadratic64Form : Fin 2 → FormCoefficients := ![⟨1,0,16⟩, ⟨4,4,5⟩]

theorem reducedForms_sixtyFour : reducedForms 64 = {quadratic64Form 0,quadratic64Form 1} := by
  decide +kernel

theorem quadratic64Form_mem (i : Fin 2) : quadratic64Form i ∈ reducedForms 64 := by
  fin_cases i <;> decide +kernel

noncomputable def quadratic64Value (i : Fin 2) : ℂ :=
  let f := quadratic64Form i
  modularInvariant (quadraticPoint 64 f.a f.b)

/-- The two determinant-one matrices realize shifts 1 and 5 at level 17. -/
theorem quadratic64_heckeDiagonal_zero (i : Fin 2) :
    let f := quadratic64Form i
    let z := quadraticPoint 64 f.a f.b
    (analyticPrimeHeckePolynomial 17 z).eval (modularInvariant z) = 0 := by
  fin_cases i
  · exact analyticPrimeHeckePolynomial_diagonal_of_shift (t := 1) (by decide)
      (modularInvariant_heckeShift_of_form 64 17 _ (by decide) 1 0 1 (-1) 1 (-1)
        (by decide) (by decide) (by decide) (by decide))
  · exact analyticPrimeHeckePolynomial_diagonal_of_shift (t := 5) (by decide)
      (modularInvariant_heckeShift_of_form 64 17 _ (by decide) 5 (-1) 0 (-4) (-1) (-1)
        (by decide) (by decide) (by decide) (by decide))

private def q64Box (i : Fin 2) : RationalComplexBox :=
  realAxisQBox 64 (quadratic64Form i).a (i==1)

private theorem q64_contains (i : Fin 2) : (q64Box i).Contains
    (Function.Periodic.qParam 1 (quadraticPoint 64 (quadratic64Form i).a (quadratic64Form i).b)) := by
  fin_cases i
  · exact realAxisQBox_contains 64 1 (by decide) false
  · exact realAxisQBox_contains 64 4 (by decide) true

/-- Rational rectangles isolating the two actual analytic values. -/
def quadratic64Box : Fin 2 → RationalComplexBox :=
  ![⟨⟨8222631632959/100,8222631632960/100⟩,⟨-1/100,1/100⟩⟩,
    ⟨⟨-8960/100,-8959/100⟩,⟨-1/100,1/100⟩⟩]

set_option maxRecDepth 150000 in
set_option maxHeartbeats 0 in
private theorem bounds64 (i : Fin 2) :
    let A := modularInvariantBox (q64Box i)
    let B := quadratic64Box i
    modularInvariantBoxDenominatorPositive (q64Box i) ∧ B.re.lo ≤ A.re.lo ∧
      A.re.hi ≤ B.re.hi ∧ B.im.lo ≤ A.im.lo ∧ A.im.hi ≤ B.im.hi := by
  fin_cases i <;> decide +kernel

theorem quadratic64Box_contains (i : Fin 2) : (quadratic64Box i).Contains (quadratic64Value i) := by
  obtain ⟨hpos,hl,hr,hd,hu⟩ := bounds64 i
  have h := modularInvariantBox_contains (quadratic64Form_mem i) (q64_contains i) hpos
  exact ⟨⟨(Rat.cast_le.mpr hl).trans h.1.1,h.1.2.trans (Rat.cast_le.mpr hr)⟩,
    ⟨(Rat.cast_le.mpr hd).trans h.2.1,h.2.2.trans (Rat.cast_le.mpr hu)⟩⟩

end GRHArticle.SingularModuli
