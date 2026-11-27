import IPRADerivations.Core.LinearAlgebra
import IPRADerivations.Core.Header

/-!
# Algebraic identities behind Diophantine descents

* `flt_ipra` (`sections/quintic.tex`): with `F = t⁴ + 10t²s² + 5s⁴` and
  `G = t⁴ + 50t²s² + 125s⁴`, `(t + s√5)⁵ = tG + 5sF√5`; its norm form
  `(tG)² − 5(5sF)² = (t² − 5s²)⁵` is derived over the integers.
* `diophantine_geometry_ipra` (`sections/05_descent.tex`): the Pythagorean
  parametrisation `(2mn)² + (m² − n²)² = (m² + n²)²`.
* `faltings_ipra` (`sections/fermat_instance.tex`): the triangle
  `a = 2x²y², b = x⁴ − y⁴, c = x⁴ + y⁴` used for `x⁴ − y⁴ = z²` is Pythagorean,
  `a² + b² = c²`.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.Identities

open_ipra exports

/-- `u⁴`, `u⁵` as products. -/
def pow4 {m : ℕ} (u : ZT m) : ZT m := ZT.sq (ZT.sq u)
def pow5 {m : ℕ} (u : ZT m) : ZT m := pow4 u * u

@[simp] theorem toZ_pow4 {m : ℕ} {Γ : List (Fm PTm m)} (u : ZT m) :
    ZT.toZ Γ (pow4 u) = ZT.toZ Γ u ^ 4 := by simp [pow4]; ring
@[simp] theorem toZ_pow5 {m : ℕ} {Γ : List (Fm PTm m)} (u : ZT m) :
    ZT.toZ Γ (pow5 u) = ZT.toZ Γ u ^ 5 := by simp [pow5]; ring

section Quintic

abbrev t : ZT 4 := .var2 0 1
abbrev s : ZT 4 := .var2 2 3

def F : ZT 4 := pow4 t + ZT.natLit 10 * ZT.sq t * ZT.sq s + ZT.natLit 5 * pow4 s
def G : ZT 4 := pow4 t + ZT.natLit 50 * ZT.sq t * ZT.sq s + ZT.natLit 125 * pow4 s

/-- `(t + s√5)⁵ = tG + 5sF√5`, as the two integer coordinates in `ℤ[√5]`:
the rational part `t⁵ + 50t³s² + 125ts⁴ = tG` and the `√5` part
`5t⁴s + 50t²s³ + 25s⁵ = 5sF`. -/
def quinticPowerFormula : Fm PTm 4 :=
  Fm.and
    (ZT.eq (pow5 t + ZT.natLit 50 * ZT.sq t * t * ZT.sq s + ZT.natLit 125 * t * pow4 s) (t * G))
    (ZT.eq (ZT.natLit 5 * pow4 t * s + ZT.natLit 50 * ZT.sq t * ZT.sq s * s + ZT.natLit 25 * pow5 s)
      (ZT.natLit 5 * s * F))

theorem quintic_power : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 quinticPowerFormula := by
  refine closeUniv 4 (.andI ?_ ?_) <;> (apply ZT.derive; simp [F, G]; ring)

/-- `(tG)² − 5(5sF)² = (t² − 5s²)⁵`. -/
def quinticNormFormula : Fm PTm 4 :=
  ZT.eq (ZT.sq (t * G) - ZT.natLit 5 * ZT.sq (ZT.natLit 5 * s * F))
    (pow5 (ZT.sq t - ZT.natLit 5 * ZT.sq s))

theorem quintic_norm : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 quinticNormFormula :=
  closeUniv 4 (ZT.derive (by simp [F, G]; ring))

end Quintic

section Pythagorean

abbrev pm : ZT 4 := .var2 0 1
abbrev pn : ZT 4 := .var2 2 3

/-- `(2mn)² + (m² − n²)² = (m² + n²)²`. -/
def pythagoreanFormula : Fm PTm 4 :=
  ZT.eq (ZT.sq (ZT.natLit 2 * pm * pn) + ZT.sq (ZT.sq pm - ZT.sq pn)) (ZT.sq (ZT.sq pm + ZT.sq pn))

theorem pythagorean_parametrisation : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 pythagoreanFormula :=
  closeUniv 4 (by unfold pythagoreanFormula; ipra_ring)

/-- The triangle of `x⁴ − y⁴ = z²`: `(2x²y²)² + (x⁴ − y⁴)² = (x⁴ + y⁴)²`. -/
def fermatTriangleFormula : Fm PTm 4 :=
  ZT.eq (ZT.sq (ZT.natLit 2 * ZT.sq pm * ZT.sq pn) + ZT.sq (pow4 pm - pow4 pn))
    (ZT.sq (pow4 pm + pow4 pn))

theorem fermat_triangle : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 fermatTriangleFormula :=
  closeUniv 4 (ZT.derive (by simp; ring))

end Pythagorean

end LeanProofs.IPRA.DiophantineNumberTheory.Identities
