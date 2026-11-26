import IPRADerivations.Core.LinearAlgebra

/-!
# Formulas for roots (`ipra_polynomial_formulas_abel_ruffini`, `three_impossibilities_ipra`)

The packet's root formulas, with denominators cleared and the radicals and the
cube root of unity replaced by integer variables subject to their defining
relations. Each theorem is an implication in iPRA from the relations to the
factorisation.

* Quadratic (`chapters/03_linear_quadratic.tex`): if `s² = b² − 4ac` then
  `4a (aX² + bX + c) = (2aX + b − s)(2aX + b + s)`.
* Cardano (`chapters/04_cubic.tex`): if `u³ + v³ = −q`, `3uv = −p` and
  `ω² + ω + 1 = 0`, then `Y³ + pY + q = (Y − u − v)(Y − ωu − ω²v)(Y − ω²u − ωv)`.
* Ferrari (`chapters/05_quartic.tex`): if `s² = 2m − p`, `2st = −q` and
  `t² = m² − r`, then `Y⁴ + pY² + qY + r = (Y² − sY + m − t)(Y² + sY + m + t)`.
* Triple angle (`three_classical_impossibilities_ipra.tex`): if `x² + y² = 1` then
  `x³ − 3xy² = 4x³ − 3x`.
-/

namespace LeanProofs.IPRA.Algebra.PolynomialFormulas

open_ipra

section Quadratic

abbrev a : ZT 10 := .var2 0 1
abbrev b : ZT 10 := .var2 2 3
abbrev c : ZT 10 := .var2 4 5
abbrev s : ZT 10 := .var2 6 7
abbrev X : ZT 10 := .var2 8 9

def discr : Fm PTm 10 := ZT.eq (ZT.sq s) (ZT.sq b - ZT.natLit 4 * a * c)

def quadraticFormula : Fm PTm 10 :=
  discr ⟶ ZT.eq (ZT.natLit 4 * a * (a * ZT.sq X + b * X + c))
    ((ZT.natLit 2 * a * X + b - s) * (ZT.natLit 2 * a * X + b + s))

theorem quadratic : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10 quadraticFormula := by
  refine closeUniv 10 (.impI (ZT.derive ?_))
  have h := ZT.toZ_mem (Γ := [discr]) (u := ZT.sq s) (v := ZT.sq b - ZT.natLit 4 * a * c)
    (by simp [discr])
  ipra_simps
  linear_combination h

end Quadratic

section Cardano

abbrev Y : ZT 12 := .var2 0 1
abbrev u : ZT 12 := .var2 2 3
abbrev v : ZT 12 := .var2 4 5
abbrev w : ZT 12 := .var2 6 7
abbrev p : ZT 12 := .var2 8 9
abbrev q : ZT 12 := .var2 10 11

def hsum : Fm PTm 12 := ZT.eq (u * u * u + v * v * v) (-q)
def hprod : Fm PTm 12 := ZT.eq (ZT.natLit 3 * u * v) (-p)
def hunit : Fm PTm 12 := ZT.eq (w * w + w + ZT.natLit 1) (ZT.natLit 0)

def cardanoFormula : Fm PTm 12 :=
  hsum ⟶ hprod ⟶ hunit ⟶
    ZT.eq (Y * Y * Y + p * Y + q)
      ((Y - u - v) * (Y - w * u - w * w * v) * (Y - w * w * u - w * v))

theorem cardano : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 12 cardanoFormula := by
  refine closeUniv 12 (.impI (.impI (.impI (ZT.derive ?_))))
  have h₁ := ZT.toZ_mem (Γ := [hunit, hprod, hsum]) (u := u * u * u + v * v * v) (v := -q)
    (by simp [hsum])
  have h₂ := ZT.toZ_mem (Γ := [hunit, hprod, hsum]) (u := ZT.natLit 3 * u * v) (v := -p)
    (by simp [hprod])
  have h₃ := ZT.toZ_mem (Γ := [hunit, hprod, hsum]) (u := w * w + w + ZT.natLit 1)
    (v := ZT.natLit 0) (by simp [hunit])
  ipra_simps
  set Y' := V [hunit, hprod, hsum] 0 - V [hunit, hprod, hsum] 1
  set u' := V [hunit, hprod, hsum] 2 - V [hunit, hprod, hsum] 3
  set v' := V [hunit, hprod, hsum] 4 - V [hunit, hprod, hsum] 5
  set w' := V [hunit, hprod, hsum] 6 - V [hunit, hprod, hsum] 7
  linear_combination h₁ + Y' * h₂ +
    (Y' ^ 2 * u' + Y' ^ 2 * v' - 3 * Y' * u' * v' - u' ^ 3 - v' ^ 3
      + w' ^ 2 * (-Y' * u' * v' + u' ^ 2 * v' + u' * v' ^ 2)
      + w' * (-Y' * u' ^ 2 + Y' * u' * v' - Y' * v' ^ 2 + u' ^ 3 + v' ^ 3)) * h₃

end Cardano

section Ferrari

abbrev fY : ZT 14 := .var2 0 1
abbrev fs : ZT 14 := .var2 2 3
abbrev ft : ZT 14 := .var2 4 5
abbrev fm : ZT 14 := .var2 6 7
abbrev fp : ZT 14 := .var2 8 9
abbrev fq : ZT 14 := .var2 10 11
abbrev fr : ZT 14 := .var2 12 13

def f₁ : Fm PTm 14 := ZT.eq (ZT.sq fs) (ZT.natLit 2 * fm - fp)
def f₂ : Fm PTm 14 := ZT.eq (ZT.natLit 2 * fs * ft) (-fq)
def f₃ : Fm PTm 14 := ZT.eq (ZT.sq ft) (ZT.sq fm - fr)

def ferrariFormula : Fm PTm 14 :=
  f₁ ⟶ f₂ ⟶ f₃ ⟶
    ZT.eq (ZT.sq (ZT.sq fY) + fp * ZT.sq fY + fq * fY + fr)
      ((ZT.sq fY - fs * fY + fm - ft) * (ZT.sq fY + fs * fY + fm + ft))

theorem ferrari : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 14 ferrariFormula := by
  refine closeUniv 14 (.impI (.impI (.impI (ZT.derive ?_))))
  have h₁ := ZT.toZ_mem (Γ := [f₃, f₂, f₁]) (u := ZT.sq fs) (v := ZT.natLit 2 * fm - fp)
    (by simp [f₁])
  have h₂ := ZT.toZ_mem (Γ := [f₃, f₂, f₁]) (u := ZT.natLit 2 * fs * ft) (v := -fq)
    (by simp [f₂])
  have h₃ := ZT.toZ_mem (Γ := [f₃, f₂, f₁]) (u := ZT.sq ft) (v := ZT.sq fm - fr) (by simp [f₃])
  ipra_simps
  linear_combination
    (V [f₃, f₂, f₁] 0 - V [f₃, f₂, f₁] 1) ^ 2 * h₁ + (V [f₃, f₂, f₁] 0 - V [f₃, f₂, f₁] 1) * h₂ + h₃

end Ferrari

section TripleAngle

abbrev tx : ZT 4 := .var2 0 1
abbrev ty : ZT 4 := .var2 2 3

def onCircle : Fm PTm 4 := ZT.eq (ZT.sq tx + ZT.sq ty) (ZT.natLit 1)

/-- If `x² + y² = 1` then `Re (x + iy)³ = x³ − 3xy² = 4x³ − 3x`. -/
def tripleAngleFormula : Fm PTm 4 :=
  onCircle ⟶ ZT.eq (tx * tx * tx - ZT.natLit 3 * tx * ZT.sq ty)
    (ZT.natLit 4 * tx * tx * tx - ZT.natLit 3 * tx)

theorem triple_angle : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 tripleAngleFormula := by
  refine closeUniv 4 (.impI (ZT.derive ?_))
  have h := ZT.toZ_mem (Γ := [onCircle]) (u := ZT.sq tx + ZT.sq ty) (v := ZT.natLit 1)
    (by simp [onCircle])
  ipra_simps
  linear_combination (-3 * (V [onCircle] 0 - V [onCircle] 1)) * h

end TripleAngle

end LeanProofs.IPRA.Algebra.PolynomialFormulas
