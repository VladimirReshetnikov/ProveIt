import IPRADerivations.Core.LinearAlgebra

/-!
# The trisector identity of Morley's theorem (`morley_ipra_constructive`)

The packet's trigonometric core (`morley_ipra.tex`) is
`sin 3x = 4 sin x sin (x + 60°) sin (x + 120°)`. With `s = sin x`, `c = cos x` and
`ρ = √3`, this is, after clearing the factor `1/4`, the identity
`3s − 4s³ = s (ρc + s)(ρc − s)` modulo `s² + c² = 1` and `ρ² = 3`, derived here
as an iPRA implication over integer `s, c, ρ`.
-/

namespace LeanProofs.IPRA.Geometry.Morley

open_ipra

abbrev s : ZT 6 := .var2 0 1
abbrev c : ZT 6 := .var2 2 3
abbrev ρ : ZT 6 := .var2 4 5

def unit : Fm PTm 6 := ZT.eq (ZT.sq s + ZT.sq c) (ZT.natLit 1)
def root3 : Fm PTm 6 := ZT.eq (ZT.sq ρ) (ZT.natLit 3)

/-- If `s² + c² = 1` and `ρ² = 3` then `3s − 4s³ = s (ρc + s)(ρc − s)`. -/
def trisectorFormula : Fm PTm 6 :=
  unit ⟶ root3 ⟶
    ZT.eq (ZT.natLit 3 * s - ZT.natLit 4 * s * s * s) (s * (ρ * c + s) * (ρ * c - s))

theorem trisector_identity : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6 trisectorFormula := by
  refine closeUniv 6 (.impI (.impI (ZT.derive ?_)))
  have h₁ := ZT.toZ_mem (Γ := [root3, unit]) (u := ZT.sq s + ZT.sq c) (v := ZT.natLit 1)
    (by simp [unit])
  have h₂ := ZT.toZ_mem (Γ := [root3, unit]) (u := ZT.sq ρ) (v := ZT.natLit 3) (by simp [root3])
  ipra_simps
  linear_combination (-3 * (V [root3, unit] 0 - V [root3, unit] 1)) * h₁ -
    ((V [root3, unit] 0 - V [root3, unit] 1) * (V [root3, unit] 2 - V [root3, unit] 3) ^ 2) * h₂

end LeanProofs.IPRA.Geometry.Morley
