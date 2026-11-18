import IPRADerivations.Geometry.SphericalCore

/-!
# Quadrantal spherical triangles (`spherical_trigonometry_ipra_2026-11-15`, (8.16)–(8.20))

Packet: `geometry/spherical_trigonometry_ipra_2026-11-15`, Subsection "Quadrantal spherical
triangles": "Assume instead that `c = π/2`. Applying the right-triangle rules to the polar
triangle gives" the ten rules (Q1)–(Q10); "the quotient forms are derived only under apartness."

Here they are derived directly from the finite core (4.16) of `Geometry/SphericalCore` with
`cos c = z = 0` and `sin c = s_c = 1` (`quadC`), as implications over integer values, in
division-free form. Where the packet cancels a guard, the equation is multiplied by it, and
the rules with a minus sign are written with both terms on the left.

* `quad_cos` : (Q8) `s_b c_A = x`; (Q9) `s_a c_B = y`; (Q10) `s_a s_b c_C + x y = 0`
  (`cos C = -cot a cot b` cleared of `s_a s_b`); (Q1) `s_a s_b c_C + s_a s_b c_A c_B = 0`
  (`cos C = -cos A cos B` times `s_a s_b`);
* `quad_sin` : (Q2) `s_b s_A = s_b (s_a s_C)`; (Q3) `s_a s_B = s_a (s_b s_C)`;
* `quad_tan` : (Q4) `s_A x = s_a s_B c_A` (`tan A = tan a sin B` cleared of `c_A x`);
  (Q5) `s_B y = s_b s_A c_B`; (Q6) `s_a (s_B c_C) + s_a (x s_C c_B) = 0`
  (`tan B = -cos a tan C` cleared of `c_B c_C`, times `s_a`);
  (Q7) `s_b (s_A c_C) + s_b (y s_C c_A) = 0`.

The polar-duality derivation of the packet is not used; the minus signs come out of the core
relations with `z = 0`.
-/

namespace LeanProofs.IPRA.Geometry.SphericalQuadrantal

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Geometry.SphericalCore
open Syn
open scoped Fm

/-! ## The ring-level certificates -/

section Ring

variable {R : Type*} [CommRing R] {x y z τ sa sb sc cA cB cC sA sB sC : R}

theorem q8_ring (h5 : sb * sc * cA = x - y * z) (hz : z = 0) (hs : sc = 1) : sb * cA = x := by
  linear_combination h5 - sb * cA * hs - y * hz

theorem q9_ring (h6 : sc * sa * cB = y - z * x) (hz : z = 0) (hs : sc = 1) : sa * cB = y := by
  linear_combination h6 - sa * cB * hs - x * hz

theorem q10_ring (h7 : sa * sb * cC = z - x * y) (hz : z = 0) : sa * sb * cC + x * y = 0 := by
  linear_combination h7 + hz

theorem q1_ring (h5 : sb * sc * cA = x - y * z) (h6 : sc * sa * cB = y - z * x)
    (h7 : sa * sb * cC = z - x * y) (hz : z = 0) (hs : sc = 1) :
    sa * sb * cC + sa * sb * (cA * cB) = 0 := by
  linear_combination (h7 + hz) + y * (h5 - sb * cA * hs - y * hz) +
    sb * cA * (h6 - sa * cB * hs - x * hz)

theorem q2_ring (h8 : sb * sc * sA = τ) (h10 : sa * sb * sC = τ) (hs : sc = 1) :
    sb * sA = sb * (sa * sC) := by
  linear_combination h8 - h10 - sb * sA * hs

theorem q3_ring (h9 : sc * sa * sB = τ) (h10 : sa * sb * sC = τ) (hs : sc = 1) :
    sa * sB = sa * (sb * sC) := by
  linear_combination h9 - h10 - sa * sB * hs

theorem q4_ring (h5 : sb * sc * cA = x - y * z) (h8 : sb * sc * sA = τ)
    (h9 : sc * sa * sB = τ) (hz : z = 0) (hs : sc = 1) : sA * x = sa * sB * cA := by
  linear_combination -sA * (h5 - sb * cA * hs - y * hz) +
    cA * (h8 - h9 - (sb * sA - sa * sB) * hs)

theorem q5_ring (h6 : sc * sa * cB = y - z * x) (h8 : sb * sc * sA = τ)
    (h9 : sc * sa * sB = τ) (hz : z = 0) (hs : sc = 1) : sB * y = sb * sA * cB := by
  linear_combination -sB * (h6 - sa * cB * hs - x * hz) -
    cB * (h8 - h9 - (sb * sA - sa * sB) * hs)

theorem q6_ring (h6 : sc * sa * cB = y - z * x) (h7 : sa * sb * cC = z - x * y)
    (h9 : sc * sa * sB = τ) (h10 : sa * sb * sC = τ) (hz : z = 0) (hs : sc = 1) :
    sa * (sB * cC) + sa * (x * sC * cB) = 0 := by
  linear_combination cC * (h9 - h10 - sa * sB * hs) + sC * (h7 + hz) +
    x * sC * (h6 - sa * cB * hs - x * hz)

theorem q7_ring (h5 : sb * sc * cA = x - y * z) (h7 : sa * sb * cC = z - x * y)
    (h8 : sb * sc * sA = τ) (h10 : sa * sb * sC = τ) (hz : z = 0) (hs : sc = 1) :
    sb * (sA * cC) + sb * (y * sC * cA) = 0 := by
  linear_combination cC * (h8 - h10 - sb * sA * hs) + sC * (h7 + hz) +
    y * sC * (h5 - sb * cA * hs - y * hz)

end Ring

/-! ## The rules in iPRA -/

/-- A quadrant side `c = π/2`: `z = cos c = 0`, `s_c = sin c = 1`. -/
def quadC : Fm PTm 26 := ZT.eq z (ZT.natLit 0) ⋏ ZT.eq sc (ZT.natLit 1)

theorem quad_toZ {Γ : List (Fm PTm 26)} (h : Γ ⊢[PRAAx] quadC) :
    ZT.toZ Γ z = 0 ∧ ZT.toZ Γ sc = 1 := by
  unfold quadC at h
  have hz := ZT.toZ_eq (Prf.andE₁ h)
  have hs := ZT.toZ_eq (Prf.andE₂ h)
  simp only [ZT.toZ_natLit, Nat.cast_zero, Nat.cast_one] at hz hs
  exact ⟨hz, hs⟩

/-- (Q8), (Q9), (Q10), (Q1). -/
def quadCosFormula : Fm PTm 26 :=
  core ⟶ quadC ⟶ ZT.eq (sb * cA) x ⋏ (ZT.eq (sa * cB) y ⋏
    (ZT.eq (sa * sb * cC + x * y) (ZT.natLit 0) ⋏
      ZT.eq (sa * sb * cC + sa * sb * (cA * cB)) (ZT.natLit 0)))

theorem quad_cos : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 26 quadCosFormula := by
  refine closeUniv 26 (.impI (.impI ?_))
  obtain ⟨_, _, _, _, h5, h6, h7, _, _, _⟩ := core_toZ (Γ := [quadC, core]) Prf.hyp1
  obtain ⟨hz, hs⟩ := quad_toZ (Γ := [quadC, core]) Prf.hyp0
  refine .andI (ZT.derive ?_) (.andI (ZT.derive ?_) (.andI (ZT.derive ?_) (ZT.derive ?_)))
  · simp only [ZT.toZ_mul]; exact q8_ring h5 hz hs
  · simp only [ZT.toZ_mul]; exact q9_ring h6 hz hs
  · simp only [ZT.toZ_mul, ZT.toZ_add, ZT.toZ_natLit, Nat.cast_zero]; exact q10_ring h7 hz
  · simp only [ZT.toZ_mul, ZT.toZ_add, ZT.toZ_natLit, Nat.cast_zero]
    exact q1_ring h5 h6 h7 hz hs

/-- (Q2), (Q3). -/
def quadSinFormula : Fm PTm 26 :=
  core ⟶ quadC ⟶ ZT.eq (sb * sA) (sb * (sa * sC)) ⋏ ZT.eq (sa * sB) (sa * (sb * sC))

theorem quad_sin : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 26 quadSinFormula := by
  refine closeUniv 26 (.impI (.impI ?_))
  obtain ⟨_, _, _, _, _, _, _, h8, h9, h10⟩ := core_toZ (Γ := [quadC, core]) Prf.hyp1
  obtain ⟨_, hs⟩ := quad_toZ (Γ := [quadC, core]) Prf.hyp0
  refine .andI (ZT.derive ?_) (ZT.derive ?_)
  · simp only [ZT.toZ_mul]; exact q2_ring h8 h10 hs
  · simp only [ZT.toZ_mul]; exact q3_ring h9 h10 hs

/-- (Q4), (Q5), (Q6), (Q7). -/
def quadTanFormula : Fm PTm 26 :=
  core ⟶ quadC ⟶ ZT.eq (sA * x) (sa * sB * cA) ⋏ (ZT.eq (sB * y) (sb * sA * cB) ⋏
    (ZT.eq (sa * (sB * cC) + sa * (x * sC * cB)) (ZT.natLit 0) ⋏
      ZT.eq (sb * (sA * cC) + sb * (y * sC * cA)) (ZT.natLit 0)))

theorem quad_tan : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 26 quadTanFormula := by
  refine closeUniv 26 (.impI (.impI ?_))
  obtain ⟨_, _, _, _, h5, h6, h7, h8, h9, h10⟩ := core_toZ (Γ := [quadC, core]) Prf.hyp1
  obtain ⟨hz, hs⟩ := quad_toZ (Γ := [quadC, core]) Prf.hyp0
  refine .andI (ZT.derive ?_) (.andI (ZT.derive ?_) (.andI (ZT.derive ?_) (ZT.derive ?_)))
  · simp only [ZT.toZ_mul]; exact q4_ring h5 h8 h9 hz hs
  · simp only [ZT.toZ_mul]; exact q5_ring h6 h8 h9 hz hs
  · simp only [ZT.toZ_mul, ZT.toZ_add, ZT.toZ_natLit, Nat.cast_zero]
    exact q6_ring h6 h7 h9 h10 hz hs
  · simp only [ZT.toZ_mul, ZT.toZ_add, ZT.toZ_natLit, Nat.cast_zero]
    exact q7_ring h5 h7 h8 h10 hz hs

end LeanProofs.IPRA.Geometry.SphericalQuadrantal
