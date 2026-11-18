import IPRADerivations.Geometry.SphericalCore

/-!
# Napier's rules for right spherical triangles (`spherical_trigonometry_ipra_2026-11-15`, (8.11)–(8.15))

Packet: `geometry/spherical_trigonometry_ipra_2026-11-15`, Subsection "Right spherical
triangles": "Assume `C = π/2`. Then `sin C = 1` and `cos C = 0`. The core laws reduce to
Napier's ten rules" (R1)–(R10); "the tangent and cotangent equations are guarded by the
corresponding cosine or sine apartness witnesses."

`Geometry/SphericalCore.right_rules` has (R1) `cos c = cos a cos b`, (R2) `sin a = sin A sin c`
and `s_c c_A = x s_b` (each times its guard). Here the remaining rules are derived from the
finite core (4.16) with `c_C = 0`, `s_C = 1` (`rightC`), as implications over integer values in
division-free form; a guard that the packet cancels is kept as a factor:

* `napier_sin` : (R3) `s_a (s_c s_B) = s_a s_b`;
* `napier_tan` : (R4) `tan a = tan A sin b` as `(s_b s_c)(s_a c_A) = (s_b s_c)(x s_A s_b)`;
  (R5) `(s_a s_c)(s_b c_B) = (s_a s_c)(y s_B s_a)`; (R6) `tan b = cos A tan c` as
  `s_b (s_b z) = s_b (y (c_A s_c))`; (R7) `s_a (s_a z) = s_a (x (c_B s_c))`;
* `napier_cos` : (R8) `cos A = sin B cos a` as `s_a s_b s_c c_A = s_a s_b s_c (s_B x)`;
  (R9) `s_a s_b s_c c_B = s_a s_b s_c (s_A y)`; (R10) `cos c = cot A cot B` as
  `(s_b s_c)(s_c s_a)(z (s_A s_B)) = (s_b s_c)(s_c s_a)(c_A c_B)`.

With `right_rules` these are all ten rules. Napier's circle is the mnemonic for them and adds
no statement.
-/

namespace LeanProofs.IPRA.Geometry.SphericalNapier

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Geometry.SphericalCore
open Syn
open scoped Fm

/-! ## The ring-level certificates -/

section Ring

variable {R : Type*} [CommRing R] {x y z τ sa sb sc cA cB cC sA sB sC : R}

theorem r3_ring (h9 : sc * sa * sB = τ) (h10 : sa * sb * sC = τ) (hS : sC = 1) :
    sa * (sc * sB) = sa * sb := by
  linear_combination h9 - h10 + sa * sb * hS

theorem r4_ring (h2 : sb ^ 2 + y ^ 2 = 1) (h5 : sb * sc * cA = x - y * z)
    (h7 : sa * sb * cC = z - x * y) (h8 : sb * sc * sA = τ) (h10 : sa * sb * sC = τ)
    (hC : cC = 0) (hS : sC = 1) :
    (sb * sc) * (sa * cA) = (sb * sc) * (x * sA * sb) := by
  linear_combination sa * h5 - x * sb * h8 - sa * x * h2 - sa * y * (sa * sb * hC - h7) -
    x * sb * (sa * sb * hS - h10)

theorem r5_ring (h1 : sa ^ 2 + x ^ 2 = 1) (h6 : sc * sa * cB = y - z * x)
    (h7 : sa * sb * cC = z - x * y) (h9 : sc * sa * sB = τ) (h10 : sa * sb * sC = τ)
    (hC : cC = 0) (hS : sC = 1) :
    (sa * sc) * (sb * cB) = (sa * sc) * (y * sB * sa) := by
  linear_combination sb * h6 - y * sa * h9 - sb * y * h1 - sb * x * (sa * sb * hC - h7) -
    y * sa * (sa * sb * hS - h10)

theorem r6_ring (h2 : sb ^ 2 + y ^ 2 = 1) (h5 : sb * sc * cA = x - y * z)
    (h7 : sa * sb * cC = z - x * y) (hC : cC = 0) :
    sb * (sb * z) = sb * (y * (cA * sc)) := by
  linear_combination z * h2 + (sa * sb * hC - h7) - y * h5

theorem r7_ring (h1 : sa ^ 2 + x ^ 2 = 1) (h6 : sc * sa * cB = y - z * x)
    (h7 : sa * sb * cC = z - x * y) (hC : cC = 0) :
    sa * (sa * z) = sa * (x * (cB * sc)) := by
  linear_combination z * h1 + (sa * sb * hC - h7) - x * h6

theorem r8_ring (h2 : sb ^ 2 + y ^ 2 = 1) (h5 : sb * sc * cA = x - y * z)
    (h7 : sa * sb * cC = z - x * y) (h9 : sc * sa * sB = τ) (h10 : sa * sb * sC = τ)
    (hC : cC = 0) (hS : sC = 1) :
    sa * sb * sc * cA = sa * sb * sc * (sB * x) := by
  linear_combination sa * h5 - x * sb * h9 - sa * x * h2 - sa * y * (sa * sb * hC - h7) -
    x * sb * (sa * sb * hS - h10)

theorem r9_ring (h1 : sa ^ 2 + x ^ 2 = 1) (h6 : sc * sa * cB = y - z * x)
    (h7 : sa * sb * cC = z - x * y) (h8 : sb * sc * sA = τ) (h10 : sa * sb * sC = τ)
    (hC : cC = 0) (hS : sC = 1) :
    sa * sb * sc * cB = sa * sb * sc * (sA * y) := by
  linear_combination sb * h6 - y * sa * h8 - sb * y * h1 - sb * x * (sa * sb * hC - h7) -
    y * sa * (sa * sb * hS - h10)

theorem r10_ring (h4 : τ ^ 2 = 1 + 2 * x * y * z - x ^ 2 - y ^ 2 - z ^ 2)
    (h5 : sb * sc * cA = x - y * z) (h6 : sc * sa * cB = y - z * x)
    (h7 : sa * sb * cC = z - x * y) (h8 : sb * sc * sA = τ) (h9 : sc * sa * sB = τ)
    (hC : cC = 0) :
    (sb * sc) * (sc * sa) * (z * (sA * sB)) = (sb * sc) * (sc * sa) * (cA * cB) := by
  linear_combination z * (sc * sa * sB) * h8 + z * τ * h9 - (sc * sa * cB) * h5 -
    (x - y * z) * h6 + z * h4 + (1 - z ^ 2) * (sa * sb * hC - h7)

end Ring

/-! ## The rules in iPRA -/

theorem right_toZ {Γ : List (Fm PTm 26)} (h : Γ ⊢[PRAAx] rightC) :
    ZT.toZ Γ cC = 0 ∧ ZT.toZ Γ sC = 1 := by
  unfold rightC at h
  have hC := ZT.toZ_eq (Prf.andE₁ h)
  have hS := ZT.toZ_eq (Prf.andE₂ h)
  simp only [ZT.toZ_natLit, Nat.cast_zero, Nat.cast_one] at hC hS
  exact ⟨hC, hS⟩

/-- (R3). -/
def napierSinFormula : Fm PTm 26 := core ⟶ rightC ⟶ ZT.eq (sa * (sc * sB)) (sa * sb)

theorem napier_sin : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 26 napierSinFormula := by
  refine closeUniv 26 (.impI (.impI (ZT.derive ?_)))
  obtain ⟨_, _, _, _, _, _, _, _, h9, h10⟩ := core_toZ (Γ := [rightC, core]) Prf.hyp1
  obtain ⟨_, hS⟩ := right_toZ (Γ := [rightC, core]) Prf.hyp0
  simp only [ZT.toZ_mul]
  exact r3_ring h9 h10 hS

/-- (R4), (R5), (R6), (R7). -/
def napierTanFormula : Fm PTm 26 :=
  core ⟶ rightC ⟶ ZT.eq ((sb * sc) * (sa * cA)) ((sb * sc) * (x * sA * sb)) ⋏
    (ZT.eq ((sa * sc) * (sb * cB)) ((sa * sc) * (y * sB * sa)) ⋏
      (ZT.eq (sb * (sb * z)) (sb * (y * (cA * sc))) ⋏
        ZT.eq (sa * (sa * z)) (sa * (x * (cB * sc)))))

theorem napier_tan : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 26 napierTanFormula := by
  refine closeUniv 26 (.impI (.impI ?_))
  obtain ⟨h1, h2, _, _, h5, h6, h7, h8, h9, h10⟩ := core_toZ (Γ := [rightC, core]) Prf.hyp1
  obtain ⟨hC, hS⟩ := right_toZ (Γ := [rightC, core]) Prf.hyp0
  refine .andI (ZT.derive ?_) (.andI (ZT.derive ?_) (.andI (ZT.derive ?_) (ZT.derive ?_)))
  · simp only [ZT.toZ_mul]; exact r4_ring h2 h5 h7 h8 h10 hC hS
  · simp only [ZT.toZ_mul]; exact r5_ring h1 h6 h7 h9 h10 hC hS
  · simp only [ZT.toZ_mul]; exact r6_ring h2 h5 h7 hC
  · simp only [ZT.toZ_mul]; exact r7_ring h1 h6 h7 hC

/-- (R8), (R9), (R10). -/
def napierCosFormula : Fm PTm 26 :=
  core ⟶ rightC ⟶ ZT.eq (sa * sb * sc * cA) (sa * sb * sc * (sB * x)) ⋏
    (ZT.eq (sa * sb * sc * cB) (sa * sb * sc * (sA * y)) ⋏
      ZT.eq ((sb * sc) * (sc * sa) * (z * (sA * sB))) ((sb * sc) * (sc * sa) * (cA * cB)))

theorem napier_cos : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 26 napierCosFormula := by
  refine closeUniv 26 (.impI (.impI ?_))
  obtain ⟨h1, h2, _, h4, h5, h6, h7, h8, h9, h10⟩ := core_toZ (Γ := [rightC, core]) Prf.hyp1
  obtain ⟨hC, hS⟩ := right_toZ (Γ := [rightC, core]) Prf.hyp0
  refine .andI (ZT.derive ?_) (.andI (ZT.derive ?_) (ZT.derive ?_))
  · simp only [ZT.toZ_mul]; exact r8_ring h2 h5 h7 h9 h10 hC hS
  · simp only [ZT.toZ_mul]; exact r9_ring h1 h6 h7 h8 h10 hC hS
  · simp only [ZT.toZ_mul]; exact r10_ring h4 h5 h6 h7 h8 h9 hC

end LeanProofs.IPRA.Geometry.SphericalNapier
