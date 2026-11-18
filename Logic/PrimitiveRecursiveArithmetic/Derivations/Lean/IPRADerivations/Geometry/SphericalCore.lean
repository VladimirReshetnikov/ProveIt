import IPRADerivations.Geometry.SphericalTrigonometry

/-!
# Consequences of the finite spherical core (`spherical_trigonometry_ipra_2026-11-15`)

Section 4 of the packet presents spherical trigonometry by the finite polynomial core (4.16),
in the cosines `x, y, z` of the sides, the triple product `τ`, the side sines `s_a, s_b, s_c`
and the angle pairs `(c_A, s_A)`, `(c_B, s_B)`, `(c_C, s_C)`:

* `s_a² + x² = 1`, `s_b² + y² = 1`, `s_c² + z² = 1` (Lagrange);
* `τ² = 1 + 2xyz − x² − y² − z²` (Gram);
* `s_b s_c c_A = x − yz`, `s_c s_a c_B = y − zx`, `s_a s_b c_C = z − xy` (side cosine laws);
* `s_b s_c s_A = τ`, `s_c s_a s_B = τ`, `s_a s_b s_C = τ` (sine laws).

"Every formula in this section is a consequence of (4.16) by polynomial normalization and guarded
cancellation." Here the consequences are derived in iPRA, as implications over integer values,
in the division-free form multiplied by the guard that the paper cancels:

* `gram_factor` (3.6): `τ² = s_b² s_c² − (x − yz)²`;
* `angle_unit` (`lem:angle-unit`): `s_b² s_c² (c_A² + s_A²) = s_b² s_c²`;
* `sine_law` (`thm:sine-law`, (4.9)): `s_c · s_A s_b = s_c · s_B s_a`;
* `angle_cosine` (`thm:angle-cosine`, (4.11)): `s_a² s_b s_c c_A = s_a² s_b s_c (s_B s_C x − c_B c_C)`;
* `cagnoli` (`thm:cagnoli`, (8.8)):
  `s_a² s_b s_c (s_b s_c + yz c_A) = s_a² s_b s_c (s_B s_C − c_B c_C x)`.

* `five_part`, `four_part` (cotangent rule), and the right-triangle rules `right_rules`.

The core is invariant under the cyclic relabelling `A → B → C`, so the universally closed
statements also give the cyclic companions by instantiation.
-/

namespace LeanProofs.IPRA.Geometry.SphericalCore

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm

/-! ## The ring-level certificates -/

section Ring

variable {R : Type*} [CommRing R] {x y z τ sa sb sc cA cB cC sA sB sC : R}

theorem gram_factor_ring (h2 : sb ^ 2 + y ^ 2 = 1) (h3 : sc ^ 2 + z ^ 2 = 1)
    (h4 : τ ^ 2 = 1 + 2 * x * y * z - x ^ 2 - y ^ 2 - z ^ 2) :
    τ ^ 2 = sb ^ 2 * sc ^ 2 - (x - y * z) ^ 2 := by
  linear_combination h4 - (1 - y ^ 2) * h3 - sc ^ 2 * h2

theorem angle_unit_ring (h2 : sb ^ 2 + y ^ 2 = 1) (h3 : sc ^ 2 + z ^ 2 = 1)
    (h4 : τ ^ 2 = 1 + 2 * x * y * z - x ^ 2 - y ^ 2 - z ^ 2) (h5 : sb * sc * cA = x - y * z)
    (h8 : sb * sc * sA = τ) :
    sb ^ 2 * sc ^ 2 * (cA ^ 2 + sA ^ 2) = sb ^ 2 * sc ^ 2 := by
  linear_combination (sb * sc * cA + x - y * z) * h5 + (sb * sc * sA + τ) * h8 + h4 - (1 - y ^ 2) * h3 -
    sc ^ 2 * h2

theorem sine_law_ring (h8 : sb * sc * sA = τ) (h9 : sc * sa * sB = τ) :
    sc * (sA * sb) = sc * (sB * sa) := by
  linear_combination h8 - h9

theorem angle_cosine_ring (h1 : sa ^ 2 + x ^ 2 = 1)
    (h4 : τ ^ 2 = 1 + 2 * x * y * z - x ^ 2 - y ^ 2 - z ^ 2) (h5 : sb * sc * cA = x - y * z)
    (h6 : sc * sa * cB = y - z * x) (h7 : sa * sb * cC = z - x * y) (h9 : sc * sa * sB = τ)
    (h10 : sa * sb * sC = τ) :
    sa ^ 2 * sb * sc * cA = sa ^ 2 * sb * sc * (sB * sC * x - cB * cC) := by
  linear_combination sa ^ 2 * h5 + sa * sb * cC * h6 + (y - z * x) * h7 - x * (sa * sb * sC) * h9 -
    x * τ * h10 + (x - y * z) * h1 - x * h4

theorem cagnoli_ring (h1 : sa ^ 2 + x ^ 2 = 1) (h2 : sb ^ 2 + y ^ 2 = 1) (h3 : sc ^ 2 + z ^ 2 = 1)
    (h4 : τ ^ 2 = 1 + 2 * x * y * z - x ^ 2 - y ^ 2 - z ^ 2) (h5 : sb * sc * cA = x - y * z)
    (h6 : sc * sa * cB = y - z * x) (h7 : sa * sb * cC = z - x * y) (h9 : sc * sa * sB = τ)
    (h10 : sa * sb * sC = τ) :
    sa ^ 2 * sb * sc * (sb * sc + y * z * cA) = sa ^ 2 * sb * sc * (sB * sC - cB * cC * x) := by
  linear_combination (sb ^ 2 * sc ^ 2 + y * z * (x - y * z)) * h1 + (1 - x ^ 2) * sc ^ 2 * h2 +
    (1 - x ^ 2) * (1 - y ^ 2) * h3 + sa ^ 2 * y * z * h5 - h4 - τ * h10 - sa * sb * sC * h9 +
    x * (sa * sb * cC) * h6 + x * (y - z * x) * h7

theorem five_part_ring (h3 : sc ^ 2 + z ^ 2 = 1) (h5 : sb * sc * cA = x - y * z)
    (h6 : sc * sa * cB = y - z * x) :
    sc * (sa * cB) = sc * (y * sc - z * sb * cA) := by
  linear_combination -y * h3 + h6 + z * h5

theorem four_part_ring (h1 : sa ^ 2 + x ^ 2 = 1) (h6 : sc * sa * cB = y - z * x)
    (h7 : sa * sb * cC = z - x * y) (h9 : sc * sa * sB = τ) (h10 : sa * sb * sC = τ) :
    sc * sa ^ 2 * sb * (x * cC * sb * sB) = sc * sa ^ 2 * sb * (sa * y * sB - sC * cB * sb) := by
  linear_combination -sb * τ * y * h1 + x * sb * sc * sa * sB * h7 + (x * sb * (z - x * y) - y * sa ^ 2 * sb) * h9 +
    sb * sc * sa * cB * h10 + sb * τ * h6

theorem right_cos_ring (h7 : sa * sb * cC = z - x * y) (hC : cC = 0) : z = x * y := by
  linear_combination sa * sb * hC - h7

theorem right_sine_ring (h8 : sb * sc * sA = τ) (h10 : sa * sb * sC = τ) (hS : sC = 1) :
    sb * (sc * sA) = sb * sa := by
  linear_combination h8 + sa * sb * hS - h10

theorem right_cosA_ring (h2 : sb ^ 2 + y ^ 2 = 1) (h5 : sb * sc * cA = x - y * z)
    (h7 : sa * sb * cC = z - x * y) (hC : cC = 0) :
    sb * (sc * cA) = sb * (x * sb) := by
  linear_combination h5 - x * h2 - y * sa * sb * hC + y * h7

end Ring

/-! ## The core as an iPRA hypothesis -/

abbrev x : ZT 26 := .var2 0 1
abbrev y : ZT 26 := .var2 2 3
abbrev z : ZT 26 := .var2 4 5
abbrev τ : ZT 26 := .var2 6 7
abbrev sa : ZT 26 := .var2 8 9
abbrev sb : ZT 26 := .var2 10 11
abbrev sc : ZT 26 := .var2 12 13
abbrev cA : ZT 26 := .var2 14 15
abbrev cB : ZT 26 := .var2 16 17
abbrev cC : ZT 26 := .var2 18 19
abbrev sA : ZT 26 := .var2 20 21
abbrev sB : ZT 26 := .var2 22 23
abbrev sC : ZT 26 := .var2 24 25

/-- The finite core (4.16). -/
def core : Fm PTm 26 :=
  ZT.eq (ZT.sq sa + ZT.sq x) (ZT.natLit 1) ⋏ (ZT.eq (ZT.sq sb + ZT.sq y) (ZT.natLit 1) ⋏
  (ZT.eq (ZT.sq sc + ZT.sq z) (ZT.natLit 1) ⋏
  (ZT.eq (ZT.sq τ) (ZT.natLit 1 + ZT.natLit 2 * x * y * z - ZT.sq x - ZT.sq y - ZT.sq z) ⋏
  (ZT.eq (sb * sc * cA) (x - y * z) ⋏ (ZT.eq (sc * sa * cB) (y - z * x) ⋏
  (ZT.eq (sa * sb * cC) (z - x * y) ⋏ (ZT.eq (sb * sc * sA) τ ⋏
  (ZT.eq (sc * sa * sB) τ ⋏ ZT.eq (sa * sb * sC) τ))))))))

section Hyps

variable {Γ : List (Fm PTm 26)}

/-- The ten core relations, read as equations of evaluations. -/
theorem core_toZ (h : Γ ⊢[PRAAx] core) :
    ZT.toZ Γ sa ^ 2 + ZT.toZ Γ x ^ 2 = 1 ∧ ZT.toZ Γ sb ^ 2 + ZT.toZ Γ y ^ 2 = 1 ∧
    ZT.toZ Γ sc ^ 2 + ZT.toZ Γ z ^ 2 = 1 ∧
    ZT.toZ Γ τ ^ 2 = 1 + 2 * ZT.toZ Γ x * ZT.toZ Γ y * ZT.toZ Γ z - ZT.toZ Γ x ^ 2 - ZT.toZ Γ y ^ 2 -
      ZT.toZ Γ z ^ 2 ∧
    ZT.toZ Γ sb * ZT.toZ Γ sc * ZT.toZ Γ cA = ZT.toZ Γ x - ZT.toZ Γ y * ZT.toZ Γ z ∧
    ZT.toZ Γ sc * ZT.toZ Γ sa * ZT.toZ Γ cB = ZT.toZ Γ y - ZT.toZ Γ z * ZT.toZ Γ x ∧
    ZT.toZ Γ sa * ZT.toZ Γ sb * ZT.toZ Γ cC = ZT.toZ Γ z - ZT.toZ Γ x * ZT.toZ Γ y ∧
    ZT.toZ Γ sb * ZT.toZ Γ sc * ZT.toZ Γ sA = ZT.toZ Γ τ ∧
    ZT.toZ Γ sc * ZT.toZ Γ sa * ZT.toZ Γ sB = ZT.toZ Γ τ ∧
    ZT.toZ Γ sa * ZT.toZ Γ sb * ZT.toZ Γ sC = ZT.toZ Γ τ := by
  unfold core at h
  have e₁ := ZT.toZ_eq (Prf.andE₁ h)
  have e₂ := ZT.toZ_eq (Prf.andE₁ (Prf.andE₂ h))
  have e₃ := ZT.toZ_eq (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ h)))
  have e₄ := ZT.toZ_eq (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h))))
  have e₅ := ZT.toZ_eq (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h)))))
  have e₆ := ZT.toZ_eq (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h))))))
  have e₇ := ZT.toZ_eq (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h)))))))
  have e₈ := ZT.toZ_eq (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂
    (Prf.andE₂ h))))))))
  have e₉ := ZT.toZ_eq (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂
    (Prf.andE₂ (Prf.andE₂ h)))))))))
  have e₁₀ := ZT.toZ_eq (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂
    (Prf.andE₂ (Prf.andE₂ h)))))))))
  simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_sub, ZT.toZ_sq, ZT.toZ_natLit, Nat.cast_one,
    Nat.cast_ofNat] at e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀
  exact ⟨e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈, e₉, e₁₀⟩

end Hyps

/-! ## The derived laws -/

def gramFactorFormula : Fm PTm 26 :=
  core ⟶ ZT.eq (ZT.sq τ) (ZT.sq sb * ZT.sq sc - ZT.sq (x - y * z))

theorem gram_factor : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 26 gramFactorFormula := by
  refine closeUniv 26 (.impI (ZT.derive ?_))
  obtain ⟨_, h2, h3, h4, -⟩ := core_toZ (Γ := [core]) Prf.hyp0
  simp only [ZT.toZ_mul, ZT.toZ_sub, ZT.toZ_sq]
  exact gram_factor_ring h2 h3 h4

def angleUnitFormula : Fm PTm 26 :=
  core ⟶ ZT.eq (ZT.sq sb * ZT.sq sc * (ZT.sq cA + ZT.sq sA)) (ZT.sq sb * ZT.sq sc)

theorem angle_unit : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 26 angleUnitFormula := by
  refine closeUniv 26 (.impI (ZT.derive ?_))
  obtain ⟨_, h2, h3, h4, h5, _, _, h8, -⟩ := core_toZ (Γ := [core]) Prf.hyp0
  simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_sq]
  exact angle_unit_ring h2 h3 h4 h5 h8

def sineLawFormula : Fm PTm 26 := core ⟶ ZT.eq (sc * (sA * sb)) (sc * (sB * sa))

theorem sine_law : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 26 sineLawFormula := by
  refine closeUniv 26 (.impI (ZT.derive ?_))
  obtain ⟨_, _, _, _, _, _, _, h8, h9, -⟩ := core_toZ (Γ := [core]) Prf.hyp0
  simp only [ZT.toZ_mul]
  exact sine_law_ring h8 h9

/-- `cor:sine-volume`, (4.10) cleared: with `6V = τ` (the triple product of the vertex vectors),
`sin A (sin a sin b sin c) = 6V sin a`, i.e. `sin A / sin a = 6V / (sin a sin b sin c)`. -/
def sineVolumeFormula : Fm PTm 26 := core ⟶ ZT.eq (sA * (sa * sb * sc)) (τ * sa)

theorem sine_volume : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 26 sineVolumeFormula := by
  refine closeUniv 26 (.impI (ZT.derive ?_))
  obtain ⟨_, _, _, _, _, _, _, h8, -⟩ := core_toZ (Γ := [core]) Prf.hyp0
  simp only [ZT.toZ_mul]
  linear_combination ZT.toZ [core] sa * h8

def angleCosineFormula : Fm PTm 26 :=
  core ⟶ ZT.eq (ZT.sq sa * sb * sc * cA) (ZT.sq sa * sb * sc * (sB * sC * x - cB * cC))

theorem angle_cosine : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 26 angleCosineFormula := by
  refine closeUniv 26 (.impI (ZT.derive ?_))
  obtain ⟨h1, _, _, h4, h5, h6, h7, _, h9, h10⟩ := core_toZ (Γ := [core]) Prf.hyp0
  simp only [ZT.toZ_mul, ZT.toZ_sub, ZT.toZ_sq]
  exact angle_cosine_ring h1 h4 h5 h6 h7 h9 h10

def cagnoliFormula : Fm PTm 26 :=
  core ⟶ ZT.eq (ZT.sq sa * sb * sc * (sb * sc + y * z * cA)) (ZT.sq sa * sb * sc * (sB * sC - cB * cC * x))

theorem cagnoli : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 26 cagnoliFormula := by
  refine closeUniv 26 (.impI (ZT.derive ?_))
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, _, h9, h10⟩ := core_toZ (Γ := [core]) Prf.hyp0
  simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_sub, ZT.toZ_sq]
  exact cagnoli_ring h1 h2 h3 h4 h5 h6 h7 h9 h10

/-- The five-part rule `sin a cos B = cos b sin c − sin b cos c cos A`, times `s_c`. -/
def fivePartFormula : Fm PTm 26 := core ⟶ ZT.eq (sc * (sa * cB)) (sc * (y * sc - z * sb * cA))

theorem five_part : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 26 fivePartFormula := by
  refine closeUniv 26 (.impI (ZT.derive ?_))
  obtain ⟨_, _, h3, _, h5, h6, -⟩ := core_toZ (Γ := [core]) Prf.hyp0
  simp only [ZT.toZ_mul, ZT.toZ_sub]
  exact five_part_ring h3 h5 h6

/-- The four-part (cotangent) rule `cos a cos C = sin a cot b − sin C cot B`, cleared by
`s_b s_B` and multiplied by the guard `s_c s_a² s_b`. -/
def fourPartFormula : Fm PTm 26 :=
  core ⟶ ZT.eq (sc * ZT.sq sa * sb * (x * cC * sb * sB)) (sc * ZT.sq sa * sb * (sa * y * sB - sC * cB * sb))

theorem four_part : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 26 fourPartFormula := by
  refine closeUniv 26 (.impI (ZT.derive ?_))
  obtain ⟨h1, _, _, _, _, h6, h7, _, h9, h10⟩ := core_toZ (Γ := [core]) Prf.hyp0
  simp only [ZT.toZ_mul, ZT.toZ_sub, ZT.toZ_sq]
  exact four_part_ring h1 h6 h7 h9 h10

/-- A right angle at `C`: `c_C = 0`, `s_C = 1`. -/
def rightC : Fm PTm 26 := ZT.eq cC (ZT.natLit 0) ⋏ ZT.eq sC (ZT.natLit 1)

/-- Right spherical triangles: `cos c = cos a cos b`, `sin a = sin c sin A` (times `s_b`) and
`cos A = tan b cot c` as `s_b · s_c c_A = s_b · x s_b`. -/
def rightFormula : Fm PTm 26 :=
  core ⟶ rightC ⟶ ZT.eq z (x * y) ⋏ (ZT.eq (sb * (sc * sA)) (sb * sa) ⋏ ZT.eq (sb * (sc * cA)) (sb * (x * sb)))

theorem right_rules : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 26 rightFormula := by
  refine closeUniv 26 (.impI (.impI ?_))
  obtain ⟨_, h2, _, _, h5, _, h7, h8, _, h10⟩ := core_toZ (Γ := [rightC, core]) Prf.hyp1
  have hr : ([rightC, core] : List (Fm PTm 26)) ⊢[PRAAx] rightC := Prf.hyp0
  unfold rightC at hr
  have hC := ZT.toZ_eq (Prf.andE₁ hr)
  have hS := ZT.toZ_eq (Prf.andE₂ hr)
  simp only [ZT.toZ_natLit, Nat.cast_zero, Nat.cast_one] at hC hS
  refine .andI (ZT.derive ?_) (.andI (ZT.derive ?_) (ZT.derive ?_))
  · simp only [ZT.toZ_mul]; exact right_cos_ring h7 hC
  · simp only [ZT.toZ_mul]; exact right_sine_ring h8 h10 hS
  · simp only [ZT.toZ_mul]; exact right_cosA_ring h2 h5 h7 hC

end LeanProofs.IPRA.Geometry.SphericalCore
