import IPRADerivations.Core.LinearAlgebra

/-!
# Spherical trigonometry in the vector model (`spherical_trigonometry_ipra_2026-11-15`)

The packet works with integer (or cleared rational) vectors `u, v, w` for the
vertices of a spherical triangle (`sections/03_vector_model.tex`,
`sections/04_core_laws.tex`). The following are derived in iPRA:

* the Binet–Cauchy identity `(u × v)·(r × s) = (u·r)(v·s) − (u·s)(v·r)`;
* its special case behind the division-free cosine law: for `u·u = 1`,
  `(u × v)·(u × w) = v·w − (u·v)(u·w)`, i.e. `s_b s_c c_A = x − y z`;
* the Gram identity `[u v w]² = (u·u)(v·v)(w·w) + 2(u·v)(v·w)(w·u) − (u·u)(v·w)² −
  (v·v)(w·u)² − (w·w)(u·v)²`, which for unit vectors with `x = v·w`, `y = w·u`,
  `z = u·v` is `τ² = 1 + 2xyz − x² − y² − z²`;
* the Lagrange identity `|u × v|² = (u·u)(v·v) − (u·v)²`;
* `gram_unit` (`lem:gram`, (3.5)) and the division-free cosine law at all three vertices
  (`cosine_law`, `cosine_law_b`, `cosine_law_c`: `thm:side-cosine`, (4.4)).
-/

namespace LeanProofs.IPRA.Geometry.SphericalTrigonometry

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn Matrix
open scoped Fm

section Ring

variable {R : Type*} [CommRing R]

theorem binetCauchy (u v r s : Fin 3 → R) :
    (u ⨯₃ v) ⬝ᵥ (r ⨯₃ s) = (u ⬝ᵥ r) * (v ⬝ᵥ s) - (u ⬝ᵥ s) * (v ⬝ᵥ r) := by
  simp [crossProduct, dotProduct, Fin.sum_univ_three]; ring

theorem gram (u v w : Fin 3 → R) :
    (u ⬝ᵥ (v ⨯₃ w)) ^ 2 = (u ⬝ᵥ u) * (v ⬝ᵥ v) * (w ⬝ᵥ w) + 2 * (u ⬝ᵥ v) * (v ⬝ᵥ w) * (w ⬝ᵥ u)
      - (u ⬝ᵥ u) * (v ⬝ᵥ w) ^ 2 - (v ⬝ᵥ v) * (w ⬝ᵥ u) ^ 2 - (w ⬝ᵥ w) * (u ⬝ᵥ v) ^ 2 := by
  simp [crossProduct, dotProduct, Fin.sum_univ_three]; ring

end Ring

section BinetCauchy

abbrev u : Vec 3 24 := Vec.vars 3 0 (by norm_num)
abbrev v : Vec 3 24 := Vec.vars 3 6 (by norm_num)
abbrev r : Vec 3 24 := Vec.vars 3 12 (by norm_num)
abbrev s : Vec 3 24 := Vec.vars 3 18 (by norm_num)

/-- `(u × v)·(r × s) = (u·r)(v·s) − (u·s)(v·r)`. -/
def binetCauchyFormula : Fm PTm 24 :=
  ZT.eq (Vec.dot (Vec.cross u v) (Vec.cross r s))
    (Vec.dot u r * Vec.dot v s - Vec.dot u s * Vec.dot v r)

theorem binet_cauchy : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 24 binetCauchyFormula :=
  closeUniv 24 (ZT.derive (by simpa [binetCauchyFormula] using binetCauchy _ _ _ _))

end BinetCauchy

section Triangle

abbrev a : Vec 3 18 := Vec.vars 3 0 (by norm_num)
abbrev b : Vec 3 18 := Vec.vars 3 6 (by norm_num)
abbrev c : Vec 3 18 := Vec.vars 3 12 (by norm_num)

/-- The Gram identity for `[a b c]²`. -/
def gramFormula : Fm PTm 18 :=
  ZT.eq (ZT.sq (Vec.triple a b c))
    (Vec.dot a a * Vec.dot b b * Vec.dot c c + ZT.natLit 2 * Vec.dot a b * Vec.dot b c * Vec.dot c a
      - Vec.dot a a * ZT.sq (Vec.dot b c) - Vec.dot b b * ZT.sq (Vec.dot c a)
      - Vec.dot c c * ZT.sq (Vec.dot a b))

theorem gram_identity : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 18 gramFormula :=
  closeUniv 18 (ZT.derive (by simpa [gramFormula] using gram _ _ _))

/-- The hypothesis that the vertex `a` is a unit vector. -/
def unitA : Fm PTm 18 := ZT.eq (Vec.dot a a) (ZT.natLit 1)

/-- The division-free spherical cosine law at `a`: if `a·a = 1` then
`(a × b)·(a × c) = b·c − (a·b)(a·c)`. -/
def cosineLawFormula : Fm PTm 18 :=
  unitA ⟶ ZT.eq (Vec.dot (Vec.cross a b) (Vec.cross a c)) (Vec.dot b c - Vec.dot a b * Vec.dot a c)

theorem cosine_law : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 18 cosineLawFormula := by
  refine closeUniv 18 (.impI (ZT.derive ?_))
  have h := ZT.toZ_mem (Γ := [unitA]) (u := Vec.dot a a) (v := ZT.natLit 1) (by simp [unitA])
  simp only [Vec.toZ_dot, ZT.toZ_natLit, Nat.cast_one] at h
  rw [Vec.toZ_dot, Vec.toZ_cross, Vec.toZ_cross, binetCauchy, h,
    dotProduct_comm (Vec.toZ _ b) (Vec.toZ _ a)]
  simp only [ZT.toZ_sub, ZT.toZ_mul, Vec.toZ_dot]
  ring

/-- The Lagrange identity `|a × b|² = (a·a)(b·b) − (a·b)²`. -/
def lagrangeFormula : Fm PTm 18 :=
  ZT.eq (Vec.dot (Vec.cross a b) (Vec.cross a b)) (Vec.dot a a * Vec.dot b b - ZT.sq (Vec.dot a b))

theorem lagrange_identity : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 18 lagrangeFormula :=
  closeUniv 18 (ZT.derive (by
    simp only [Vec.toZ_dot, Vec.toZ_cross, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_sq, binetCauchy]
    rw [dotProduct_comm (Vec.toZ _ b) (Vec.toZ _ a)]
    ring))

/-- The unit hypotheses at `b` and `c`. -/
def unitB : Fm PTm 18 := ZT.eq (Vec.dot b b) (ZT.natLit 1)
def unitC : Fm PTm 18 := ZT.eq (Vec.dot c c) (ZT.natLit 1)

/-- `lem:gram`, (3.5): for unit `a, b, c` with `x = b·c`, `y = c·a`, `z = a·b`,
`τ² = [a b c]² = 1 + 2xyz − x² − y² − z²`. -/
def gramUnitFormula : Fm PTm 18 :=
  unitA ⟶ unitB ⟶ unitC ⟶ ZT.eq (ZT.sq (Vec.triple a b c))
    (ZT.natLit 1 + ZT.natLit 2 * Vec.dot b c * Vec.dot c a * Vec.dot a b
      - ZT.sq (Vec.dot b c) - ZT.sq (Vec.dot c a) - ZT.sq (Vec.dot a b))

theorem gram_unit : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 18 gramUnitFormula := by
  refine closeUniv 18 (.impI (.impI (.impI (ZT.derive ?_))))
  have ha := ZT.toZ_mem (Γ := [unitC, unitB, unitA]) (u := Vec.dot a a) (v := ZT.natLit 1) (by simp [unitA])
  have hb := ZT.toZ_mem (Γ := [unitC, unitB, unitA]) (u := Vec.dot b b) (v := ZT.natLit 1) (by simp [unitB])
  have hc := ZT.toZ_mem (Γ := [unitC, unitB, unitA]) (u := Vec.dot c c) (v := ZT.natLit 1) (by simp [unitC])
  simp only [Vec.toZ_dot, ZT.toZ_natLit, Nat.cast_one] at ha hb hc
  simp only [ZT.toZ_sq, Vec.toZ_triple, ZT.toZ_sub, ZT.toZ_add, ZT.toZ_mul, ZT.toZ_natLit, Vec.toZ_dot]
  rw [gram, ha, hb, hc]
  push_cast
  ring

/-- `thm:side-cosine`, (4.4) at `b`: if `b·b = 1` then `(b × c)·(b × a) = c·a − (b·c)(b·a)`, i.e.
`s_c s_a c_B = y − z x`. -/
def cosineLawBFormula : Fm PTm 18 :=
  unitB ⟶ ZT.eq (Vec.dot (Vec.cross b c) (Vec.cross b a)) (Vec.dot c a - Vec.dot b c * Vec.dot b a)

theorem cosine_law_b : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 18 cosineLawBFormula := by
  refine closeUniv 18 (.impI (ZT.derive ?_))
  have h := ZT.toZ_mem (Γ := [unitB]) (u := Vec.dot b b) (v := ZT.natLit 1) (by simp [unitB])
  simp only [Vec.toZ_dot, ZT.toZ_natLit, Nat.cast_one] at h
  rw [Vec.toZ_dot, Vec.toZ_cross, Vec.toZ_cross, binetCauchy, h,
    dotProduct_comm (Vec.toZ _ c) (Vec.toZ _ b)]
  simp only [ZT.toZ_sub, ZT.toZ_mul, Vec.toZ_dot]
  ring

/-- `thm:side-cosine`, (4.4) at `c`: if `c·c = 1` then `(c × a)·(c × b) = a·b − (c·a)(c·b)`, i.e.
`s_a s_b c_C = z − x y`. -/
def cosineLawCFormula : Fm PTm 18 :=
  unitC ⟶ ZT.eq (Vec.dot (Vec.cross c a) (Vec.cross c b)) (Vec.dot a b - Vec.dot c a * Vec.dot c b)

theorem cosine_law_c : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 18 cosineLawCFormula := by
  refine closeUniv 18 (.impI (ZT.derive ?_))
  have h := ZT.toZ_mem (Γ := [unitC]) (u := Vec.dot c c) (v := ZT.natLit 1) (by simp [unitC])
  simp only [Vec.toZ_dot, ZT.toZ_natLit, Nat.cast_one] at h
  rw [Vec.toZ_dot, Vec.toZ_cross, Vec.toZ_cross, binetCauchy, h,
    dotProduct_comm (Vec.toZ _ a) (Vec.toZ _ c)]
  simp only [ZT.toZ_sub, ZT.toZ_mul, Vec.toZ_dot]
  ring

end Triangle

end LeanProofs.IPRA.Geometry.SphericalTrigonometry
