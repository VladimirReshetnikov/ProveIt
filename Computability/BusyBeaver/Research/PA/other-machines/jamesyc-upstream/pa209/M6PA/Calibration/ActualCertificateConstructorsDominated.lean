module
public import M6PA.Theory
public import M6PA.Calibration.ActualCertificateConstructorsLeaves
@[expose] public section

/-! Fixed schematic certificates over arbitrary PA-model values. The finite
row recipes mirror ActualDominated exactly, but every leaf and MP produces
an explicit numeric V1 certificate justified by the all-model verifier. -/
namespace M6.PA.ActualCertificateConstructors.Dominated
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open SourceCantorInternal ActualCheckerBlueprint ActualHeadGraphs
open M6.PA.ActualCertificateConstructors
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Numeric data plus its verifier equation, never a Prop-extracted witness. -/
structure Certificate (a : V) where
  code : V
  accepted : verifyValue code = a+1

noncomputable abbrev wim (a b : V) : V := implicationValue a b
noncomputable abbrev rho8 (a b c u : V) : V :=
  wim (wim (wim c u) a) (wim (wim a c) (wim b c))

theorem refl (a : V) : a ≤ a := le_rfl

theorem implication_bound (x y : V) : pairValue x y ≤ wim x y := by
  change pairValue x y ≤ 4 * pairValue x y
  exact Arithmetic.le_mul_of_pos_left (by norm_num)

theorem le_l {u x : V} (y : V) (h : u ≤ x) : u ≤ wim x y :=
  le_trans h (le_trans (pairValue_bounds x y).1 (implication_bound x y))
theorem le_r {u y : V} (x : V) (h : u ≤ y) : u ≤ wim x y :=
  le_trans h (le_trans (pairValue_bounds x y).2 (implication_bound x y))

abbrev below (a b : V) : Prop := a ≤ b

variable [V↓[ℒₒᵣ] ⊧* theory]

noncomputable def mp (a b : V) (major : Certificate (wim a b))
    (minor : Certificate a) : Certificate b :=
  ⟨mpCertificate b minor.code major.code,verify_mp _ _ _ _ minor.accepted major.accepted⟩
noncomputable def row (a b c u : V) (h : u ≤ a) : Certificate (rho8 a b c u) :=
  ⟨leafCertificate 9 (pack4Value a b c u),verify_r8 a b c u h⟩
noncomputable def d1 (v0 : V) (v1 : V) (v2 : V) (v3 : V) (v4 : V) (hb0 : v3 ≤ v0) :
  Certificate (wim (wim (wim (wim v0 v1) (wim v2 v1)) (wim v1 v3)) (wim v4 (wim v1 v3))) :=
  (mp _ _ (row (wim (wim v0 v1) (wim v2 v1)) v4 (wim v1 v3) v0 (le_l (wim v2 v1) (le_l v1 (refl _)))) (row v0 v2 v1 v3 hb0))

noncomputable def d2 (v0 : V) (v1 : V) (v2 : V) (v3 : V) (v4 : V) (v5 : V) (hb0 : v2 ≤ v3) :
  Certificate (wim (wim (wim v0 (wim v1 v2)) (wim (wim v3 v1) (wim v4 v1))) (wim v5 (wim (wim v3 v1) (wim v4 v1)))) :=
  (mp _ _ (row (wim v0 (wim v1 v2)) v5 (wim (wim v3 v1) (wim v4 v1)) (wim v1 v2) (le_r v0 (refl _))) (d1 v3 v1 v4 v2 v0 hb0))

noncomputable def d3 (v0 : V) (v1 : V) (v2 : V) (v3 : V) :
  Certificate (wim v0 (wim (wim (wim v1 v2) v1) (wim v3 v1))) :=
  (mp _ _ (d2 (wim v1 (wim v1 v2)) v1 v2 (wim v1 v2) v3 v0 (le_r v1 (refl _))) (row (wim v1 v2) v3 v1 (wim v1 v2) (refl _)))

noncomputable def d4 (v0 : V) (v1 : V) (v2 : V) :
  Certificate (wim (wim (wim v0 v1) v0) (wim v2 v0)) :=
  (mp _ _ (d3 (wim (wim (wim v0 v0) v0) (wim (wim v0 v0) (wim v0 v0))) v0 v1 v2) (row v0 v0 v0 v0 (refl _)))

noncomputable def d5 (v0 : V) (v1 : V) (v2 : V) (v3 : V) :
  Certificate (wim (wim (wim v0 v1) (wim v1 v2)) (wim v3 (wim v1 v2))) :=
  (mp _ _ (row (wim v0 v1) v3 (wim v1 v2) v1 (le_r v0 (refl _))) (d4 v1 v2 v0))

noncomputable def d6 (v0 : V) (v1 : V) (v2 : V) (v3 : V) (v4 : V) :
  Certificate (wim (wim (wim v0 (wim v1 v2)) (wim v3 v1)) (wim v4 (wim v3 v1))) :=
  (mp _ _ (row (wim v0 (wim v1 v2)) v4 (wim v3 v1) (wim v1 v2) (le_r v0 (refl _))) (d5 v3 v1 v2 v0))

noncomputable def d7 (v0 : V) (v1 : V) (v2 : V) (v3 : V) :
  Certificate (wim v0 (wim (wim (wim (wim v1 v2) v3) v2) (wim v1 v2))) :=
  (mp _ _ (d6 (wim v2 (wim (wim v1 v2) v3)) (wim v1 v2) v3 (wim (wim (wim v1 v2) v3) v2) v0) (row (wim (wim v1 v2) v3) v1 v2 (wim (wim v1 v2) v3) (refl _)))

noncomputable def d8 (v0 : V) (v1 : V) (v2 : V) (v3 : V) (v4 : V) (v5 : V) :
  Certificate (wim (wim (wim v0 (wim v1 v2)) (wim v3 (wim v2 v4))) (wim v5 (wim v3 (wim v2 v4)))) :=
  (mp _ _ (row (wim v0 (wim v1 v2)) v5 (wim v3 (wim v2 v4)) (wim v1 v2) (le_r v0 (refl _))) (d6 v3 v2 v4 v1 v0))

noncomputable def d9 (v0 : V) (v1 : V) (v2 : V) :
  Certificate (wim (wim (wim (wim v0 v1) v2) v1) (wim v0 v1)) :=
  (mp _ _ (d7 (wim (wim (wim v0 v0) v0) (wim (wim v0 v0) (wim v0 v0))) v0 v1 v2) (row v0 v0 v0 v0 (refl _)))

noncomputable def d10 (v0 : V) (v1 : V) (v2 : V) (v3 : V) :
  Certificate (wim v0 (wim (wim (wim v1 v2) v3) (wim v2 v3))) :=
  (mp _ _ (d8 (wim v3 (wim v1 v2)) v1 v2 (wim (wim v1 v2) v3) v3 v0) (row (wim v1 v2) v2 v3 (wim v1 v2) (refl _)))

noncomputable def d11 (v0 : V) (v1 : V) (v2 : V) (v3 : V) :
  Certificate (wim (wim (wim v0 v1) (wim (wim v0 v1) v2)) (wim v3 (wim (wim v0 v1) v2))) :=
  (mp _ _ (row (wim v0 v1) v3 (wim (wim v0 v1) v2) v1 (le_r v0 (refl _))) (d9 v0 v1 v2))

noncomputable def d12 (v0 : V) (v1 : V) :
  Certificate (wim v0 (wim v1 v0)) :=
  (mp _ _ (d9 v0 (wim v1 v0) v0) (d4 v0 (wim v1 v0) v1))

noncomputable def d13 (v0 : V) (v1 : V) (v2 : V) :
  Certificate (wim (wim (wim v0 v1) v2) (wim v1 v2)) :=
  (mp _ _ (d10 (wim (wim (wim v0 v0) v0) (wim (wim v0 v0) (wim v0 v0))) v0 v1 v2) (row v0 v0 v0 v0 (refl _)))

noncomputable def d14 (v0 : V) (v1 : V) (v2 : V) :
  Certificate (wim v0 (wim (wim (wim v1 v2) v1) v1)) :=
  (mp _ _ (d11 (wim v1 v2) v1 v1 v0) (d4 v1 v2 (wim (wim v1 v2) v1)))

noncomputable def d15 (v0 : V) (v1 : V) (v2 : V) (v3 : V) :
  Certificate (wim (wim (wim v0 (wim v1 v2)) v1) (wim v3 v1)) :=
  (mp _ _ (row (wim v0 (wim v1 v2)) v3 v1 v2 (le_r v0 (le_r v1 (refl _)))) (d12 (wim v1 v2) v0))

noncomputable def d16 (v0 : V) (v1 : V) (v2 : V) :
  Certificate (wim v0 (wim (wim v0 v1) (wim v2 v1))) :=
  (mp _ _ (d13 (wim v1 v0) v0 (wim (wim v0 v1) (wim v2 v1))) (row v0 v2 v1 v0 (refl _)))

noncomputable def d17 (v0 : V) (v1 : V) (v2 : V) :
  Certificate (wim v0 (wim v1 (wim v2 v0))) :=
  (mp _ _ (d13 v2 v0 (wim v1 (wim v2 v0))) (d12 (wim v2 v0) v1))

noncomputable def d18 (v0 : V) (v1 : V) :
  Certificate (wim (wim (wim v0 v1) v0) v0) :=
  (mp _ _ (d14 (wim (wim (wim v0 v0) v0) (wim (wim v0 v0) (wim v0 v0))) v0 v1) (row v0 v0 v0 v0 (refl _)))

noncomputable def d19 (v0 : V) (v1 : V) (v2 : V) (v3 : V) (v4 : V) :
  Certificate (wim (wim (wim (wim (wim v0 v1) v2) (wim v3 v2)) v0) (wim v4 v0)) :=
  (mp _ _ (row (wim (wim (wim v0 v1) v2) (wim v3 v2)) v4 v0 v1 (le_l (wim v3 v2) (le_l v2 (le_r v0 (refl _))))) (d16 (wim v0 v1) v2 v3))

noncomputable def d20 (v0 : V) (v1 : V) (v2 : V) :
  Certificate (wim (wim v0 (wim v0 v1)) (wim v2 (wim v0 v1))) :=
  (mp _ _ (row v0 v2 (wim v0 v1) v0 (refl _)) (d18 v0 v1))

noncomputable def d21 (v0 : V) (v1 : V) (v2 : V) :
  Certificate (wim v0 (wim (wim v1 (wim v1 v2)) (wim v1 v2))) :=
  (mp _ _ (d11 v1 (wim v1 v2) (wim v1 v2) v0) (d20 v1 v2 (wim v1 (wim v1 v2))))

noncomputable def d22 (v0 : V) (v1 : V) :
  Certificate (wim (wim v0 (wim v0 v1)) (wim v0 v1)) :=
  (mp _ _ (d21 (wim (wim (wim v0 v0) v0) (wim (wim v0 v0) (wim v0 v0))) v0 v1) (row v0 v0 v0 v0 (refl _)))

noncomputable def d23 (v0 : V) (v1 : V) (v2 : V) :
  Certificate (wim (wim (wim v0 (wim v1 v2)) v1) v1) :=
  (mp _ _ (d22 (wim (wim v0 (wim v1 v2)) v1) v1) (d15 v0 v1 v2 (wim (wim v0 (wim v1 v2)) v1)))

noncomputable def d24 (v0 : V) (v1 : V) (v2 : V) (v3 : V) :
  Certificate (wim (wim (wim (wim (wim v0 v1) v2) (wim v3 v2)) v0) v0) :=
  (mp _ _ (d22 (wim (wim (wim (wim v0 v1) v2) (wim v3 v2)) v0) v0) (d19 v0 v1 v2 v3 (wim (wim (wim (wim v0 v1) v2) (wim v3 v2)) v0)))

noncomputable def d25 (v0 : V) (v1 : V) (v2 : V) (v3 : V) :
  Certificate (wim (wim v0 (wim v1 (wim v0 v2))) (wim v3 (wim v1 (wim v0 v2)))) :=
  (mp _ _ (row v0 v3 (wim v1 (wim v0 v2)) v0 (refl _)) (d23 v1 v0 v2))

noncomputable def d26 (v0 : V) (v1 : V) (v2 : V) (v3 : V) (v4 : V) :
  Certificate (wim (wim v0 (wim (wim (wim v0 v1) v2) (wim v3 v2))) (wim v4 (wim (wim (wim v0 v1) v2) (wim v3 v2)))) :=
  (mp _ _ (row v0 v4 (wim (wim (wim v0 v1) v2) (wim v3 v2)) v0 (refl _)) (d24 v0 v1 v2 v3))

noncomputable def d27 (v0 : V) (v1 : V) (v2 : V) :
  Certificate (wim (wim v0 (wim v1 (wim v0 v2))) (wim v1 (wim v0 v2))) :=
  (mp _ _ (d22 (wim v0 (wim v1 (wim v0 v2))) (wim v1 (wim v0 v2))) (d25 v0 v1 v2 (wim v0 (wim v1 (wim v0 v2)))))

noncomputable def d28 (v0 : V) (v1 : V) (v2 : V) (v3 : V) (v4 : V) (v5 : V) :
  Certificate (wim (wim (wim v0 (wim (wim (wim v1 v2) v3) (wim v4 v3))) v1) (wim v5 v1)) :=
  (mp _ _ (row (wim v0 (wim (wim (wim v1 v2) v3) (wim v4 v3))) v5 v1 (wim (wim (wim v1 v2) v3) (wim v4 v3)) (le_r v0 (refl _))) (d26 v1 v2 v3 v4 v0))

noncomputable def d29 (v0 : V) (v1 : V) (v2 : V) (v3 : V) (v4 : V) :
  Certificate (wim (wim (wim v0 (wim (wim (wim v1 v2) v3) (wim v4 v3))) v1) v1) :=
  (mp _ _ (d22 (wim (wim v0 (wim (wim (wim v1 v2) v3) (wim v4 v3))) v1) v1) (d28 v0 v1 v2 v3 v4 (wim (wim v0 (wim (wim (wim v1 v2) v3) (wim v4 v3))) v1)))

noncomputable def d30 (v0 : V) (v1 : V) (v2 : V) (hb0 : v2 ≤ v0) :
  Certificate (wim (wim v0 v1) (wim (wim (wim v1 v2) v0) v1)) :=
  (mp _ _ (d27 (wim (wim v1 v2) v0) (wim v0 v1) v1) (row v0 (wim (wim v1 v2) v0) v1 v2 hb0))

noncomputable def d31 (v0 : V) (v1 : V) (v2 : V) (v3 : V) (hb0 : v3 ≤ v0) :
  Certificate (wim (wim (wim (wim (wim v0 v1) (wim v2 v1)) v3) v0) (wim (wim v0 v1) (wim v2 v1))) :=
  (mp _ _ (d30 v0 (wim (wim v0 v1) (wim v2 v1)) v3 hb0) (d16 v0 v1 v2))

noncomputable def d32 (v0 : V) (v1 : V) (v2 : V) (v3 : V) :
  Certificate (wim (wim v0 (wim v1 v2)) (wim (wim (wim v0 v3) v2) (wim v1 v2))) :=
  (mp _ _ (d31 v0 (wim v1 v2) (wim (wim v0 v3) v2) v0 (refl _)) (d29 (wim v0 (wim v1 v2)) v0 v3 v2 v1))

noncomputable def d33 (v0 : V) (v1 : V) (v2 : V) (v3 : V) :
  Certificate (wim (wim (wim v0 v1) (wim v2 v3)) (wim (wim v0 v3) (wim v2 v3))) :=
  (mp _ _ (d32 v0 (wim v0 v3) (wim v2 v3) v1) (d16 v0 v3 v2))

noncomputable def d34 (v0 : V) (v1 : V) (v2 : V) (v3 : V) (hb0 : v3 ≤ v2) :
  Certificate (wim (wim (wim (wim v0 (wim v1 v2)) v3) v2) (wim v0 (wim v1 v2))) :=
  (mp _ _ (d30 v2 (wim v0 (wim v1 v2)) v3 hb0) (d17 v2 v0 v1))

noncomputable def d35 (v0 : V) (v1 : V) (v2 : V) (v3 : V) :
  Certificate (wim v0 (wim v1 (wim (wim v0 v2) (wim v3 v2)))) :=
  (mp _ _ (d34 v0 v1 (wim (wim v0 v2) (wim v3 v2)) (wim v3 v2) (le_r (wim v0 v2) (refl _))) (d33 v0 (wim v1 (wim (wim v0 v2) (wim v3 v2))) v3 v2))

noncomputable def d36 (v0 : V) (v1 : V) (v2 : V) (v3 : V) (hb0 : below v3 (wim v1 (wim v1 v2))) :
  Certificate (wim (wim (wim (wim v0 (wim v1 v2)) v3) (wim v1 (wim v1 v2))) (wim v0 (wim v1 v2))) :=
  (mp _ _ (d30 (wim v1 (wim v1 v2)) (wim v0 (wim v1 v2)) v3 hb0) (d20 v1 v2 v0))

noncomputable def d37 (v0 : V) (v1 : V) :
  Certificate (wim v0 (wim (wim v0 v1) v1)) :=
  (mp _ _ (d36 v0 (wim v0 v1) v1 (wim (wim v0 v1) v1) (le_r (wim v0 v1) (refl _))) (d33 v0 (wim (wim v0 v1) v1) (wim v0 v1) v1))

noncomputable def d38 (v0 : V) (v1 : V) (v2 : V) :
  Certificate (wim v0 (wim (wim (wim v1 v0) v2) v2)) :=
  (mp _ _ (d13 v1 v0 (wim (wim (wim v1 v0) v2) v2)) (d37 (wim v1 v0) v2))

noncomputable def d39 (v0 : V) (v1 : V) (v2 : V) :
  Certificate (wim (wim (wim v0 v1) v2) (wim (wim v0 v2) v2)) :=
  (mp _ _ (d32 v0 (wim v0 v2) v2 v1) (d37 v0 v2))

noncomputable def d40 (v0 : V) (v1 : V) (v2 : V) (v3 : V) :
  Certificate (wim (wim (wim v0 v1) v2) (wim (wim (wim v3 v0) v2) v2)) :=
  (mp _ _ (d32 v0 (wim (wim v3 v0) v2) v2 v1) (d38 v0 v3 v2))

noncomputable def d41 (v0 : V) (v1 : V) (v2 : V) (v3 : V) :
  Certificate (wim (wim v0 v1) (wim (wim (wim v2 (wim v0 v3)) v1) v1)) :=
  (mp _ _ (d33 v0 v3 (wim (wim v2 (wim v0 v3)) v1) v1) (d38 (wim v0 v3) v2 v1))

noncomputable def d42 (v0 : V) (v1 : V) (v2 : V) (v3 : V) :
  Certificate (wim (wim v0 (wim v1 (wim v2 (wim v0 v3)))) (wim v1 (wim v2 (wim v0 v3)))) :=
  (mp _ _ (d39 v0 v3 (wim v1 (wim v2 (wim v0 v3)))) (d17 (wim v0 v3) v1 v2))

noncomputable def d43 (v0 : V) (v1 : V) (v2 : V) :
  Certificate (wim (wim v0 (wim (wim (wim v0 v1) v2) v2)) (wim (wim (wim v0 v1) v2) v2)) :=
  (mp _ _ (d39 v0 v1 (wim (wim (wim v0 v1) v2) v2)) (d37 (wim v0 v1) v2))

noncomputable def d44 (v0 : V) (v1 : V) (v2 : V) :
  Certificate (wim (wim (wim (wim v0 v1) (wim v0 v2)) v1) v1) :=
  (mp _ _ (d43 (wim v0 v1) (wim v0 v2) v1) (d41 v0 v1 (wim v0 v1) v2))

noncomputable def d45 (v0 : V) (v1 : V) (v2 : V) (v3 : V) :
  Certificate (wim (wim (wim v0 (wim (wim v1 v2) (wim v1 v3))) v2) v2) :=
  (mp _ _ (d40 (wim (wim v1 v2) (wim v1 v3)) v2 v2 v0) (d44 v1 v2 v3))

noncomputable def d46 (v0 : V) (v1 : V) (v2 : V) :
  Certificate (wim (wim v0 (wim v1 v2)) (wim (wim v1 v0) (wim v1 v2))) :=
  (mp _ _ (d31 v0 (wim v1 v2) (wim v1 v0) v0 (refl _)) (d45 (wim v0 (wim v1 v2)) v1 v0 v2))

noncomputable def d47 (v0 : V) (v1 : V) (v2 : V) (v3 : V) :
  Certificate (wim (wim v0 v1) (wim v0 (wim (wim v1 v2) (wim v3 v2)))) :=
  (mp _ _ (d46 v1 v0 (wim (wim v1 v2) (wim v3 v2))) (d35 v1 v0 v2 v3))

noncomputable def d48 (v0 : V) (v1 : V) (v2 : V) (v3 : V) :
  Certificate (wim v0 (wim (wim (wim (wim v0 v1) v1) v2) (wim v3 v2))) :=
  (mp _ _ (d47 v0 (wim (wim v0 v1) v1) v2 v3) (d37 v0 v1))

noncomputable def d49 (v0 : V) (v1 : V) (v2 : V) :
  Certificate (wim (wim (wim (wim v0 v1) v1) v2) (wim v0 v2)) :=
  (mp _ _ (d27 v0 (wim (wim (wim v0 v1) v1) v2) v2) (d48 v0 v1 v2 v0))

noncomputable def d50 (v0 : V) (v1 : V) (v2 : V) (v3 : V) :
  Certificate (wim v0 (wim (wim v0 v1) (wim (wim v1 v2) (wim v3 v2)))) :=
  (mp _ _ (d49 v0 v1 (wim (wim v0 v1) (wim (wim v1 v2) (wim v3 v2)))) (d47 (wim v0 v1) v1 v2 v3))

noncomputable def d51 (v0 : V) (v1 : V) (v2 : V) :
  Certificate (wim (wim v0 v1) (wim (wim v1 v2) (wim v0 v2))) :=
  (mp _ _ (d42 v0 (wim v0 v1) (wim v1 v2) v2) (d50 v0 v1 v2 v0))

noncomputable def d52 (v0 : V) (v1 : V) (v2 : V) (v3 : V) :
  Certificate (wim (wim (wim (wim v0 v1) (wim v2 v1)) v3) (wim (wim v2 v0) v3)) :=
  (mp _ _ (d51 (wim v2 v0) (wim (wim v0 v1) (wim v2 v1)) v3) (d51 v2 v0 v1))

noncomputable def d53 (v0 : V) (v1 : V) (v2 : V) :
  Certificate (wim (wim v0 v1) (wim (wim v0 (wim v1 v2)) (wim v0 v2))) :=
  (mp _ _ (d52 v1 v2 v0 (wim (wim v0 (wim v1 v2)) (wim v0 v2))) (d46 (wim v1 v2) v0 v2))

noncomputable def d54 (v0 : V) (v1 : V) (v2 : V) :
  Certificate (wim (wim v0 (wim v1 v2)) (wim v1 (wim v0 v2))) :=
  (mp _ _ (d52 (wim v1 v2) v2 v0 (wim v1 (wim v0 v2))) (d49 v1 v2 (wim v0 v2)))

noncomputable def d55 (v0 : V) (v1 : V) (v2 : V) :
  Certificate (wim (wim v0 v1) (wim (wim v2 v0) (wim v2 v1))) :=
  (mp _ _ (d49 (wim v0 v1) (wim v2 v1) (wim (wim v2 v0) (wim v2 v1))) (d52 v0 v1 v2 (wim v2 v1)))

noncomputable def d57 (v0 : V) (v1 : V) (v2 : V) (v3 : V) :
  Certificate (wim (wim v0 (wim (wim v1 v2) v1)) (wim v0 (wim v3 v1))) :=
  (mp _ _ (d55 (wim (wim v1 v2) v1) (wim v3 v1) v0) (d4 v1 v2 v3))

noncomputable def rho8_all (a : V) (b : V) (c : V) (u : V) :
  Certificate (rho8 a b c u) :=
  (mp _ _ (d52 a c (wim c u) (wim (wim a c) (wim b c))) (d57 (wim a c) c u b))

noncomputable def composition (a : V) (b : V) (c : V) :
  Certificate (wim (wim a b) (wim (wim b c) (wim a c))) :=
  (d51 a b c)

noncomputable def lift_right (a : V) (b : V) (hab : Certificate (wim a b)) (x : V) :
  Certificate (wim (wim x a) (wim x b)) :=
  (mp _ _ (d55 a b x) hab)

noncomputable def k (a : V) (b : V) :
  Certificate (wim a (wim b a)) :=
  (d12 a b)

noncomputable def peirce (a : V) (b : V) :
  Certificate (wim (wim (wim a b) a) a) :=
  (d18 a b)

noncomputable def s (a : V) (b : V) (c : V) :
  Certificate (wim (wim a (wim b c)) (wim (wim a b) (wim a c))) :=
  (mp _ _ (d54 (wim a b) (wim a (wim b c)) (wim a c)) (d53 a b c))


/-- Public verifier equations expose the concrete recipe outputs. -/
theorem k_accepted (a b : V) : verifyValue (k a b).code = wim a (wim b a)+1 :=
  (k a b).accepted

theorem s_accepted (a b c : V) : verifyValue (s a b c).code =
    wim (wim a (wim b c)) (wim (wim a b) (wim a c))+1 := (s a b c).accepted

theorem peirce_accepted (a b : V) : verifyValue (peirce a b).code =
    wim (wim (wim a b) a) a+1 := (peirce a b).accepted

theorem composition_accepted (a b c : V) : verifyValue (composition a b c).code =
    wim (wim a b) (wim (wim b c) (wim a c))+1 := (composition a b c).accepted

#print axioms k_accepted
#print axioms s_accepted
#print axioms peirce_accepted
#print axioms composition_accepted
#print axioms rho8_all
end M6.PA.ActualCertificateConstructors.Dominated

