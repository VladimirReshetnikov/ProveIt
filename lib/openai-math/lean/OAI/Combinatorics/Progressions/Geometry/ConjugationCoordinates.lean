import OAI.Combinatorics.Progressions.Nilpotent.BCHOuterGridChangeBasis
import OAI.Combinatorics.Progressions.Nilpotent.BCHUniformQuotientCharts

namespace OAI

section

namespace Erdos3

open Module MvPolynomial

def conjugationInput {ι : Type*} (a b : ι → ℚ) : Fin 3 × ι → ℚ :=
  fun ji => ![a ji.2, b ji.2, -a ji.2] ji.1

theorem conjugationInput_mem_denominatorGrid {ι : Type*} (a b : ι → ℚ) (q : ℕ)
    (ha : a ∈ denominatorGrid q) (hb : b ∈ denominatorGrid q) :
    conjugationInput a b ∈ denominatorGrid q := by
  obtain ⟨za, hza⟩ := ha
  obtain ⟨zb, hzb⟩ := hb
  refine ⟨fun ji => ![za ji.2, zb ji.2, -za ji.2] ji.1, ?_⟩
  rintro ⟨j, i⟩
  have hai : (q : ℚ) * a i = (za i : ℚ) := hza i
  have hbi : (q : ℚ) * b i = (zb i : ℚ) := hzb i
  fin_cases j <;> simp [conjugationInput, Pi.smul_apply, smul_eq_mul, hai, hbi]

theorem scaledIntegerGrid_mem_denominatorGrid {ι : Type*} (m q : ℕ) {b : ι → ℚ}
    (hb : b ∈ scaledIntegerGrid m) : b ∈ denominatorGrid q := by
  obtain ⟨z, rfl⟩ := hb
  refine ⟨fun i => (q : ℤ) * m * z i, ?_⟩
  intro i
  simp [Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem conjugationInput_sub_mem_scaledGrid {ι : Type*} (a b : ι → ℚ) (m : ℕ)
    (hb : b ∈ scaledIntegerGrid m) :
    conjugationInput a b - conjugationInput a 0 ∈ scaledIntegerGrid m := by
  obtain ⟨z, hz⟩ := hb
  refine ⟨fun ji => ![0, z ji.2, 0] ji.1, ?_⟩
  funext ⟨j, i⟩
  have hi := congrFun hz i
  change b i = (m : ℚ) * (z i : ℚ) at hi
  fin_cases j <;> simp [conjugationInput, Pi.smul_apply, smul_eq_mul, hi]

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

noncomputable def conjugationCoordinatePolynomial (e : Basis ι ℚ L) (s : ℕ) (i : ι) :
    MvPolynomial (Fin 3 × ι) ℚ :=
  bchProductCoordinatePolynomial (lieStructureConstants e) s [0, 1, 2] i

theorem conjugationCoordinatePolynomial_degree (e : Basis ι ℚ L) (s : ℕ) (i : ι) :
    (conjugationCoordinatePolynomial e s i).totalDegree ≤ s :=
  bchProductCoordinatePolynomial_totalDegree _ _ _ _

theorem conjugationCoordinatePolynomial_eval (e : Basis ι ℚ L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (z g : NilpotentLieBCHGroup L s hnil) (i : ι) :
    eval (conjugationInput (e.equivFun z.coord) (e.equivFun g.coord))
      (conjugationCoordinatePolynomial e s i) = e.repr (z * g * z⁻¹).coord i := by
  let f : Fin 3 → NilpotentLieBCHGroup L s hnil := ![z, g, z⁻¹]
  have he := bchProductCoordinatePolynomial_eval e s hnil (fun j => (f j).coord) [0, 1, 2] i
  have hp := lieBCHList_group_prod s hnil (fun j => (f j).coord) [0, 1, 2]
  rw [← hp] at he
  have hmap : ([0, 1, 2].map (fun j => (⟨(f j).coord⟩ : NilpotentLieBCHGroup L s hnil))) =
      [z, g, z⁻¹] := by simp [f]; rfl
  rw [hmap] at he
  simp only [List.prod_cons, List.prod_nil, mul_one] at he
  have hi : (fun ji : Fin 3 × ι => e.repr (f ji.1).coord ji.2) =
      conjugationInput (e.equivFun z.coord) (e.equivFun g.coord) := by
    funext ⟨j, k⟩
    fin_cases j <;> simp [f, conjugationInput]
  change eval (fun ji : Fin 3 × ι => e.repr (f ji.1).coord ji.2)
    (conjugationCoordinatePolynomial e s i) = _ at he
  rw [hi] at he
  simpa only [mul_assoc] using he

theorem conjugationCoordinatePolynomial_zero (e : Basis ι ℚ L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (z : NilpotentLieBCHGroup L s hnil) (i : ι) :
    eval (conjugationInput (e.equivFun z.coord) 0) (conjugationCoordinatePolynomial e s i) = 0 := by
  simpa using conjugationCoordinatePolynomial_eval e hnil z 1 i

theorem conjugation_preserves_inner_grid (e : Basis ι ℚ L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) (q l : ℕ) (hq : 0 < q)
    (z g : NilpotentLieBCHGroup L s hnil)
    (hz : e.equivFun z.coord ∈ denominatorGrid q)
    (hg : e.equivFun g.coord ∈ scaledIntegerGrid
      (l * polynomialFamilyDenominator (conjugationCoordinatePolynomial e s) * q ^ s)) :
    e.equivFun (z * g * z⁻¹).coord ∈ scaledIntegerGrid l := by
  have hb := scaledIntegerGrid_mem_denominatorGrid _ q hg
  have hzero : (0 : ι → ℚ) ∈ denominatorGrid q := ⟨0, by simp⟩
  have h := rational_polynomial_family_eval_sub_mem_grid
    (conjugationCoordinatePolynomial e s) q s l hq (conjugationCoordinatePolynomial_degree e s)
    (conjugationInput (e.equivFun z.coord) (e.equivFun g.coord))
    (conjugationInput (e.equivFun z.coord) 0)
    (conjugationInput_mem_denominatorGrid _ _ q hz hb)
    (conjugationInput_mem_denominatorGrid _ _ q hz hzero)
    (conjugationInput_sub_mem_scaledGrid _ _ _ hg)
  simpa only [conjugationCoordinatePolynomial_eval, conjugationCoordinatePolynomial_zero,
    sub_zero, ← Basis.equivFun_apply] using h

end Erdos3

end

end OAI
