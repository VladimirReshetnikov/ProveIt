import OAI.Combinatorics.Progressions.Estimates.RationalLieSubalgebra

namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem exists_quotient_presentation_exp_height {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    (A : Matrix ι κ ℚ) {H : ℕ} (hHpos : 1 ≤ H)
    (hA : ∀ i j, RationalHeightLE (A i j) H)
    {p : ℝ} (hp : 0 ≤ p) (hrows : (Fintype.card ι : ℝ) ≤ p)
    (hcols : (Fintype.card κ : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    ∃ d : ℕ, d ≤ Fintype.card ι ∧
      ∃ D : Matrix (Fin d) ι ℚ, ∃ S : Matrix ι (Fin d) ℚ,
        LinearMap.ker D.mulVecLin = LinearMap.range A.mulVecLin ∧ D * S = 1 ∧
        (∀ i j, ((D i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 7) ∧
          ((D i j).den : ℝ) ≤ Real.exp ((p + 2) ^ 7)) ∧
        ∀ i j, ((S i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 45) ∧
          ((S i j).den : ℝ) ≤ Real.exp ((p + 2) ^ 45) := by
  obtain ⟨t, ht, d, hd, D, S, hker, hDS, hD, hS⟩ :=
    exists_bounded_quotient_presentation A hHpos hA
  have htp : (t : ℝ) ≤ p :=
    (show (t : ℝ) ≤ Fintype.card κ from by exact_mod_cast ht).trans hcols
  have hdp : (d : ℝ) ≤ p :=
    (show (d : ℝ) ≤ Fintype.card ι from by exact_mod_cast hd).trans hrows
  have hK := rationalKernelHeight_le_budget t H hp htp hH
  have hSbudget : (rationalSolveHeight d (rationalKernelHeight t H) : ℝ) ≤
      Real.exp ((p + 2) ^ 45) := by
    have hb := rationalSolveHeight_le_budget d (rationalKernelHeight t H)
      (by positivity : 0 ≤ (p + 2) ^ 7)
      (hdp.trans (le_power_budget hp (by decide : 1 ≤ 7))) hK
    exact exponential_budget_comp hp (by positivity) 7 5 le_rfl hb
  refine ⟨d, hd, D, S, hker, hDS, ?_, ?_⟩
  · intro i j
    constructor
    · exact (show ((D i j).num.natAbs : ℝ) ≤ rationalKernelHeight t H from
        by exact_mod_cast (hD i j).1).trans hK
    · exact (show ((D i j).den : ℝ) ≤ rationalKernelHeight t H from
        by exact_mod_cast (hD i j).2).trans hK
  · intro i j
    constructor
    · exact (show ((S i j).num.natAbs : ℝ) ≤ rationalSolveHeight d (rationalKernelHeight t H) from
        by exact_mod_cast (hS i j).1).trans hSbudget
    · exact (show ((S i j).den : ℝ) ≤ rationalSolveHeight d (rationalKernelHeight t H) from
        by exact_mod_cast (hS i j).2).trans hSbudget

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix

theorem rationalQuotientSectionHeight_le_exp (t d H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (ht : (t : ℝ) ≤ p) (hd : (d : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (rationalSolveHeight d (rationalKernelHeight t H) : ℝ) ≤ Real.exp ((p + 2) ^ 45) := by
  have hK := rationalKernelHeight_le_budget t H hp ht hH
  have hS := rationalSolveHeight_le_budget d (rationalKernelHeight t H)
    (by positivity : 0 ≤ (p + 2) ^ 7)
    (hd.trans (le_power_budget hp (by decide : 1 ≤ 7))) hK
  exact exponential_budget_comp hp (by positivity) 7 5 le_rfl hS

theorem rationalLieQuotientStructureHeight_le_exp (n t d H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (ht : (t : ℝ) ≤ p) (hd : (d : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) :
    (rationalLieStructureHeight n
      (max H (max (rationalKernelHeight t H)
        (rationalSolveHeight d (rationalKernelHeight t H)))) : ℝ) ≤
      Real.exp ((p + 2) ^ 51) := by
  apply rationalLieStructureHeight_le_exp n _ hp hn 45
  simp only [Nat.cast_max, max_le_iff]
  refine ⟨hH.trans (Real.exp_le_exp.mpr (le_power_budget hp (by decide))), ?_,
    rationalQuotientSectionHeight_le_exp t d H hp ht hd hH⟩
  exact (rationalKernelHeight_le_budget t H hp ht hH).trans
    (Real.exp_le_exp.mpr (pow_le_pow_right₀ (by linarith : 1 ≤ p + 2) (by decide : 7 ≤ 45)))

variable {ι η L : Type*} [Fintype ι] [DecidableEq ι] [Fintype η] [LieRing L] [LieAlgebra ℚ L]

theorem exists_lie_quotient_basis_exp_height (e : Basis ι ℚ L) (I : LieIdeal ℚ L)
    (v : η → L) (hspan : Submodule.span ℚ (Set.range v) = I.toSubmodule)
    {H : ℕ} (hHpos : 1 ≤ H) (hv : ∀ i j, RationalHeightLE (e.repr (v j) i) H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)
    {p : ℝ} (hp : 0 ≤ p) (hn : (Fintype.card ι : ℝ) ≤ p)
    (hm : (Fintype.card η : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    ∃ d : ℕ, d ≤ Fintype.card ι ∧ ∃ b : Basis (Fin d) ℚ (L ⧸ I),
      ∃ D : Matrix (Fin d) ι ℚ, ∃ S : Matrix ι (Fin d) ℚ,
        LinearMap.toMatrix e b (lieQuotientMap I).toLinearMap = D ∧ D * S = 1 ∧
        (∀ i j, ((D i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 7) ∧
          ((D i j).den : ℝ) ≤ Real.exp ((p + 2) ^ 7)) ∧
        (∀ i j, ((S i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 45) ∧
          ((S i j).den : ℝ) ≤ Real.exp ((p + 2) ^ 45)) ∧
        ∀ i j k, ((lieStructureConstants b i j k).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 51) ∧
          ((lieStructureConstants b i j k).den : ℝ) ≤ Real.exp ((p + 2) ^ 51) := by
  classical
  obtain ⟨t, ht, d, hd, b, D, S, hmatrix, hDS, hD, hS, hbracket⟩ :=
    exists_bounded_lie_quotient_with_structure e I v hspan hHpos hv hc
  have htp : (t : ℝ) ≤ p := (Nat.cast_le.mpr ht).trans hm
  have hdp : (d : ℝ) ≤ p := (Nat.cast_le.mpr hd).trans hn
  have hK := rationalKernelHeight_le_budget t H hp htp hH
  have hJ := rationalQuotientSectionHeight_le_exp t d H hp htp hdp hH
  have hC := rationalLieQuotientStructureHeight_le_exp (Fintype.card ι) t d H hp hn htp hdp hH
  refine ⟨d, hd, b, D, S, hmatrix, hDS, ?_, ?_, ?_⟩
  · intro i j
    exact ⟨(Nat.cast_le.mpr (hD i j).1).trans hK, (Nat.cast_le.mpr (hD i j).2).trans hK⟩
  · intro i j
    exact ⟨(Nat.cast_le.mpr (hS i j).1).trans hJ, (Nat.cast_le.mpr (hS i j).2).trans hJ⟩
  · intro i j k
    exact ⟨(Nat.cast_le.mpr (hbracket i j k).1).trans hC,
      (Nat.cast_le.mpr (hbracket i j k).2).trans hC⟩

end Erdos3

end

end OAI
