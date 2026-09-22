import Surreal.HahnSeries.MvEvaluation
import Mathlib.RingTheory.MvPowerSeries.Substitution

/-!
# Composition under finite-variable strong Hahn evaluation

This proves the finite-variable composition clause of `a:cor:complexsub`
in the analysis article. Arbitrary outer formal series may be composed with
zero-constant inner series before or after admissible Hahn evaluation.

At every Hahn exponent, the original positive-order arguments admit only
finitely many contributing monomials. At each of those formal multidegrees,
Mathlib's substitution theorem supplies finitely many outer contributions.
These facts justify the coefficient interchange. No native fine-topological
continuity or convergence is assumed.
-/

namespace Surreal.HahnSeries

open _root_.HahnSeries

noncomputable section

variable {Γ R σ τ : Type*} [AddCommMonoid Γ] [LinearOrder Γ]
  [IsOrderedCancelAddMonoid Γ] [CommRing R] [Fintype σ] [Fintype τ]

omit [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] in
private def coefficientRefinement {α β : Type*} (s : SummableFamily Γ R β)
    (c : α → β → R) (hc : ∀ b, (fun a => c a b).HasFiniteSupport) :
    SummableFamily Γ R (α × β) where
  toFun p := c p.1 p.2 • s p.2
  isPWO_iUnion_support' := s.isPWO_iUnion_support.mono <| by
    refine Set.iUnion_subset fun p => ?_
    intro g hg
    exact Set.mem_iUnion.mpr ⟨p.2, support_smul_subset _ _ hg⟩
  finite_co_support' g := by
    apply ((s.finite_co_support g).biUnion
      (fun b _ => (hc b).image (fun a => (a, b)))).subset
    rintro ⟨a, b⟩ hab
    have hb : (s b).coeff g ≠ 0 := by
      intro h
      exact hab (by simp [coeff_smul, h])
    have ha : c a b ≠ 0 := by
      intro h
      exact hab (by simp [h])
    exact Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr ⟨hb, ⟨a, ha, rfl⟩⟩⟩

/-- The entire double family underlying formal substitution and Hahn
evaluation is jointly strongly summable. Finiteness is proved before any
interchange: each Hahn exponent has finitely many inner monomials, each of
which has finitely many outer formal contributions. -/
theorem summable_mv_composition_coefficients (x : τ → R⟦Γ⟧)
    (hx : ∀ i, 0 < (x i).orderTop) (A : MvPowerSeries σ R)
    (B : σ → MvPowerSeries τ R)
    (hB : ∀ i, MvPowerSeries.constantCoeff (B i) = 0) :
    ∃ s : SummableFamily Γ R ((σ →₀ ℕ) × (τ →₀ ℕ)), ∀ e d,
      s (e, d) = (MvPowerSeries.coeff e A *
        MvPowerSeries.coeff d (∏ i, B i ^ e i)) • ∏ i, x i ^ d i := by
  have hsubst := MvPowerSeries.hasSubst_of_constantCoeff_zero hB
  have hc (d : τ →₀ ℕ) : (fun e => MvPowerSeries.coeff e A *
      MvPowerSeries.coeff d (∏ i, B i ^ e i)).HasFiniteSupport := by
    simpa only [smul_eq_mul, Finsupp.prod_pow] using
      MvPowerSeries.coeff_subst_finite hsubst A d
  refine ⟨coefficientRefinement (mvPowerFamily x hx) _ hc, fun e d => ?_⟩
  change (MvPowerSeries.coeff e A * MvPowerSeries.coeff d (∏ i, B i ^ e i)) •
    mvPowerFamily x hx d = _
  rw [mvPowerFamily_apply]

/-- A finite set containing the contributing substituted monomials computes
the coefficient of every formal evaluation at a fixed Hahn exponent. -/
theorem coeff_mvEvaluate_eq_sum (x : τ → R⟦Γ⟧) (hx : ∀ i, 0 < (x i).orderTop)
    (F : MvPowerSeries τ R) (g : Γ) (s : Finset (τ →₀ ℕ))
    (hs : ∀ d ∉ s, (∏ i, x i ^ d i).coeff g = 0) :
    (mvEvaluate x hx F).coeff g =
      ∑ d ∈ s, MvPowerSeries.coeff d F * (∏ i, x i ^ d i).coeff g := by
  rw [coeff_mvEvaluate]
  simp only [single_zero_mul_eq_smul, coeff_smul, smul_eq_mul]
  apply finsum_eq_sum_of_support_subset
  intro d hd
  by_contra hds
  exact hd (by simp only [hs d hds, mul_zero])

/-- The finite-variable composition identity. All inner series have zero
constant coefficient, which proves positive order of their evaluated values;
both the outer and inner series otherwise have arbitrary coefficients. -/
theorem mvEvaluate_subst (x : τ → R⟦Γ⟧) (hx : ∀ i, 0 < (x i).orderTop)
    (A : MvPowerSeries σ R) (B : σ → MvPowerSeries τ R)
    (hB : ∀ i, MvPowerSeries.constantCoeff (B i) = 0) :
    mvEvaluate x hx (MvPowerSeries.subst B A) =
      mvEvaluate (fun i => mvEvaluate x hx (B i))
        (fun i => orderTop_mvEvaluate_pos_of_constantCoeff_zero x hx (B i) (hB i)) A := by
  classical
  apply _root_.HahnSeries.ext
  funext g
  let s := ((mvPowerFamily x hx).finite_co_support g).toFinset
  have hs : ∀ d ∉ s, (∏ i, x i ^ d i).coeff g = 0 := by
    intro d hd
    simpa only [s, Set.Finite.mem_toFinset, Function.mem_support, mvPowerFamily_apply,
      not_not] using hd
  have heval (F : MvPowerSeries τ R) :
      (mvEvaluate x hx F).coeff g =
        ∑ d ∈ s, MvPowerSeries.coeff d F * (∏ i, x i ^ d i).coeff g :=
    coeff_mvEvaluate_eq_sum x hx F g s hs
  have hsubst : MvPowerSeries.HasSubst B :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero hB
  have hprod (d : σ →₀ ℕ) : d.prod (fun i n => B i ^ n) = ∏ i, B i ^ d i :=
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)
  have hfinite (d : τ →₀ ℕ) :
      (fun e => MvPowerSeries.coeff e A *
        MvPowerSeries.coeff d (∏ i, B i ^ e i)).HasFiniteSupport := by
    simpa only [smul_eq_mul, hprod] using MvPowerSeries.coeff_subst_finite hsubst A d
  have hfinite_mul (d : τ →₀ ℕ) :
      (fun e => (MvPowerSeries.coeff e A *
        MvPowerSeries.coeff d (∏ i, B i ^ e i)) *
          (∏ i, x i ^ d i).coeff g).HasFiniteSupport :=
    (hfinite d).mul_left (fun _ => (∏ i, x i ^ d i).coeff g)
  calc
    (mvEvaluate x hx (MvPowerSeries.subst B A)).coeff g =
        ∑ d ∈ s, (∑ᶠ e, MvPowerSeries.coeff e A *
          MvPowerSeries.coeff d (∏ i, B i ^ e i)) *
            (∏ i, x i ^ d i).coeff g := by
      rw [heval]
      simp only [MvPowerSeries.coeff_subst hsubst, smul_eq_mul, hprod]
    _ = ∑ d ∈ s, ∑ᶠ e, (MvPowerSeries.coeff e A *
        MvPowerSeries.coeff d (∏ i, B i ^ e i)) * (∏ i, x i ^ d i).coeff g := by
      apply Finset.sum_congr rfl
      intro d _
      exact finsum_mul' _ _ (hfinite d)
    _ = ∑ᶠ e, ∑ d ∈ s, (MvPowerSeries.coeff e A *
        MvPowerSeries.coeff d (∏ i, B i ^ e i)) * (∏ i, x i ^ d i).coeff g :=
      sum_finsum_comm s _ (fun d _ => hfinite_mul d)
    _ = ∑ᶠ e, MvPowerSeries.coeff e A *
        (∏ i, mvEvaluate x hx (B i) ^ e i).coeff g := by
      apply finsum_congr
      intro e
      simp only [mul_assoc, ← Finset.mul_sum, ← heval, map_prod, map_pow]
    _ = (mvEvaluate (fun i => mvEvaluate x hx (B i))
        (fun i => orderTop_mvEvaluate_pos_of_constantCoeff_zero x hx (B i) (hB i)) A).coeff g := by
      rw [coeff_mvEvaluate]
      simp only [single_zero_mul_eq_smul, coeff_smul, smul_eq_mul]

end

end Surreal.HahnSeries
