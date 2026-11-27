import IPRADerivations.Analysis.Stirling.AllOrders.Bernoulli.Mesh.GaussianStirlingAllOrderBernoulliMeshRefinement

/-!
# Full-panel bounds for the actual centered Bernoulli sampler

Reflection and exact refinement place every rational mesh sample between
zero and the common midpoint value. The upper endpoint is independent of
the mesh, including for odd panel subdivisions.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderBernoulliEnvelope

open_ipra
open GaussianStirlingAllOrderCenteredBernoulli
  (sample numerator denominator reflected_sample)
open GaussianStirlingAllOrderBernoulliMeshOrder (sample_monotone sample_nonnegative_first_half)
open GaussianStirlingAllOrderBernoulliMeshRefinement (sample_refinement)
open GaussianEuclideanDistanceName (fraction)
open GaussianRationalHorner (positive_product)
open RationalArgmin (rationalLE rationalLE_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem subst_signed_sum {l d : ℕ} (σ : Fin n → PTm l) (f : Fin d → ZT n) :
    (ZT.sumFin f).subst σ = ZT.sumFin (fun i => (f i).subst σ) := by
  induction d with
  | zero => simp only [ZT.sumFin,ZT.subst_natLit]
  | succ d ih => simp only [ZT.sumFin,ZT.subst_add,ih]

ipra_subst sample [numerator, denominator, BernoulliBounds.pv, BernoulliBounds.zint, subst_signed_sum, pw]

theorem sample_congr (m : ℕ) {p q M N : PTm n} (hp : Γ ⊢[PRAAx] p ≐ q)
    (hM : Γ ⊢[PRAAx] M ≐ N) : Γ ⊢[PRAAx] sample m p M ≐ sample m q N := by
  simpa only [subst_sample,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,Matrix.tail_cons]
    using Prf.eqCongr (Γ := Γ) (sample m (var 0) (var 1) : PTm 2)
      (σ := ![p,M]) (σ' := ![q,N]) (fun i => by fin_cases i; exact hp; exact hM)

/-- The exact upper endpoint attained by the centered profile. -/
def cap (m : ℕ) : PTm n := sample (m+1) one two

ipra_subst cap

theorem cap_nonnegative (m : ℕ) :
    Γ ⊢[PRAAx] rationalLE (fraction zero one) (cap m) :=
  sample_nonnegative_first_half m one two (by ipra_le 1) (by ipra_le 0)

private theorem grid_le_midpoint (m : ℕ) (r M : PTm n) (hM : Γ ⊢[PRAAx] le one M)
    (hr : Γ ⊢[PRAAx] le (two*r) (two*M)) :
    Γ ⊢[PRAAx] rationalLE (fraction zero one) (sample (m+1) r (two*M)) ⋏
      rationalLE (sample (m+1) r (two*M)) (cap m) := by
  have h2M := positive_product two M (by ipra_le 1) hM
  have h : Γ ⊢[PRAAx] le r M := RationalValueBounds.positive_cancel (by ipra_le 1 : Γ ⊢[PRAAx] le one two) hr
  have e : Γ ⊢[PRAAx] sample (m+1) M (two*M) ≐ cap m :=
    (sample_congr (m+1) (by ipra_ring) (by ipra_ring)).eqTrans (sample_refinement (m+1) M one two hM (by ipra_le 1))
  exact .andI (sample_nonnegative_first_half m r (two*M) h2M hr)
    (rationalLE_congr (.eqRefl _) e (sample_monotone m r M (two*M) h2M h (le_refl _)))

theorem sample_envelope (m : ℕ) (p M : PTm n) (hM : Γ ⊢[PRAAx] le one M)
    (hp : Γ ⊢[PRAAx] le p M) :
    Γ ⊢[PRAAx] rationalLE (fraction zero one) (sample (m+1) p M) ⋏
      rationalLE (sample (m+1) p M) (cap m) := by
  have h2 : Γ ⊢[PRAAx] le one (two : PTm n) := by ipra_le 1
  have scaled := sample_refinement (m+1) two p M h2 hM
  have hs : Γ ⊢[PRAAx] le (two*p) (two*M) := by
    have e := natEq (eq_add_of_le hp)
    ipra_le 2*Groth.ι (IPRA.Q.mk Γ (monus M p)) using linear_combination 2*e
  refine .orE (le_total (two*(two*p)) (two*M)) ?_ ?_
  · have h := grid_le_midpoint m (two*p) M hM.wk Prf.hyp0
    exact .andI (rationalLE_congr (.eqRefl _) scaled.wk h.andE₁)
      (rationalLE_congr scaled.wk (.eqRefl _) h.andE₂)
  · let r := monus (two*M) (two*p)
    let Δ := le (two*M) (two*(two*p)) :: Γ
    have e := natEq (eq_add_of_le (hs.wk : Δ ⊢[PRAAx] le (two*p) (two*M)))
    have gap := natEq (eq_add_of_le (Prf.hyp0 : Δ ⊢[PRAAx] le (two*M) (two*(two*p))))
    have hr : Δ ⊢[PRAAx] le (two*r) (two*M) := by
      unfold r
      ipra_le Groth.ι (IPRA.Q.mk Δ (monus (two*(two*p)) (two*M))) using linear_combination 2*e+gap
    have h := grid_le_midpoint m r M hM.wk hr
    have er := (reflected_sample (Γ := Δ) (m+1) (two*p) (two*M)
      (positive_product two M h2.wk hM.wk) hs.wk).eqTrans scaled.wk
    exact .andI (rationalLE_congr (.eqRefl _) er h.andE₁) (rationalLE_congr er (.eqRefl _) h.andE₂)

theorem actual_centered_Bernoulli_full_panel_envelope_closed (m : ℕ) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      ((le one (var 1) ⋏ le (var 0) (var 1)) ⟶
        rationalLE (fraction zero one) (sample (m+1) (var 0) (var 1)) ⋏
          rationalLE (sample (m+1) (var 0) (var 1)) (cap m)) :=
  closeUniv 2 (.impI (sample_envelope m _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderBernoulliEnvelope
