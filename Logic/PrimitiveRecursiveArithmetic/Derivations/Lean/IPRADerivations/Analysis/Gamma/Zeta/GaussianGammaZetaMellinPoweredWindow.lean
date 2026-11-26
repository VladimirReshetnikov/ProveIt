import IPRADerivations.Analysis.Gamma.Zeta.GaussianGammaZetaMellinDampedWindowSchedule

/-!
# A powered left endpoint for the shared Mellin window

Choose both endpoints of the shared window from one later powered
Euler cutoff. The original nested cutoff split then applies exactly. The root degree and Gamma half-plane margin are
independent parameters.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinPoweredWindow

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaIntegralCutoffs (etaDen eta_den_positive height top)
open GaussianGammaZetaMellinDampedWindow (cutoff source rowSource clock)
open GaussianGammaZetaMellinDampedWindowSchedule (gainBudget mesh mesh_positive
  gain_le_budget grid_le_mesh)
open GaussianRationalHorner (positive_product)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "baseDen" => GaussianGammaZetaMellinDampedWindowSchedule.leftDen

def outerCutoff (i N k A R J S : PTm n) : PTm n := succ i+baseDen N k A R (etaDen i J S)+top k A R

def denominator (i N k A R J S : PTm n) : PTm n := etaDen (outerCutoff i N k A R J S) J S

private theorem subst_etaDen {m : ℕ} (σ : Fin n → PTm m) (p A R : PTm n) :
    Syn.subst σ (etaDen p A R) = etaDen (Syn.subst σ p) (Syn.subst σ A) (Syn.subst σ R) := by
  simp [etaDen,height,GaussianGammaIntegralCutoffs.tailCoefficient]

private theorem subst_baseDen {m : ℕ} (σ : Fin n → PTm m) (N k A R E₀ : PTm n) :
    Syn.subst σ (baseDen N k A R E₀) =
      baseDen (Syn.subst σ N) (Syn.subst σ k) (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ E₀) := by
  simp [GaussianGammaZetaMellinDampedWindowSchedule.leftDen,subst_etaDen,one]

private theorem subst_top {m : ℕ} (σ : Fin n → PTm m) (k A R : PTm n) :
    Syn.subst σ (top k A R) = top (Syn.subst σ k) (Syn.subst σ A) (Syn.subst σ R) := by
  simp [top,height,GaussianGammaIntegralCutoffs.tailCoefficient]

@[simp] theorem subst_outerCutoff {m : ℕ} (σ : Fin n → PTm m) (i N k A R J S : PTm n) :
    Syn.subst σ (outerCutoff i N k A R J S) = outerCutoff (Syn.subst σ i) (Syn.subst σ N) (Syn.subst σ k)
      (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ J) (Syn.subst σ S) := by
  simp [outerCutoff,subst_baseDen,subst_etaDen,subst_top]

@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (i N k A R J S : PTm n) :
    Syn.subst σ (denominator i N k A R J S) =
      denominator (Syn.subst σ i) (Syn.subst σ N) (Syn.subst σ k) (Syn.subst σ A)
        (Syn.subst σ R) (Syn.subst σ J) (Syn.subst σ S) := by
  simp [denominator,subst_etaDen]

theorem later_cutoff (i N k A R J S : PTm n) :
    Γ ⊢[PRAAx] lt i (outerCutoff i N k A R J S) := le_trans (le_add_right _ _) (le_add_right _ _)

theorem denominator_dominates (i N k A R J S : PTm n) (hJ : Γ ⊢[PRAAx] le one J) :
    Γ ⊢[PRAAx] le (baseDen N k A R (etaDen i J S)) (denominator i N k A R J S) := by
  let b := baseDen N k A R (etaDen i J S)
  let q := outerCutoff i N k A R J S
  let h := height q J S
  have bq : Γ ⊢[PRAAx] le b q := le_trans (le_add_left _ _) (le_add_right _ _)
  have qh : Γ ⊢[PRAAx] le q h := le_trans (le_add_right _ _) (le_trans (le_add_right _ _) (le_add_right _ _))
  have hp : Γ ⊢[PRAAx] le h (J*h) := le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right h hJ)
  have pow : Γ ⊢[PRAAx] le (J*h) (unit (J*h)) :=
    le_trans (le_succ_self _) (RationalClosure.succ_le_two_pow (J*h))
  exact le_trans bq (le_trans qh (le_trans hp pow))

private theorem row_encloses (z R B A k N c i J S : PTm n)
    (hz : Γ ⊢[PRAAx] GaussianEulerIntegralGammaIdentification.source z R B A)
    (hc : Γ ⊢[PRAAx] le one c) (hcN : Γ ⊢[PRAAx] le c N) (hJ : Γ ⊢[PRAAx] le one J) :
    let q := outerCutoff i N k A R J S
    let E := denominator i N k A R J S
    let H := top q J S
    Γ ⊢[PRAAx] GaussianGammaZetaMellinDampedExhaustion.source z R B A k c one
      (GaussianGammaCompactQuadratureBoundary.width q J S) E (N*H) := by
  intro q E H
  let W := GaussianGammaCompactQuadratureBoundary.width q J S
  let E₀ := etaDen i J S
  have original := GaussianGammaZetaMellinDampedWindowSchedule.row_encloses z R B A k N c E₀ zero hz hc hcN
    (eta_den_positive i J S)
  have eft : Γ ⊢[PRAAx] le ((c*one)*etaDen k A R) E :=
    le_trans original.andE₁.andE₂.andE₂.andE₁ (denominator_dominates i N k A R J S hJ)
  have hE : Γ ⊢[PRAAx] le one E := eta_den_positive _ _ _
  have hTop : Γ ⊢[PRAAx] le (top k A R) H := by
    have hq : Γ ⊢[PRAAx] le (top k A R) q := le_add_left _ _
    have qh : Γ ⊢[PRAAx] le q (height q J S) :=
      le_trans (le_add_right _ _) (le_trans (le_add_right _ _) (le_add_right _ _))
    have doubled : Γ ⊢[PRAAx] le (height q J S) H :=
      le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right _ (le_succ_self one))
    exact le_trans hq (le_trans qh doubled)
  have ep : Γ ⊢[PRAAx] one+W ≐ H*E :=
    (GaussianGammaCompactQuadratureBoundary.exact_right_endpoint q J S).eqTrans (mul_comm _ _)
  have info := (GaussianEulerIntegralGammaIdentification.improper_source z R B A hz).andE₁
  have param : Γ ⊢[PRAAx] GaussianEulerExponentCompactBounds.source z R B E :=
    .andI info.andE₁ (.andI hE info.andE₂)
  have lo : Γ ⊢[PRAAx] le one (c*one) :=
    le_congr (.eqRefl _) (by ipra_ring) hc
  have loE : Γ ⊢[PRAAx] le E (E*(c*one)) :=
    le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right E hc)
  have ec : Γ ⊢[PRAAx] c*one+c*W ≐ c*(H*E) :=
    (by ipra_ring : Γ ⊢[PRAAx] c*one+c*W ≐ c*(one+W)).eqTrans (congrMul (.eqRefl _) ep)
  have up : Γ ⊢[PRAAx] le (c*one+c*W) ((N*H)*E) :=
    le_congr ec.eqSymm (by ipra_ring) (mul_le_mul_right (H*E) hcN)
  have low : Γ ⊢[PRAAx] le (top k A R*E) (c*one+c*W) :=
    le_congr (.eqRefl _) ec.eqSymm
      (le_trans (mul_le_mul_right E hTop)
        (le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right (H*E) hc)))
  exact .andI (.andI hz (.andI (.andI param (.andI (.andI lo hE) (.andI loE up))) (.andI eft low)))
    (.andI hc (le_refl one))

theorem shared_source (p i N z R B A J S M : PTm n)
    (hz : Γ ⊢[PRAAx] GaussianEulerIntegralGammaIdentification.source z R B A) (hJ : Γ ⊢[PRAAx] le one J) :
    let G := gainBudget N z R B A
    let k := cutoff p N G
    let q := outerCutoff i N k A R J S
    let E := denominator i N k A R J S
    let T := N*top q J S
    (Γ ⊢[PRAAx] le (mesh p N R E T) M) → (Γ ⊢[PRAAx] source N p z R B A one
      (GaussianGammaCompactQuadratureBoundary.width q J S) E T G M) := by
  intro G k q E T hm
  refine .allI (.impI ?_)
  let sh (u : PTm n) := Syn.shift u
  let Δ := lt (var 0) (sh N) :: Γ.map Fm.shift
  let j : PTm (n+1) := var 0
  have hi : Δ ⊢[PRAAx] lt j (sh N) := Prf.hyp0
  have hγ : Δ ⊢[PRAAx] GaussianEulerIntegralGammaIdentification.source (sh z) (sh R) (sh B) (sh A) := by
    simpa only [Fm.shift,GaussianEulerIntegralGammaIdentification.subst_source,Syn.shift,sh,Δ] using hz.shift.wk
  have hJ' : Δ ⊢[PRAAx] le one (sh J) := by
    simpa only [Fm.shift,subst_le,Syn.shift,sh,Δ,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using hJ.shift.wk
  let g := gainBudget (sh N) (sh z) (sh R) (sh B) (sh A)
  let t := cutoff (sh p) (sh N) g
  let e := denominator (sh i) (sh N) t (sh A) (sh R) (sh J) (sh S)
  let q' := outerCutoff (sh i) (sh N) t (sh A) (sh R) (sh J) (sh S)
  let v := sh N*top q' (sh J) (sh S)
  have hm' : Δ ⊢[PRAAx] le (mesh (sh p) (sh N) (sh R) e v) (sh M) := by
    simpa only [G,k,E,T,q,g,t,e,q',v,Δ,sh,Fm.shift,Syn.shift,subst_le,subst_top,subst_outerCutoff,
      subst_denominator,GaussianGammaZetaMellinDampedWindowSchedule.subst_gainBudget,
      GaussianGammaZetaMellinDampedWindowSchedule.subst_mesh,GaussianFastValueCut.subst_exponent,cutoff,PTm.subst_mul]
      using hm.shift.wk
  have hh : Δ ⊢[PRAAx] rowSource (sh N) (sh p) (sh z) (sh R) (sh B) (sh A)
      one (GaussianGammaCompactQuadratureBoundary.width q' (sh J) (sh S)) e v g (sh M) j :=
    .andI (row_encloses (sh z) (sh R) (sh B) (sh A) t (sh N) (succ j) (sh i) (sh J) (sh S)
      hγ (zero_lt_succ j) hi hJ')
      (.andI (gain_le_budget (sh N) (sh z) (sh R) (sh B) (sh A) j hi)
        (le_trans (grid_le_mesh (sh p) (sh N) (sh R) e v j hi) hm'))
  simpa only [G,k,E,T,q,g,t,e,q',v,j,Δ,sh,Syn.shift,GaussianGammaZetaMellinDampedWindowSchedule.subst_gainBudget,
    subst_denominator,subst_top,subst_outerCutoff,GaussianGammaCompactQuadratureBoundary.subst_width,
    GaussianFastValueCut.subst_exponent,cutoff,PTm.subst_mul,one,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using hh

theorem scheduled_product_error (p s r i N z R B A J S M : PTm n)
    (hz : Γ ⊢[PRAAx] GaussianEulerIntegralGammaIdentification.source z R B A) (hJ : Γ ⊢[PRAAx] le one J) :
    let G := gainBudget N z R B A
    let k := cutoff p N G
    let q := outerCutoff i N k A R J S
    let E := denominator i N k A R J S
    let T := N*top q J S
    let u := unit p
    let v := unit r
    (Γ ⊢[PRAAx] le (mesh p N R E T) M) → (Γ ⊢[PRAAx] le (clock p N T) s) →
    (Γ ⊢[PRAAx] GaussianRationalMetric.distanceBounded
      (GaussianGammaZetaMellinDampedStrip.dampedValue s z B M N one (GaussianGammaCompactQuadratureBoundary.width q J S) E)
      (ap2 GaussianGammaZetaMellinDampedImproper.gammaProductF r (GaussianGammaZetaMellinDampedImproper.gammaProductData N z R B A))
      (num 9*(u*v)+(u+v)*u) (u*(u*v))) := by
  intro G k q E T u v hm hs
  exact GaussianGammaZetaMellinDampedWindow.finite_gamma_dirichlet_error_at p s r N z R B A one _ _ _ _ M
    (shared_source p i N z R B A J S M hz hJ hm) (le_trans (mesh_positive _ _ _ _ _) hm) hs hz

end LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinPoweredWindow
