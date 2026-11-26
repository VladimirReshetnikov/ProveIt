import IPRADerivations.Analysis.Gamma.Zeta.Mellin.Damped.GaussianGammaZetaMellinDampedWindow

/-!
# A shared enclosing window after the finite Mellin count

Bound the finite row gains first. Choose the Euler cutoff, then enlarge
the time window to enclose its image at every admitted scale. The common
grid count is a second finite natural sum, depending only on this window.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinDampedWindowSchedule

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaIntegralCutoffs (etaDen top eta_den_positive top_positive)
open GaussianGammaZetaMellinDampedExhaustion (gain gridCount)
open GaussianGammaZetaMellinDampedWindow (cutoff rowClock clock rowSource source)
open GaussianRationalHorner (positive_product)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private def gainParameters (z R B A : PTm n) : PTm n := pairT (pairT z R) (pairT B A)
private def gainBody : PTm 2 :=
  let x := var 1
  gain (fstT (fstT x)) (sndT (fstT x)) (fstT (sndT x)) (sndT (sndT x)) (succ (var 0))

def gainBudget (N z R B A : PTm n) : PTm n :=
  ap2 (LeanProofs.IPRA.sumF gainBody) N (gainParameters z R B A)

private theorem subst_gain {m : ℕ} (σ : Fin n → PTm m) (z R B A c : PTm n) :
    Syn.subst σ (gain z R B A c) =
    gain (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ A) (Syn.subst σ c) := by
  simp [gain,GaussianEulerCompactExhaustion.budget,GaussianEulerPositiveScalingConstant.inverseBound,one]

private theorem gain_at (i z R B A : PTm n) :
    Γ ⊢[PRAAx] inst2 gainBody i (gainParameters z R B A) ≐ gain z R B A (succ i) := by
  let x := gainParameters z R B A
  let t : PTm 5 := gain (var 1) (var 2) (var 3) (var 4) (succ (var 0))
  have l := fst_pair (Γ := Γ) (pairT z R) (pairT B A)
  have r := snd_pair (Γ := Γ) (pairT z R) (pairT B A)
  have e := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) t
    (σ := ![i,fstT (fstT x),sndT (fstT x),fstT (sndT x),sndT (sndT x)]) (σ' := ![i,z,R,B,A])
    (fun j => by fin_cases j
                 · exact .eqRefl i
                 · exact (congrFst l).eqTrans (fst_pair z R)
                 · exact (congrSnd l).eqTrans (snd_pair z R)
                 · exact (congrFst r).eqTrans (fst_pair B A)
                 · exact (congrSnd r).eqTrans (snd_pair B A))
  simpa only [t,inst2,gainBody,subst_gain,subst_fstT,subst_sndT,ConciseIPRA.PTm.subst_succ,
    Syn.subst_var,Matrix.cons_val,x] using e

theorem gain_le_budget (N z R B A i : PTm n) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] le (gain z R B A (succ i)) (gainBudget N z R B A) :=
  le_congr (gain_at i z R B A) (.eqRefl _) (term_le_sum gainBody (x := gainParameters z R B A) hi)

private def gridParameters (s R E T : PTm n) : PTm n := pairT (pairT s R) (pairT E T)
private def gridBody : PTm 2 :=
  let x := var 1
  gridCount (fstT (fstT x)) (sndT (fstT x)) (succ (var 0)) (fstT (sndT x)) (sndT (sndT x))

def mesh (p N R E T : PTm n) : PTm n :=
  one+ap2 (LeanProofs.IPRA.sumF gridBody) N (gridParameters (rowClock p N) R E T)

private theorem subst_gridCount {m : ℕ} (σ : Fin n → PTm m) (s R c E T : PTm n) :
    Syn.subst σ (gridCount s R c E T) =
    gridCount (Syn.subst σ s) (Syn.subst σ R) (Syn.subst σ c) (Syn.subst σ E) (Syn.subst σ T) := by
  simp [gridCount,one]

private theorem grid_at (i s R E T : PTm n) :
    Γ ⊢[PRAAx] inst2 gridBody i (gridParameters s R E T) ≐ gridCount s R (succ i) E T := by
  let x := gridParameters s R E T
  let t : PTm 5 := gridCount (var 1) (var 2) (succ (var 0)) (var 3) (var 4)
  have l := fst_pair (Γ := Γ) (pairT s R) (pairT E T)
  have r := snd_pair (Γ := Γ) (pairT s R) (pairT E T)
  have e := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) t
    (σ := ![i,fstT (fstT x),sndT (fstT x),fstT (sndT x),sndT (sndT x)]) (σ' := ![i,s,R,E,T])
    (fun j => by fin_cases j
                 · exact .eqRefl i
                 · exact (congrFst l).eqTrans (fst_pair s R)
                 · exact (congrSnd l).eqTrans (snd_pair s R)
                 · exact (congrFst r).eqTrans (fst_pair E T)
                 · exact (congrSnd r).eqTrans (snd_pair E T))
  simpa only [t,inst2,gridBody,subst_gridCount,subst_fstT,subst_sndT,ConciseIPRA.PTm.subst_succ,
    Syn.subst_var,Matrix.cons_val,x] using e

theorem mesh_positive (p N R E T : PTm n) : Γ ⊢[PRAAx] le one (mesh p N R E T) :=
  le_add_right _ _

theorem grid_le_mesh (p N R E T i : PTm n) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] le (gridCount (rowClock p N) R (succ i) E T) (mesh p N R E T) :=
  le_trans (le_congr (grid_at i (rowClock p N) R E T) (.eqRefl _)
    (term_le_sum gridBody (x := gridParameters (rowClock p N) R E T) hi)) (le_add_left _ _)

def leftDen (N k A R E₀ : PTm n) : PTm n := (one+N*etaDen k A R)*E₀
def upper (k A R T₀ : PTm n) : PTm n := top k A R+T₀
def width (E H : PTm n) : PTm n := monus (H*E) one

theorem left_den_lower (N k A R E₀ : PTm n) : Γ ⊢[PRAAx] le E₀ (leftDen N k A R E₀) :=
  le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right E₀ (le_add_right one _))

theorem upper_positive (k A R T₀ : PTm n) : Γ ⊢[PRAAx] le one (upper k A R T₀) :=
  le_trans (top_positive k A R) (le_add_right _ _)

theorem right_exact (E H : PTm n) (hE : Γ ⊢[PRAAx] le one E) (hH : Γ ⊢[PRAAx] le one H) :
    Γ ⊢[PRAAx] one+width E H ≐ H*E :=
  (eq_add_of_le (positive_product _ _ hH hE)).eqSymm

/-- The original wider window covers any admitted interval with denominator
E₀ and integer upper cap T₀. -/
theorem contains_panel (N k A R a₀ C₀ E₀ T₀ : PTm n) (ha : Γ ⊢[PRAAx] le one a₀)
    (h₀ : Γ ⊢[PRAAx] le (a₀+C₀) (T₀*E₀)) :
    Γ ⊢[PRAAx] le E₀ (a₀*leftDen N k A R E₀) ⋏ le (a₀+C₀) (upper k A R T₀*E₀) := by
  have start := le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right (leftDen N k A R E₀) ha)
  exact .andI (le_trans (left_den_lower N k A R E₀) start)
    (le_trans h₀ (mul_le_mul_right E₀ (le_add_left _ _)))

theorem row_encloses (z R B A k N c E₀ T₀ : PTm n)
    (hz : Γ ⊢[PRAAx] GaussianEulerIntegralGammaIdentification.source z R B A)
    (hc : Γ ⊢[PRAAx] le one c) (hcN : Γ ⊢[PRAAx] le c N) (hE₀ : Γ ⊢[PRAAx] le one E₀) :
    Γ ⊢[PRAAx] GaussianGammaZetaMellinDampedExhaustion.source z R B A k c one
      (width (leftDen N k A R E₀) (upper k A R T₀)) (leftDen N k A R E₀) (N*upper k A R T₀) := by
  let E := leftDen N k A R E₀
  let H := upper k A R T₀
  let W := width E H
  let L := etaDen k A R
  let K := top k A R
  have hE : Γ ⊢[PRAAx] le one E := le_trans hE₀ (left_den_lower N k A R E₀)
  have hH : Γ ⊢[PRAAx] le one H := upper_positive k A R T₀
  have widthEq := right_exact E H hE hH
  have info := (GaussianEulerIntegralGammaIdentification.improper_source z R B A hz).andE₁
  have param : Γ ⊢[PRAAx] GaussianEulerExponentCompactBounds.source z R B E :=
    .andI info.andE₁ (.andI hE info.andE₂)
  have cOne : Γ ⊢[PRAAx] c*one ≐ c := by ipra_ring
  have lowerNum := le_congr (.eqRefl _) cOne.eqSymm hc
  have aApprox : Γ ⊢[PRAAx] le E (E*(c*one)) :=
    le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right E hc)
  have leftCap := le_trans (mul_le_mul_right L hcN) (le_add_left (N*L) one)
  have enlarge : Γ ⊢[PRAAx] le (one+N*L) E :=
    le_congr (one_mul (one+N*L)) (mul_comm E₀ (one+N*L))
      (mul_le_mul_right (one+N*L) hE₀)
  have left : Γ ⊢[PRAAx] le ((c*one)*L) E :=
    le_congr (by ipra_ring) (.eqRefl _) (le_trans leftCap enlarge)
  have endEq : Γ ⊢[PRAAx] c*one+c*W ≐ c*(H*E) :=
    (by ipra_ring : Γ ⊢[PRAAx] c*one+c*W ≐ c*(one+W)).eqTrans (congrMul (.eqRefl c) widthEq)
  have useCap : Γ ⊢[PRAAx] le (K*E) (H*E) := mul_le_mul_right E (le_add_right K T₀)
  have rise : Γ ⊢[PRAAx] le (H*E) (c*(H*E)) :=
    le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right (H*E) hc)
  have right : Γ ⊢[PRAAx] le (K*E) (c*one+c*W) :=
    le_congr (.eqRefl _) endEq.eqSymm (le_trans useCap rise)
  have upperBound : Γ ⊢[PRAAx] le (c*one+c*W) ((N*H)*E) :=
    le_congr endEq.eqSymm (by ipra_ring) (mul_le_mul_right (H*E) hcN)
  exact .andI (.andI hz (.andI (.andI param (.andI (.andI lowerNum hE) (.andI aApprox upperBound)))
    (.andI left right))) (.andI hc (le_refl one))

@[simp] theorem subst_gainBudget {m : ℕ} (σ : Fin n → PTm m) (N z R B A : PTm n) :
    Syn.subst σ (gainBudget N z R B A) =
      gainBudget (Syn.subst σ N) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ A) := by
  simp [gainBudget,gainParameters]

@[simp] theorem subst_mesh {m : ℕ} (σ : Fin n → PTm m) (p N R E T : PTm n) :
    Syn.subst σ (mesh p N R E T) =
      mesh (Syn.subst σ p) (Syn.subst σ N) (Syn.subst σ R) (Syn.subst σ E) (Syn.subst σ T) := by
  simp [mesh,gridParameters,rowClock,one]

private theorem subst_leftDen {m : ℕ} (σ : Fin n → PTm m) (N k A R E₀ : PTm n) :
    Syn.subst σ (leftDen N k A R E₀) =
      leftDen (Syn.subst σ N) (Syn.subst σ k) (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ E₀) := by
  simp [leftDen,etaDen,GaussianGammaIntegralCutoffs.height,GaussianGammaIntegralCutoffs.tailCoefficient,one]

private theorem subst_upper {m : ℕ} (σ : Fin n → PTm m) (k A R T₀ : PTm n) :
    Syn.subst σ (upper k A R T₀) =
      upper (Syn.subst σ k) (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ T₀) := by
  simp [upper,top,GaussianGammaIntegralCutoffs.height,GaussianGammaIntegralCutoffs.tailCoefficient,one]

/-- Simultaneous certificate for every row on one shared enlarged panel. -/
theorem shared_source (p N z R B A E₀ T₀ : PTm n)
    (hz : Γ ⊢[PRAAx] GaussianEulerIntegralGammaIdentification.source z R B A)
    (hE₀ : Γ ⊢[PRAAx] le one E₀) :
    let G := gainBudget N z R B A
    let k := cutoff p N G
    let E := leftDen N k A R E₀
    let H := upper k A R T₀
    let T := N*H
    Γ ⊢[PRAAx] source N p z R B A one (width E H) E T G (mesh p N R E T) := by
  intro G k E H T
  refine .allI (.impI ?_)
  let sh (x : PTm n) := Syn.shift x
  let Δ := lt (var 0) (sh N) :: Γ.map Fm.shift
  let j : PTm (n+1) := var 0
  have hi : Δ ⊢[PRAAx] lt j (sh N) := Prf.hyp0
  have hγ : Δ ⊢[PRAAx] GaussianEulerIntegralGammaIdentification.source (sh z) (sh R) (sh B) (sh A) := by
    simpa only [Fm.shift,GaussianEulerIntegralGammaIdentification.subst_source,Syn.shift,sh,Δ] using hz.shift.wk
  have hE : Δ ⊢[PRAAx] le one (sh E₀) := by
    simpa only [Fm.shift,subst_le,Syn.shift,sh,Δ,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using hE₀.shift.wk
  let g := gainBudget (sh N) (sh z) (sh R) (sh B) (sh A)
  let s := cutoff (sh p) (sh N) g
  let e := leftDen (sh N) s (sh A) (sh R) (sh E₀)
  let h := upper s (sh A) (sh R) (sh T₀)
  let t := sh N*h
  have hrow : Δ ⊢[PRAAx] rowSource (sh N) (sh p) (sh z) (sh R) (sh B) (sh A)
      one (width e h) e t g (mesh (sh p) (sh N) (sh R) e t) j :=
    .andI (row_encloses (sh z) (sh R) (sh B) (sh A) s (sh N) (succ j) (sh E₀) (sh T₀)
      hγ (zero_lt_succ j) hi hE)
      (.andI (gain_le_budget (sh N) (sh z) (sh R) (sh B) (sh A) j hi)
        (grid_le_mesh (sh p) (sh N) (sh R) e t j hi))
  simpa only [G,k,E,H,T,g,s,e,h,t,j,Δ,sh,Syn.shift,subst_gainBudget,subst_mesh,subst_leftDen,subst_upper,
    GaussianFastValueCut.subst_exponent,cutoff,width,PTm.subst_monus,PTm.subst_mul,
    one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using hrow

/-- The widened panel also supplies a valid original Mellin strip window. -/
theorem strip_window (N k A R E₀ T₀ : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hE₀ : Γ ⊢[PRAAx] le one E₀) :
    let E := leftDen N k A R E₀
    let H := upper k A R T₀
    Γ ⊢[PRAAx] GaussianGammaZetaMellinStrip.window one (width E H) E E (N*H) := by
  intro E H
  have hE : Γ ⊢[PRAAx] le one E := le_trans hE₀ (left_den_lower N k A R E₀)
  have hH : Γ ⊢[PRAAx] le one H := upper_positive k A R T₀
  exact .andI (.andI (le_refl one) hE)
    (.andI (le_congr (.eqRefl _) (by ipra_ring) (le_refl E))
      (le_congr (right_exact E H hE hH).eqSymm (by ipra_ring)
        (mul_le_mul_right (H*E) hN |> le_congr (one_mul _) (.eqRefl _))))

/-- Completely scheduled shared-window estimate for the genuine finite product. -/
theorem scheduled_product_error (p r N z R B A E₀ T₀ : PTm n)
    (hz : Γ ⊢[PRAAx] GaussianEulerIntegralGammaIdentification.source z R B A)
    (hE₀ : Γ ⊢[PRAAx] le one E₀) :
    let G := gainBudget N z R B A
    let k := cutoff p N G
    let E := leftDen N k A R E₀
    let H := upper k A R T₀
    let T := N*H
    let u := GaussianCoefficientNameBounds.unit p
    let v := GaussianCoefficientNameBounds.unit r
    Γ ⊢[PRAAx] GaussianRationalMetric.distanceBounded
      (GaussianGammaZetaMellinDampedStrip.dampedValue (clock p N T) z B (mesh p N R E T) N one (width E H) E)
      (ap2 GaussianGammaZetaMellinDampedImproper.gammaProductF r
        (GaussianGammaZetaMellinDampedImproper.gammaProductData N z R B A))
      (LeanProofs.IPRA.PTm.num 9*(u*v)+(u+v)*u) (u*(u*v)) :=
  GaussianGammaZetaMellinDampedWindow.finite_gamma_dirichlet_error p r N z R B A one _ _ _ _ _
    (shared_source p N z R B A E₀ T₀ hz hE₀) (mesh_positive _ _ _ _ _) hz

end LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinDampedWindowSchedule
