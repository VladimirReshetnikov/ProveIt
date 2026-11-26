import IPRADerivations.Analysis.Integration.CompactGrids.GaussianCompactIntervalRescaling
import IPRADerivations.Analysis.Integration.CompactGrids.GaussianCompactMeshIndependence
import IPRADerivations.Analysis.Euler.CompactExhaustion.GaussianEulerCompactAdditivity

/-!
# Original Euler compact names align at new denominators and budgets

Original native disk and interval guards derive every actual modulus,
scaled source and legitimate budget used in the alignment. Both returned
data refer to the SAME original Euler quadrature name program. Its old
sample clock and new sample clock are independent; exact finite proofs
of interval rescaling and mesh independence supply cross-equivalence.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerCompactAlignment

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerCompactAdditivity (data nameF intervalSource)
open GaussianEulerCompactModulus (lipschitz)
open GaussianRationalHorner (positive_product)
open GaussianNameEquivalence (crossEquivalent)
open GaussianRationalMetric (distanceBounded)
open GaussianCoefficientNameBounds (unit)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (z R B a C E T S k : PTm n) : Fm PTm n := GaussianEulerExponentCompactBounds.source z R B E ⋏
  (le one a ⋏ (le one k ⋏ (le (a+C) (E*T) ⋏ le (a+C) (E*S))))
@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (z R B a C E T S k : PTm n) :
    (source z R B a C E T S k).subst σ = source (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ a)
      (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ S) (Syn.subst σ k) := by simp [source]

theorem original_source (z R B a C E T S k : PTm n) (h : Γ ⊢[PRAAx] source z R B a C E T S k) : Γ ⊢[PRAAx]
    intervalSource z R B a C E T := .andI h.andE₁ (.andI h.andE₂.andE₁ h.andE₂.andE₂.andE₂.andE₁)

theorem scaled_source (z R B a C E T S k : PTm n) (h : Γ ⊢[PRAAx] source z R B a C E T S k) : Γ ⊢[PRAAx]
    intervalSource z R B (k*a) (k*C) (k*E) S := by
  have hk := h.andE₂.andE₂.andE₁
  have ep := positive_product (Γ := Γ) _ _ hk h.andE₁.andE₂.andE₁
  have newSource : Γ ⊢[PRAAx] GaussianEulerExponentCompactBounds.source z R B (k*E) :=
    .andI h.andE₁.andE₁ (.andI ep h.andE₁.andE₂.andE₂)
  have endpoint : Γ ⊢[PRAAx] le (k*a+k*C) ((k*E)*S) :=
    le_congr (by ipra_ring) (by ipra_ring) (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl k) h.andE₂.andE₂.andE₂.andE₂)
  exact .andI newSource (.andI (positive_product _ _ hk h.andE₂.andE₁) endpoint)

theorem aligned_names (z R B a C E T S k : PTm n) (h : Γ ⊢[PRAAx] source z R B a C E T S k) : Γ ⊢[PRAAx]
    crossEquivalent nameF nameF (data z R B a C E T) (data z R B (k*a) (k*C) (k*E) S) := by
  let F := GaussianEulerIntegrandName.evaluatorF
  let x := GaussianEulerIntegrandName.fixedData z B
  let L := lipschitz R E T
  let M := lipschitz R (k*E) S
  have old := GaussianEulerCompactAdditivity.compact_input z R B a C E T (original_source z R B a C E T S k h)
  have rescaleInput : Γ ⊢[PRAAx] GaussianCompactIntervalRescaling.input F k a C E L T x := .andI h.andE₂.andE₂.andE₁ old
  have mid := GaussianCompactIntervalRescaling.scaled_input F k a C E L T x rescaleInput
  have newInput := GaussianEulerCompactAdditivity.compact_input z R B (k*a) (k*C) (k*E) S (scaled_source z R B a C E T S k h)
  have first := GaussianCompactIntervalRescaling.name_rescaling F k a C E L T x rescaleInput
  have second := GaussianCompactMeshIndependence.name_independence F (k*a) (k*C) (k*E) L T M S x (.andI mid newInput)
  exact GaussianNameEquivalence.cross_trans _ _ _ _ _ _ first second

theorem observations (p q z R B a C E T S k : PTm n) (h : Γ ⊢[PRAAx] source z R B a C E T S k) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (data z R B a C E T)) (ap2 nameF q (data z R B (k*a) (k*C) (k*E) S))
      (unit p+unit q) (unit p*unit q) := GaussianNameEquivalence.cross_at _ _ _ _ p q (aligned_names z R B a C E T S k h)

def output (z R B a C E T S k : PTm n) : PTm n := pairT (data z R B a C E T)
  (pairT (data z R B (k*a) (k*C) (k*E) S) (pairT (lipschitz R E T) (lipschitz R (k*E) S)))
def outputF : PR 9 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8))
def run (z R B a C E T S k : PTm n) : PTm n := PTm.app outputF ![z,R,B,a,C,E,T,S,k]
@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (z R B a C E T S k : PTm n) :
    Syn.subst σ (output z R B a C E T S k) = output (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ a)
      (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ S) (Syn.subst σ k) := by simp [output]
theorem program_at (z R B a C E T S k : PTm n) : Γ ⊢[PRAAx] run z R B a C E T S k ≐ output z R B a C E T S k := by
  simpa [run,outputF] using toPR_eq (Γ := Γ)
    (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) : PTm 9) ![z,R,B,a,C,E,T,S,k]
theorem returned_original (z R B a C E T S k : PTm n) : Γ ⊢[PRAAx]
    fstT (run z R B a C E T S k) ≐ data z R B a C E T := (congrFst (program_at z R B a C E T S k)).eqTrans (fst_pair _ _)
theorem returned_tail (z R B a C E T S k : PTm n) : Γ ⊢[PRAAx]
    sndT (run z R B a C E T S k) ≐ pairT (data z R B (k*a) (k*C) (k*E) S)
      (pairT (lipschitz R E T) (lipschitz R (k*E) S)) := (congrSnd (program_at z R B a C E T S k)).eqTrans (snd_pair _ _)
theorem returned_aligned (z R B a C E T S k : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run z R B a C E T S k)) ≐ data z R B (k*a) (k*C) (k*E) S :=
  (congrFst (returned_tail z R B a C E T S k)).eqTrans (fst_pair _ _)
theorem returned_budgets (z R B a C E T S k : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (run z R B a C E T S k)) ≐ pairT (lipschitz R E T) (lipschitz R (k*E) S) :=
  (congrSnd (returned_tail z R B a C E T S k)).eqTrans (snd_pair _ _)
theorem returned_original_budget (z R B a C E T S k : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (run z R B a C E T S k))) ≐ lipschitz R E T := (congrFst (returned_budgets z R B a C E T S k)).eqTrans (fst_pair _ _)
theorem returned_aligned_budget (z R B a C E T S k : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (run z R B a C E T S k))) ≐ lipschitz R (k*E) S := (congrSnd (returned_budgets z R B a C E T S k)).eqTrans (snd_pair _ _)

theorem returned_alignment (z R B a C E T S k : PTm n) (h : Γ ⊢[PRAAx] source z R B a C E T S k) : Γ ⊢[PRAAx]
    crossEquivalent nameF nameF (fstT (run z R B a C E T S k)) (fstT (sndT (run z R B a C E T S k))) := by
  simpa using Prf.eqSubst (crossEquivalent nameF nameF (var 0) (var 1) : Fm PTm 2)
    ![data z R B a C E T,data z R B (k*a) (k*C) (k*E) S]
    ![fstT (run z R B a C E T S k),fstT (sndT (run z R B a C E T S k))]
    (fun i => by fin_cases i; exact (returned_original z R B a C E T S k).eqSymm; exact (returned_aligned z R B a C E T S k).eqSymm)
    (by simpa using aligned_names z R B a C E T S k h)

theorem original_Euler_scaled_source_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      intervalSource (var 0) (var 1) (var 2) (var 8*var 3) (var 8*var 4) (var 8*var 5) (var 7)) :=
  closeUniv 9 (.impI (scaled_source _ _ _ _ _ _ _ _ _ Prf.hyp0))
theorem original_Euler_compact_encoding_budget_alignment_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      crossEquivalent nameF nameF (data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
        (data (var 0) (var 1) (var 2) (var 8*var 3) (var 8*var 4) (var 8*var 5) (var 7))) :=
  closeUniv 9 (.impI (aligned_names _ _ _ _ _ _ _ _ _ Prf.hyp0))
theorem original_Euler_aligned_independent_observations_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
    (source (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) ⟶
      distanceBounded (ap2 nameF (var 0) (data (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)))
        (ap2 nameF (var 1) (data (var 2) (var 3) (var 4) (var 10*var 5) (var 10*var 6) (var 10*var 7) (var 9)))
        (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 11 (.impI (observations _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))
theorem actual_Euler_alignment_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ≐
      output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)) :=
  closeUniv 9 (program_at _ _ _ _ _ _ _ _ _)
theorem actual_returned_Euler_alignment_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      crossEquivalent nameF nameF (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)))
        (fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8))))) :=
  closeUniv 9 (.impI (returned_alignment _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerCompactAlignment
