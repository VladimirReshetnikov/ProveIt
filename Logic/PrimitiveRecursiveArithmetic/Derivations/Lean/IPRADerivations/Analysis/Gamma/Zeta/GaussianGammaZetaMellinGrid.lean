import IPRADerivations.Analysis.Gamma.Zeta.GaussianGammaZetaMellinStrip

/-!
# The actual Mellin evaluator on a fixed rational grid

The ordinary compact quadrature uses the same original Mellin
observations as the finite-rectangle comparison on every physical tag.
-/

set_option autoImplicit false
set_option maxHeartbeats 700000

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinGrid

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCompactRiemannName (quadrature sampleBody sampleData sample_body_at)
open GaussianGammaZetaMellinIntegrand (nameF data subst_data)
open GaussianRationalFiniteSum (termsEqual)
open GaussianRationalSyntheticDivision (qmul_congr)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def fixedData (z B : PTm n) : PTm n := pairT z B
def evaluatorTerm (p t x : PTm n) : PTm n :=
  ap2 nameF p (data (fstT x) (sndT x) (fstT t) (sndT t))
def evaluatorF : PR 3 := PTm.toPR (evaluatorTerm (var 0) (var 1) (var 2))
def sample (p z B a b : PTm n) : PTm n := ap3 evaluatorF p (pairT a b) (fixedData z B)

@[simp] theorem subst_fixedData {m : ℕ} (σ : Fin n → PTm m) (z B : PTm n) :
    Syn.subst σ (fixedData z B) = fixedData (Syn.subst σ z) (Syn.subst σ B) := by simp [fixedData]
@[simp] theorem subst_evaluatorTerm {m : ℕ} (σ : Fin n → PTm m) (p t x : PTm n) :
    Syn.subst σ (evaluatorTerm p t x) = evaluatorTerm (Syn.subst σ p) (Syn.subst σ t) (Syn.subst σ x) := by
  simp [evaluatorTerm]

theorem evaluator_at (p t x : PTm n) : Γ ⊢[PRAAx] ap3 evaluatorF p t x ≐ evaluatorTerm p t x := by
  simpa [evaluatorF,ap3] using toPR_eq (Γ := Γ) (evaluatorTerm (var 0) (var 1) (var 2) : PTm 3) ![p,t,x]

theorem sample_at (p z B a b : PTm n) : Γ ⊢[PRAAx] sample p z B a b ≐ ap2 nameF p (data z B a b) := by
  refine (evaluator_at p (pairT a b) (fixedData z B)).eqTrans ?_
  let t := pairT a b
  let x := fixedData z B
  let body : PTm 5 := ap2 nameF (var 0) (data (var 1) (var 2) (var 3) (var 4))
  let v : Fin 5 → PTm n := ![p,fstT x,sndT x,fstT t,sndT t]
  let w : Fin 5 → PTm n := ![p,z,B,a,b]
  have e := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) body (σ := v) (σ' := w) (fun i => by
    fin_cases i
    · exact .eqRefl p
    · exact fst_pair z B
    · exact snd_pair z B
    · exact fst_pair a b
    · exact snd_pair a b)
  have left : Syn.subst v body = evaluatorTerm p t x := by
    simp only [body,subst_ap2,subst_data,Syn.subst_var]
    rfl
  have right : Syn.subst w body = ap2 nameF p (data z B a b) := by
    simp only [body,subst_ap2,subst_data,Syn.subst_var]
    rfl
  rw [left,right] at e
  exact e

theorem strip_grid_agreement (p z B M N a C E : PTm n) :
    Γ ⊢[PRAAx] GaussianGammaZetaMellinStrip.mellinValue p z B M N a C E ≐
      quadrature evaluatorF p M a C E (fixedData z B) := by
  let f := GaussianGammaZetaMellinStrip.mellinBody
  let g := sampleBody evaluatorF
  let X := GaussianGammaZetaMellinStrip.data p z B M N a C E
  let Y := sampleData p M a C E (fixedData z B)
  have rows : Γ ⊢[PRAAx] termsEqual f g M X Y := by
    refine .allI (.impI ?_)
    let sh (t : PTm n) := Syn.shift t
    let i : PTm (n+1) := var 0
    let Δ := lt i (sh M)::Γ.map Fm.shift
    have observed := GaussianGammaZetaMellinStrip.mellin_row_at (Γ := Δ)
      i (sh p) (sh z) (sh B) (sh M) (sh N) (sh a) (sh C) (sh E)
    have exactGrid := (sample_body_at (Γ := Δ) evaluatorF i (sh p) (sh M) (sh a) (sh C) (sh E)
        (fixedData (sh z) (sh B))).eqTrans
      (sample_at (sh p) (sh z) (sh B) (sh a*sh M+sh C*i) (sh E*sh M))
    simpa only [termsEqual, Δ, i, sh, f, g, X, Y, Syn.shift,
      GaussianGammaZetaMellinStrip.subst_data, GaussianCompactRiemannName.subst_sampleData, subst_fixedData]
      using observed.eqTrans exactGrid.eqSymm
  exact qmul_congr (.eqRefl _) (GaussianRationalFiniteSum.sum_congr_bounded f g M X Y rows)

end LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinGrid
