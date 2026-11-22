import IPRADerivations.Foundations.AdjunctionMonad

/-!
# Naturality of the multiplication and the Kleisli identity laws

Packet: `foundations/category_theory_ipra_2026-11-20`, `sections/adjunctions.tex`, Theorem `thm:kleisli`
("Kleisli construction": "A presented monad `T` determines a presented category `C_T` with the same object
codes as `C`, arrows `a → b` represented by arrows `a → Tb` in `C`, identity `η_a`, and composition
`g ∘_T f = μ_c ∘ T(g) ∘ f`"), for the monad `T = RL` of a presented adjunction (`Foundations/AdjunctionMonad`):

* `mu_nat`: `T(a) ∘ μ_x = μ_{x'} ∘ T(T(a))` for `a : x → x'` (naturality of `ε` at `L(a)`, transported by
  `R`);
* `kleisli_left`: `η_b ∘_T f = f` for `f : a → Tb` (the right unit law `μ ∘ T(η) = 1`);
* `kleisli_right`: `f ∘_T η_a = f` (naturality of `η` and the left unit law `μ ∘ η_T = 1`).
-/

namespace LeanProofs.IPRA.Foundations.KleisliIdentity

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.PresentedCategory
open LeanProofs.IPRA.Foundations.Adjunction
open LeanProofs.IPRA.Foundations.AdjunctionMonad
open Syn
open scoped Fm

variable {C D : Pres} (LC : C.Laws) (LD : D.Laws) {A : Adj} (FL : A.L.Laws C D)
  (FR : A.R.Laws D C) (AL : A.Laws C D) {n : ℕ} {Γ : List (Fm PTm n)}

include LC LD FL FR AL in
/-- `T(a) ∘ μ_x = μ_{x'} ∘ T(T(a))`. -/
theorem mu_nat {x x' a : PTm n} (hx : Γ ⊢[PRAAx] C.obj x) (hx' : Γ ⊢[PRAAx] C.obj x')
    (ha : Γ ⊢[PRAAx] C.hom x x' a) :
    Γ ⊢[PRAAx] C.eqv (A.RL (A.RL x)) (A.RL x')
      (C.comp (A.RL (A.RL x)) (A.RL x) (A.RL x') (Tm A x x' a) (mu A x))
      (C.comp (A.RL (A.RL x)) (A.RL (A.RL x')) (A.RL x') (mu A x') (Tm A (A.RL x) (A.RL x') (Tm A x x' a))) := by
  have hy := FL.ob_obj hx
  have hy' := FL.ob_obj hx'
  have hb := FL.ar_hom ha
  have hε := AL.eps_hom hy
  have hε' := AL.eps_hom hy'
  have hLRb := FL.ar_hom (FR.ar_hom hb)
  -- `L(a) ∘ ε_{Lx} = ε_{Lx'} ∘ LR(L(a))`
  have nat := AL.eps_nat hy hy' hb
  have t₁ := FR.ar_comp hε hb
  have t₂ := FR.ar_comp hLRb hε'
  exact LC.eqv_trans (LC.eqv_symm t₁) (LC.eqv_trans (FR.ar_congr nat) t₂)

/-- Kleisli composition `g ∘_T f = μ_c ∘ (T(g) ∘ f)` for `f : a → Tb`, `g : b → Tc`. -/
def kcomp (C : Pres) (A : Adj) (a b c f g : PTm n) : PTm n :=
  C.comp a (A.RL (A.RL c)) (A.RL c) (mu A c) (C.comp a (A.RL b) (A.RL (A.RL c)) (Tm A b (A.RL c) g) f)

include LC FL FR AL in
/-- `η_b ∘_T f = f`. -/
theorem kleisli_left {a b f : PTm n} (hb : Γ ⊢[PRAAx] C.obj b) (hf : Γ ⊢[PRAAx] C.hom a (A.RL b) f) :
    Γ ⊢[PRAAx] C.eqv a (A.RL b) (kcomp C A a b b f (A.η b)) f := by
  have hTη := FR.ar_hom (FL.ar_hom (AL.eta_hom hb))
  have hμ := mu_hom FL FR AL hb
  -- `μ ∘ (Tη ∘ f) = (μ ∘ Tη) ∘ f`
  have t₁ := LC.eqv_symm (LC.assoc hf hTη hμ)
  have t₂ := LC.comp_congr (LC.eqv_refl hf) (unit_right LC FL FR AL hb)
  exact LC.eqv_trans t₁ (LC.eqv_trans t₂ (LC.id_left hf))

include LC FL FR AL in
/-- `f ∘_T η_a = f`. -/
theorem kleisli_right {a b f : PTm n} (ha : Γ ⊢[PRAAx] C.obj a) (hb : Γ ⊢[PRAAx] C.obj b)
    (hf : Γ ⊢[PRAAx] C.hom a (A.RL b) f) :
    Γ ⊢[PRAAx] C.eqv a (A.RL b) (kcomp C A a a b (A.η a) f) f := by
  have hTb := FR.ob_obj (FL.ob_obj hb)
  have hη := AL.eta_hom ha
  have hηT := AL.eta_hom hTb
  have hμ := mu_hom FL FR AL hb
  -- naturality of `η` at `f`: `η_{Tb} ∘ f = T(f) ∘ η_a`
  have nat := AL.eta_nat ha hTb hf
  have t₁ := LC.comp_congr (LC.eqv_symm nat) (LC.eqv_refl hμ)
  -- `μ ∘ (η_{Tb} ∘ f) = (μ ∘ η_{Tb}) ∘ f`
  have t₂ := LC.eqv_symm (LC.assoc hf hηT hμ)
  have t₃ := LC.comp_congr (LC.eqv_refl hf) (unit_left FL AL hb)
  exact LC.eqv_trans t₁ (LC.eqv_trans t₂ (LC.eqv_trans t₃ (LC.id_left hf)))

end LeanProofs.IPRA.Foundations.KleisliIdentity
