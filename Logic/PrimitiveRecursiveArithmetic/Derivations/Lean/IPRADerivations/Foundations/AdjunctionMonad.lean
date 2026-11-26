import IPRADerivations.Foundations.Adjunction
import IPRADerivations.Core.Header

/-!
# Every displayed adjunction induces a monad

Packet: `foundations/category_theory_ipra_2026-11-20`, `sections/adjunctions.tex`, Theorem "Every displayed
adjunction induces a monad": "For `F ⊣ G` with unit `η` and counit `ε`, the operations `T = GF`,
`μ_a = G(ε_{Fa})` …" satisfy the monad laws.

For the adjunctions of `Foundations/Adjunction` (`L ⊣ R`, presented categories, specified functors and
transformations, all laws as derivable rules), with `T = RL`, `T(f) = R(L(f))` and `μ_x = R(ε_{Lx})`:

* `mu_hom`: `μ_x : T(T(x)) → T(x)`;
* `unit_left`: `μ_x ∘ η_{Tx} = 1_{Tx}` (the right triangle at `Lx`);
* `unit_right`: `μ_x ∘ T(η_x) = 1_{Tx}` (the left triangle, transported by `R`);
* `mu_assoc`: `μ_x ∘ T(μ_x) = μ_x ∘ μ_{Tx}` (naturality of `ε` at `ε_{Lx}`, transported by `R`).

Each is an iPRA derivation at arbitrary object terms and hypotheses.
-/

namespace LeanProofs.IPRA.Foundations.AdjunctionMonad

open_ipra
open LeanProofs.IPRA.Foundations.PresentedCategory
open LeanProofs.IPRA.Foundations.Adjunction

variable {C D : Pres} (LC : C.Laws) (LD : D.Laws) {A : Adj} (FL : A.L.Laws C D)
  (FR : A.R.Laws D C) (AL : A.Laws C D) {n : ℕ} {Γ : List (Fm PTm n)}

/-- The multiplication `μ_x = R(ε_{Lx}) : T(T(x)) → T(x)`. -/
def mu (A : Adj) (x : PTm n) : PTm n := A.R.m (A.LR (A.L.o x)) (A.L.o x) (A.ε (A.L.o x))

/-- `T(f) = R(L(f))` for `f : u → v`. -/
def Tm (A : Adj) (u v f : PTm n) : PTm n := A.R.m (A.L.o u) (A.L.o v) (A.L.m u v f)

include FL FR AL in
theorem mu_hom {x : PTm n} (hx : Γ ⊢[PRAAx] C.obj x) :
    Γ ⊢[PRAAx] C.hom (A.RL (A.RL x)) (A.RL x) (mu A x) :=
  FR.ar_hom (AL.eps_hom (FL.ob_obj hx))

include FL AL in
/-- `μ_x ∘ η_{Tx} = 1_{Tx}`. -/
theorem unit_left {x : PTm n} (hx : Γ ⊢[PRAAx] C.obj x) :
    Γ ⊢[PRAAx] C.eqv (A.RL x) (A.RL x) (C.comp (A.RL x) (A.RL (A.RL x)) (A.RL x) (mu A x) (A.η (A.RL x)))
      (C.id1 (A.RL x)) :=
  AL.tri_right (FL.ob_obj hx)

include LC FL FR AL in
/-- `μ_x ∘ T(η_x) = 1_{Tx}`. -/
theorem unit_right {x : PTm n} (hx : Γ ⊢[PRAAx] C.obj x) :
    Γ ⊢[PRAAx] C.eqv (A.RL x) (A.RL x)
      (C.comp (A.RL x) (A.RL (A.RL x)) (A.RL x) (mu A x) (Tm A x (A.RL x) (A.η x)))
      (C.id1 (A.RL x)) := by
  have hLx := FL.ob_obj hx
  have hLη := FL.ar_hom (AL.eta_hom hx)
  have hε := AL.eps_hom hLx
  -- `R(ε ∘ L(η)) = R(ε) ∘ R(L(η))`
  have t₁ := FR.ar_comp hLη hε
  -- `R(ε ∘ L(η)) = R(1_{Lx})`
  have t₂ := FR.ar_congr (AL.tri_left hx)
  -- `R(1_{Lx}) = 1_{RLx}`
  have t₃ := FR.ar_id hLx
  exact LC.eqv_trans (LC.eqv_symm t₁) (LC.eqv_trans t₂ t₃)

include LC LD FL FR AL in
/-- `μ_x ∘ T(μ_x) = μ_x ∘ μ_{Tx}`. -/
theorem mu_assoc {x : PTm n} (hx : Γ ⊢[PRAAx] C.obj x) :
    Γ ⊢[PRAAx] C.eqv (A.RL (A.RL (A.RL x))) (A.RL x)
      (C.comp (A.RL (A.RL (A.RL x))) (A.RL (A.RL x)) (A.RL x) (mu A x) (Tm A (A.RL (A.RL x)) (A.RL x) (mu A x)))
      (C.comp (A.RL (A.RL (A.RL x))) (A.RL (A.RL x)) (A.RL x) (mu A x) (mu A (A.RL x))) := by
  have hy' := FL.ob_obj hx
  have hy := FL.ob_obj (FR.ob_obj hy')
  have hε' := AL.eps_hom hy'
  have hε := AL.eps_hom hy
  have hLRε := FL.ar_hom (FR.ar_hom hε')
  -- naturality of `ε` at `ε_{Lx}`: `ε_{Lx} ∘ ε_{LRLx} = ε_{Lx} ∘ LR(ε_{Lx})`
  have nat := AL.eps_nat hy hy' hε'
  -- `R(ε_{Lx} ∘ LR(ε_{Lx})) = μ_x ∘ T(μ_x)`
  have t₁ := FR.ar_comp hLRε hε'
  -- `R(ε_{Lx} ∘ ε_{LRLx}) = μ_x ∘ μ_{Tx}`
  have t₂ := FR.ar_comp hε hε'
  exact LC.eqv_trans (LC.eqv_symm t₁) (LC.eqv_trans (FR.ar_congr (LD.eqv_symm nat)) t₂)

end LeanProofs.IPRA.Foundations.AdjunctionMonad
