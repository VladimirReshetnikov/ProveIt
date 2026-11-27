import IPRADerivations.Foundations.KleisliCategory

/-!
# Eilenberg–Moore algebras of the monad of an adjunction

Packet: `foundations/category_theory_ipra_2026-11-20`, `sections/adjunctions.tex`, Theorem `thm:em`
("Eilenberg–Moore construction"), for the monad `T = RL`, `μ_x = R(ε_{Lx})` of a presented adjunction
(`Foundations/AdjunctionMonad`). A `T`-algebra `(a, h)` is an arrow `h : Ta → a` with `h η_a = 1` and
`h μ_a = h T(h)`; a morphism `(a, h) → (b, k)` is `f : a → b` with `f h = k T(f)`. These are hypotheses
(derivable iPRA formulas), "arithmetical predicates on number codes, not new comprehension axioms".

* `T_id`: `T(1_a) = 1_{Ta}`;
* `id_morphism`, `comp_morphism`: identities and composites of algebra morphisms are algebra morphisms
  ("`(gf)h = g(kT(f)) = lT(g)T(f) = lT(gf)`");
* `free_unit`, `free_mult`: `(Ta, μ_a)` is an algebra ("The monad laws make `(Ta, μ_a)` an algebra");
  `free_morphism`: `T(f)` is an algebra morphism of free algebras ("Naturality of `μ`");
* `transpose_morphism`: for an algebra `(b, k)` and `g : a → b`, `k T(g) : (Ta, μ_a) → (b, k)` is an algebra
  morphism ("`kT(g)μ_a = kμ_bT²(g) = kT(k)T²(g) = kT(kT(g))`");
* `transpose_unit`: `k T(g) η_a = g`; `unit_transpose`: for an algebra morphism `f : (Ta, μ_a) → (b, k)`,
  `k T(f η_a) = f` (the two composites of the correspondence);
* `transpose_nat`: precomposition by `F^T(u) = T(u)` is precomposition by `u` after transposition
  ("`fT(u)η_{a'} = fη_a u`").
-/

namespace LeanProofs.IPRA.Foundations.EilenbergMoore

open_ipra exports
open LeanProofs.IPRA.Foundations.PresentedCategory
open LeanProofs.IPRA.Foundations.Adjunction
open LeanProofs.IPRA.Foundations.AdjunctionMonad
open LeanProofs.IPRA.Foundations.KleisliIdentity (mu_nat)
open LeanProofs.IPRA.Foundations.KleisliCategory (cmp_left cmp_right T_hom T_comp)

variable {C D : Pres} (LC : C.Laws) (LD : D.Laws) {A : Adj} (FL : A.L.Laws C D)
  (FR : A.R.Laws D C) (AL : A.Laws C D) {n : ℕ} {Γ : List (Fm PTm n)}

include LC FL FR in
theorem T_id {a : PTm n} (ha : Γ ⊢[PRAAx] C.obj a) :
    Γ ⊢[PRAAx] C.eqv (A.RL a) (A.RL a) (Tm A a a (C.id1 a)) (C.id1 (A.RL a)) :=
  LC.eqv_trans (FR.ar_congr (FL.ar_id ha)) (FR.ar_id (FL.ob_obj ha))

include LC FL FR in
/-- `1_a h = h T(1_a)`. -/
theorem id_morphism {a h : PTm n} (ha : Γ ⊢[PRAAx] C.obj a) (hh : Γ ⊢[PRAAx] C.hom (A.RL a) a h) :
    Γ ⊢[PRAAx] C.eqv (A.RL a) a (C.comp (A.RL a) a a (C.id1 a) h)
      (C.comp (A.RL a) (A.RL a) a h (Tm A a a (C.id1 a))) :=
  LC.eqv_trans (LC.id_left hh) (LC.eqv_symm (LC.eqv_trans (cmp_right LC hh (T_id LC FL FR ha)) (LC.id_right hh)))

include LC FL FR in
/-- `(g f) h = l T(g f)` for algebra morphisms `f : (a, h) → (b, k)`, `g : (b, k) → (c, l)`. -/
theorem comp_morphism {a b c f g h k l : PTm n} (hf : Γ ⊢[PRAAx] C.hom a b f) (hg : Γ ⊢[PRAAx] C.hom b c g)
    (hh : Γ ⊢[PRAAx] C.hom (A.RL a) a h) (hk : Γ ⊢[PRAAx] C.hom (A.RL b) b k)
    (hl : Γ ⊢[PRAAx] C.hom (A.RL c) c l)
    (mf : Γ ⊢[PRAAx] C.eqv (A.RL a) b (C.comp (A.RL a) a b f h) (C.comp (A.RL a) (A.RL b) b k (Tm A a b f)))
    (mg : Γ ⊢[PRAAx] C.eqv (A.RL b) c (C.comp (A.RL b) b c g k) (C.comp (A.RL b) (A.RL c) c l (Tm A b c g))) :
    Γ ⊢[PRAAx] C.eqv (A.RL a) c (C.comp (A.RL a) a c (C.comp a b c g f) h)
      (C.comp (A.RL a) (A.RL c) c l (Tm A a c (C.comp a b c g f))) := by
  have hTf := T_hom FL FR hf
  have hTg := T_hom FL FR hg
  have t₁ := LC.assoc hh hf hg
  have t₂ := cmp_right LC hg mf
  have t₃ := LC.eqv_symm (LC.assoc hTf hk hg)
  have t₄ := cmp_left LC hTf mg
  have t₅ := LC.assoc hTf hTg hl
  have t₆ := cmp_right LC hl (LC.eqv_symm (T_comp LC FL FR hf hg))
  exact LC.eqv_trans t₁ (LC.eqv_trans t₂ (LC.eqv_trans t₃ (LC.eqv_trans t₄ (LC.eqv_trans t₅ t₆))))

include FL AL in
/-- The free algebra, unit law: `μ_a η_{Ta} = 1`. -/
theorem free_unit {a : PTm n} (ha : Γ ⊢[PRAAx] C.obj a) :
    Γ ⊢[PRAAx] C.eqv (A.RL a) (A.RL a) (C.comp (A.RL a) (A.RL (A.RL a)) (A.RL a) (mu A a) (A.η (A.RL a)))
      (C.id1 (A.RL a)) :=
  unit_left FL AL ha

include LC LD FL FR AL in
/-- The free algebra, multiplication law: `μ_a μ_{Ta} = μ_a T(μ_a)`. -/
theorem free_mult {a : PTm n} (ha : Γ ⊢[PRAAx] C.obj a) :
    Γ ⊢[PRAAx] C.eqv (A.RL (A.RL (A.RL a))) (A.RL a)
      (C.comp (A.RL (A.RL (A.RL a))) (A.RL (A.RL a)) (A.RL a) (mu A a) (mu A (A.RL a)))
      (C.comp (A.RL (A.RL (A.RL a))) (A.RL (A.RL a)) (A.RL a) (mu A a) (Tm A (A.RL (A.RL a)) (A.RL a) (mu A a))) :=
  LC.eqv_symm (mu_assoc LC LD FL FR AL ha)

include LC LD FL FR AL in
/-- `T(f) : (Ta, μ_a) → (Tb, μ_b)` is an algebra morphism. -/
theorem free_morphism {a b f : PTm n} (ha : Γ ⊢[PRAAx] C.obj a) (hb : Γ ⊢[PRAAx] C.obj b)
    (hf : Γ ⊢[PRAAx] C.hom a b f) :
    Γ ⊢[PRAAx] C.eqv (A.RL (A.RL a)) (A.RL b)
      (C.comp (A.RL (A.RL a)) (A.RL a) (A.RL b) (Tm A a b f) (mu A a))
      (C.comp (A.RL (A.RL a)) (A.RL (A.RL b)) (A.RL b) (mu A b) (Tm A (A.RL a) (A.RL b) (Tm A a b f))) :=
  mu_nat LC LD FL FR AL ha hb hf

include LC LD FL FR AL in
/-- For an algebra `(b, k)` and `g : a → b`, `k T(g) : (Ta, μ_a) → (b, k)` is an algebra morphism. -/
theorem transpose_morphism {a b g k : PTm n} (ha : Γ ⊢[PRAAx] C.obj a) (hb : Γ ⊢[PRAAx] C.obj b)
    (hg : Γ ⊢[PRAAx] C.hom a b g) (hk : Γ ⊢[PRAAx] C.hom (A.RL b) b k)
    (hk₂ : Γ ⊢[PRAAx] C.eqv (A.RL (A.RL b)) b (C.comp (A.RL (A.RL b)) (A.RL b) b k (mu A b))
      (C.comp (A.RL (A.RL b)) (A.RL b) b k (Tm A (A.RL b) b k))) :
    Γ ⊢[PRAAx] C.eqv (A.RL (A.RL a)) b
      (C.comp (A.RL (A.RL a)) (A.RL a) b (C.comp (A.RL a) (A.RL b) b k (Tm A a b g)) (mu A a))
      (C.comp (A.RL (A.RL a)) (A.RL b) b k
        (Tm A (A.RL a) b (C.comp (A.RL a) (A.RL b) b k (Tm A a b g)))) := by
  have hμa := mu_hom FL FR AL ha
  have hμb := mu_hom FL FR AL hb
  have hTg := T_hom FL FR hg
  have hTTg := T_hom FL FR hTg
  have hTk := T_hom FL FR hk
  have t₁ := LC.assoc hμa hTg hk
  have t₂ := cmp_right LC hk (mu_nat LC LD FL FR AL ha hb hg)
  have t₃ := LC.eqv_symm (LC.assoc hTTg hμb hk)
  have t₄ := cmp_left LC hTTg hk₂
  have t₅ := LC.assoc hTTg hTk hk
  have t₆ := cmp_right LC hk (LC.eqv_symm (T_comp LC FL FR hTg hk))
  exact LC.eqv_trans t₁ (LC.eqv_trans t₂ (LC.eqv_trans t₃ (LC.eqv_trans t₄ (LC.eqv_trans t₅ t₆))))

include LC FL FR AL in
/-- `k T(g) η_a = g` for an algebra `(b, k)`. -/
theorem transpose_unit {a b g k : PTm n} (ha : Γ ⊢[PRAAx] C.obj a) (hb : Γ ⊢[PRAAx] C.obj b)
    (hg : Γ ⊢[PRAAx] C.hom a b g) (hk : Γ ⊢[PRAAx] C.hom (A.RL b) b k)
    (hk₁ : Γ ⊢[PRAAx] C.eqv b b (C.comp b (A.RL b) b k (A.η b)) (C.id1 b)) :
    Γ ⊢[PRAAx] C.eqv a b (C.comp a (A.RL a) b (C.comp (A.RL a) (A.RL b) b k (Tm A a b g)) (A.η a)) g := by
  have hηa := AL.eta_hom ha
  have hηb := AL.eta_hom hb
  have hTg := T_hom FL FR hg
  have t₁ := LC.assoc hηa hTg hk
  have t₂ := cmp_right LC hk (LC.eqv_symm (AL.eta_nat ha hb hg))
  have t₃ := LC.eqv_symm (LC.assoc hg hηb hk)
  have t₄ := cmp_left LC hg hk₁
  exact LC.eqv_trans t₁ (LC.eqv_trans t₂ (LC.eqv_trans t₃ (LC.eqv_trans t₄ (LC.id_left hg))))

include LC FL FR AL in
/-- `k T(f η_a) = f` for an algebra morphism `f : (Ta, μ_a) → (b, k)`. -/
theorem unit_transpose {a b f k : PTm n} (ha : Γ ⊢[PRAAx] C.obj a)
    (hf : Γ ⊢[PRAAx] C.hom (A.RL a) b f) (hk : Γ ⊢[PRAAx] C.hom (A.RL b) b k)
    (mf : Γ ⊢[PRAAx] C.eqv (A.RL (A.RL a)) b (C.comp (A.RL (A.RL a)) (A.RL a) b f (mu A a))
      (C.comp (A.RL (A.RL a)) (A.RL b) b k (Tm A (A.RL a) b f))) :
    Γ ⊢[PRAAx] C.eqv (A.RL a) b
      (C.comp (A.RL a) (A.RL b) b k (Tm A a b (C.comp a (A.RL a) b f (A.η a)))) f := by
  have hηa := AL.eta_hom ha
  have hμa := mu_hom FL FR AL ha
  have hTf := T_hom FL FR hf
  have hTη := T_hom FL FR hηa
  have t₁ := cmp_right LC hk (T_comp LC FL FR hηa hf)
  have t₂ := LC.eqv_symm (LC.assoc hTη hTf hk)
  have t₃ := cmp_left LC hTη (LC.eqv_symm mf)
  have t₄ := LC.assoc hTη hμa hf
  have t₅ := cmp_right LC hf (unit_right LC FL FR AL ha)
  exact LC.eqv_trans t₁ (LC.eqv_trans t₂ (LC.eqv_trans t₃ (LC.eqv_trans t₄ (LC.eqv_trans t₅ (LC.id_right hf)))))

include LC FL FR AL in
/-- Naturality in `a`: `(f T(u)) η_{a'} = (f η_a) u` for `u : a' → a`. -/
theorem transpose_nat {a a' b f u : PTm n} (ha : Γ ⊢[PRAAx] C.obj a) (ha' : Γ ⊢[PRAAx] C.obj a')
    (hu : Γ ⊢[PRAAx] C.hom a' a u) (hf : Γ ⊢[PRAAx] C.hom (A.RL a) b f) :
    Γ ⊢[PRAAx] C.eqv a' b (C.comp a' (A.RL a') b (C.comp (A.RL a') (A.RL a) b f (Tm A a' a u)) (A.η a'))
      (C.comp a' a b (C.comp a (A.RL a) b f (A.η a)) u) := by
  have hη' := AL.eta_hom ha'
  have hη := AL.eta_hom ha
  have hTu := T_hom FL FR hu
  have t₁ := LC.assoc hη' hTu hf
  have t₂ := cmp_right LC hf (LC.eqv_symm (AL.eta_nat ha' ha hu))
  have t₃ := LC.eqv_symm (LC.assoc hu hη hf)
  exact LC.eqv_trans t₁ (LC.eqv_trans t₂ t₃)

end LeanProofs.IPRA.Foundations.EilenbergMoore
