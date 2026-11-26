import IPRADerivations.Foundations.KleisliIdentity
import IPRADerivations.Core.Header

/-!
# The Kleisli category of the monad of an adjunction

Packet: `foundations/category_theory_ipra_2026-11-20`, `sections/adjunctions.tex`, Theorem `thm:kleisli`
("Kleisli construction"), for the monad `T = RL`, `μ_x = R(ε_{Lx})` of a presented adjunction
(`Foundations/AdjunctionMonad`), with Kleisli composition `g ⋆ f = μ_c ∘ T(g) ∘ f` (`KleisliIdentity.kcomp`;
the identity laws are `KleisliIdentity.kleisli_left`/`kleisli_right`):

* functoriality of `T`: `T_hom`, `T_congr`, `T_comp` (`T(g ∘ f) = T(g) ∘ T(f)`);
* typing and congruence of `⋆`: `kcomp_hom`, `kcomp_congr` ("Typing and congruence follow from those in `C`
  and `T`");
* `kleisli_assoc`: `h ⋆ (g ⋆ f) = (h ⋆ g) ⋆ f`, by naturality of `μ` at `h` and the associativity law
  `μ_d T(μ_d) = μ_d μ_{Td}`;
* the free functor `F_T(f) = η_b ∘ f`: `FT_id` and `FT_comp` (`F_T(g) ⋆ F_T(f) = F_T(g ∘ f)`);
* the forgetful functor `U_T(f) = μ_b ∘ T(f)`: `UT_id` and `UT_comp` (`U_T(g ⋆ f) = U_T(g) ∘ U_T(f)`);
* `UT_FT`: `U_T F_T(f) = T(f)`, so the adjunction `F_T ⊣ U_T` induces the original monad on arrows.

Each statement is an iPRA derivation at arbitrary object terms and hypotheses.
-/

namespace LeanProofs.IPRA.Foundations.KleisliCategory

open_ipra
open LeanProofs.IPRA.Foundations.PresentedCategory
open LeanProofs.IPRA.Foundations.Adjunction
open LeanProofs.IPRA.Foundations.AdjunctionMonad
open LeanProofs.IPRA.Foundations.KleisliIdentity

variable {C D : Pres} (LC : C.Laws) (LD : D.Laws) {A : Adj} (FL : A.L.Laws C D)
  (FR : A.R.Laws D C) (AL : A.Laws C D) {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Rewriting under composition -/

include LC in
theorem cmp_left {a b d p p' q : PTm n} (hq : Γ ⊢[PRAAx] C.hom a b q) (hp : Γ ⊢[PRAAx] C.eqv b d p p') :
    Γ ⊢[PRAAx] C.eqv a d (C.comp a b d p q) (C.comp a b d p' q) :=
  LC.comp_congr (LC.eqv_refl hq) hp

include LC in
theorem cmp_right {a b d p q q' : PTm n} (hp : Γ ⊢[PRAAx] C.hom b d p) (hq : Γ ⊢[PRAAx] C.eqv a b q q') :
    Γ ⊢[PRAAx] C.eqv a d (C.comp a b d p q) (C.comp a b d p q') :=
  LC.comp_congr hq (LC.eqv_refl hp)

/-! ## Functoriality of `T` -/

include FL FR in
theorem T_hom {u v f : PTm n} (hf : Γ ⊢[PRAAx] C.hom u v f) :
    Γ ⊢[PRAAx] C.hom (A.RL u) (A.RL v) (Tm A u v f) :=
  FR.ar_hom (FL.ar_hom hf)

include FL FR in
theorem T_congr {u v f f' : PTm n} (hf : Γ ⊢[PRAAx] C.eqv u v f f') :
    Γ ⊢[PRAAx] C.eqv (A.RL u) (A.RL v) (Tm A u v f) (Tm A u v f') :=
  FR.ar_congr (FL.ar_congr hf)

include LC FL FR in
theorem T_comp {u v w f g : PTm n} (hf : Γ ⊢[PRAAx] C.hom u v f) (hg : Γ ⊢[PRAAx] C.hom v w g) :
    Γ ⊢[PRAAx] C.eqv (A.RL u) (A.RL w) (Tm A u w (C.comp u v w g f))
      (C.comp (A.RL u) (A.RL v) (A.RL w) (Tm A v w g) (Tm A u v f)) :=
  LC.eqv_trans (FR.ar_congr (FL.ar_comp hf hg)) (FR.ar_comp (FL.ar_hom hf) (FL.ar_hom hg))

/-! ## Typing, congruence and associativity of `⋆` -/

include LC FL FR AL in
theorem kcomp_hom {a b c f g : PTm n} (hc : Γ ⊢[PRAAx] C.obj c) (hf : Γ ⊢[PRAAx] C.hom a (A.RL b) f)
    (hg : Γ ⊢[PRAAx] C.hom b (A.RL c) g) :
    Γ ⊢[PRAAx] C.hom a (A.RL c) (kcomp C A a b c f g) :=
  LC.comp_hom (LC.comp_hom hf (T_hom FL FR hg)) (mu_hom FL FR AL hc)

include LC FL FR AL in
theorem kcomp_congr {a b c f f' g g' : PTm n} (hc : Γ ⊢[PRAAx] C.obj c)
    (hf : Γ ⊢[PRAAx] C.eqv a (A.RL b) f f') (hg : Γ ⊢[PRAAx] C.eqv b (A.RL c) g g') :
    Γ ⊢[PRAAx] C.eqv a (A.RL c) (kcomp C A a b c f g) (kcomp C A a b c f' g') :=
  LC.comp_congr (LC.comp_congr hf (T_congr FL FR hg)) (LC.eqv_refl (mu_hom FL FR AL hc))

include LC LD FL FR AL in
/-- `h ⋆ (g ⋆ f) = (h ⋆ g) ⋆ f`. -/
theorem kleisli_assoc {a b c d f g h : PTm n} (hc : Γ ⊢[PRAAx] C.obj c) (hd : Γ ⊢[PRAAx] C.obj d)
    (hf : Γ ⊢[PRAAx] C.hom a (A.RL b) f) (hg : Γ ⊢[PRAAx] C.hom b (A.RL c) g)
    (hh : Γ ⊢[PRAAx] C.hom c (A.RL d) h) :
    Γ ⊢[PRAAx] C.eqv a (A.RL d) (kcomp C A a c d (kcomp C A a b c f g) h)
      (kcomp C A a b d f (kcomp C A b c d g h)) := by
  have hTd := FR.ob_obj (FL.ob_obj hd)
  have hμc := mu_hom FL FR AL hc
  have hμd := mu_hom FL FR AL hd
  have hμTd := mu_hom FL FR AL hTd
  have hTg := T_hom FL FR hg
  have hTh := T_hom FL FR hh
  have hTTh := T_hom FL FR hTh
  have hTμd := T_hom FL FR hμd
  have hX := LC.comp_hom hf hTg
  have hY := LC.comp_hom hX hTTh
  -- the left side: `μ_d (T h (μ_c X)) = μ_d (T μ_d Y)` with `X = T g ∘ f`, `Y = T²h ∘ X`
  have e₁ := LC.eqv_symm (LC.assoc hX hμc hTh)
  have e₂ := cmp_left LC hX (mu_nat LC LD FL FR AL hc hTd hh)
  have e₃ := LC.assoc hX hTTh hμTd
  have l₁ := cmp_right LC hμd (LC.eqv_trans e₁ (LC.eqv_trans e₂ e₃))
  have e₄ := LC.eqv_symm (LC.assoc hY hμTd hμd)
  have e₅ := cmp_left LC hY (LC.eqv_symm (mu_assoc LC LD FL FR AL hd))
  have e₆ := LC.assoc hY hTμd hμd
  have lhs := LC.eqv_trans l₁ (LC.eqv_trans e₄ (LC.eqv_trans e₅ e₆))
  -- the right side: `T(μ_d (T h ∘ g)) = T μ_d ∘ (T² h ∘ T g)`
  have hThg := LC.comp_hom hg hTh
  have r₁ := T_comp LC FL FR hThg hμd
  have r₂ := T_comp LC FL FR hg hTh
  have r₃ := LC.eqv_trans r₁ (cmp_right LC hTμd r₂)
  have r₄ := LC.assoc hf (LC.comp_hom hTg hTTh) hTμd
  have r₅ := cmp_right LC hTμd (LC.assoc hf hTg hTTh)
  have rhs := cmp_right LC hμd (LC.eqv_trans (cmp_left LC hf r₃) (LC.eqv_trans r₄ r₅))
  exact LC.eqv_trans lhs (LC.eqv_symm rhs)

/-! ## The free and forgetful functors -/

/-- `F_T(f) = η_b ∘ f` for `f : a → b`. -/
def FT (C : Pres) (A : Adj) (a b f : PTm n) : PTm n := C.comp a b (A.RL b) (A.η b) f

/-- `U_T(f) = μ_b ∘ T(f) : Ta → Tb` for a Kleisli arrow `f : a → Tb`. -/
def UT (C : Pres) (A : Adj) (a b f : PTm n) : PTm n :=
  C.comp (A.RL a) (A.RL (A.RL b)) (A.RL b) (mu A b) (Tm A a (A.RL b) f)

include LC AL in
theorem FT_id {a : PTm n} (ha : Γ ⊢[PRAAx] C.obj a) :
    Γ ⊢[PRAAx] C.eqv a (A.RL a) (FT C A a a (C.id1 a)) (A.η a) :=
  LC.id_right (AL.eta_hom ha)

include LC FL FR AL in
theorem UT_id {a : PTm n} (ha : Γ ⊢[PRAAx] C.obj a) :
    Γ ⊢[PRAAx] C.eqv (A.RL a) (A.RL a) (UT C A a a (A.η a)) (C.id1 (A.RL a)) :=
  unit_right LC FL FR AL ha

include LC FL FR AL in
/-- `F_T(g) ⋆ F_T(f) = F_T(g ∘ f)`. -/
theorem FT_comp {a b c f g : PTm n} (hb : Γ ⊢[PRAAx] C.obj b) (hc : Γ ⊢[PRAAx] C.obj c)
    (hf : Γ ⊢[PRAAx] C.hom a b f) (hg : Γ ⊢[PRAAx] C.hom b c g) :
    Γ ⊢[PRAAx] C.eqv a (A.RL c) (kcomp C A a b c (FT C A a b f) (FT C A b c g)) (FT C A a c (C.comp a b c g f)) := by
  have hηb := AL.eta_hom hb
  have hηc := AL.eta_hom hc
  have hμc := mu_hom FL FR AL hc
  have hTg := T_hom FL FR hg
  have hTηc := T_hom FL FR hηc
  have hηf := LC.comp_hom hf hηb
  have hZ := LC.comp_hom hηf hTg
  -- `T(η_c g) = T η_c ∘ T g`
  have s₁ := cmp_left LC hηf (T_comp LC FL FR hg hηc)
  have s₂ := LC.assoc hηf hTg hTηc
  have s₃ := LC.eqv_symm (LC.assoc hZ hTηc hμc)
  have s₄ := cmp_left LC hZ (unit_right LC FL FR AL hc)
  have s₅ := LC.id_left hZ
  have t₁ := cmp_right LC hμc (LC.eqv_trans s₁ s₂)
  have t₂ := LC.eqv_trans t₁ (LC.eqv_trans s₃ (LC.eqv_trans s₄ s₅))
  -- `T g ∘ (η_b ∘ f) = (η_c ∘ g) ∘ f = η_c ∘ (g ∘ f)`
  have s₆ := LC.eqv_symm (LC.assoc hf hηb hTg)
  have s₇ := cmp_left LC hf (LC.eqv_symm (AL.eta_nat hb hc hg))
  have s₈ := LC.assoc hf hg hηc
  exact LC.eqv_trans t₂ (LC.eqv_trans s₆ (LC.eqv_trans s₇ s₈))

include LC LD FL FR AL in
/-- `U_T(g ⋆ f) = U_T(g) ∘ U_T(f)`. -/
theorem UT_comp {a b c f g : PTm n} (hb : Γ ⊢[PRAAx] C.obj b) (hc : Γ ⊢[PRAAx] C.obj c)
    (hf : Γ ⊢[PRAAx] C.hom a (A.RL b) f) (hg : Γ ⊢[PRAAx] C.hom b (A.RL c) g) :
    Γ ⊢[PRAAx] C.eqv (A.RL a) (A.RL c) (UT C A a c (kcomp C A a b c f g))
      (C.comp (A.RL a) (A.RL b) (A.RL c) (UT C A b c g) (UT C A a b f)) := by
  have hTc := FR.ob_obj (FL.ob_obj hc)
  have hμb := mu_hom FL FR AL hb
  have hμc := mu_hom FL FR AL hc
  have hμTc := mu_hom FL FR AL hTc
  have hTf := T_hom FL FR hf
  have hTg := T_hom FL FR hg
  have hTTg := T_hom FL FR hTg
  have hTμc := T_hom FL FR hμc
  have hX := LC.comp_hom hf hTg
  have hW := LC.comp_hom hTf hTTg
  -- `T(μ_c (T g ∘ f)) = T μ_c ∘ (T² g ∘ T f)`
  have r₁ := T_comp LC FL FR hX hμc
  have r₂ := cmp_right LC hTμc (T_comp LC FL FR hf hTg)
  have t₁ := cmp_right LC hμc (LC.eqv_trans r₁ r₂)
  -- `μ_c (T μ_c W) = μ_c (μ_{Tc} W)`
  have s₁ := LC.eqv_symm (LC.assoc hW hTμc hμc)
  have s₂ := cmp_left LC hW (mu_assoc LC LD FL FR AL hc)
  have s₃ := LC.assoc hW hμTc hμc
  -- `μ_{Tc} (T² g ∘ T f) = (T g ∘ μ_b) ∘ T f`
  have s₄ := LC.eqv_symm (LC.assoc hTf hTTg hμTc)
  have s₅ := cmp_left LC hTf (LC.eqv_symm (mu_nat LC LD FL FR AL hb hTc hg))
  have s₆ := LC.assoc hTf hμb hTg
  have t₂ := cmp_right LC hμc (LC.eqv_trans s₄ (LC.eqv_trans s₅ s₆))
  have s₇ := LC.eqv_symm (LC.assoc (LC.comp_hom hTf hμb) hTg hμc)
  exact LC.eqv_trans t₁ (LC.eqv_trans s₁ (LC.eqv_trans s₂ (LC.eqv_trans s₃ (LC.eqv_trans t₂ s₇))))

include LC FL FR AL in
/-- `U_T F_T(f) = T(f)`. -/
theorem UT_FT {a b f : PTm n} (hb : Γ ⊢[PRAAx] C.obj b) (hf : Γ ⊢[PRAAx] C.hom a b f) :
    Γ ⊢[PRAAx] C.eqv (A.RL a) (A.RL b) (UT C A a b (FT C A a b f)) (Tm A a b f) := by
  have hηb := AL.eta_hom hb
  have hμb := mu_hom FL FR AL hb
  have hTf := T_hom FL FR hf
  have hTη := T_hom FL FR hηb
  have t₁ := cmp_right LC hμb (T_comp LC FL FR hf hηb)
  have t₂ := LC.eqv_symm (LC.assoc hTf hTη hμb)
  have t₃ := cmp_left LC hTf (unit_right LC FL FR AL hb)
  exact LC.eqv_trans t₁ (LC.eqv_trans t₂ (LC.eqv_trans t₃ (LC.id_left hTf)))

end LeanProofs.IPRA.Foundations.KleisliCategory
