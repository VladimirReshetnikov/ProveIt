import IPRADerivations.Foundations.PresentedCategory
import IPRADerivations.Core.ParityArith

/-!
# Adjunctions from unit and counit (`ipra_categorical_methods`, Section 4)

Packet: `foundations/ipra_categorical_methods`, Subsection "Adjunctions from unit and counit".
Everything is for *fixed presentations*: two presented categories `C`, `D` with laws
(`Foundations/PresentedCategory`), specified functors `L : C → D`, `R : D → C` (a term for the
object map and a term for the arrow map, `Fun`, with laws `Fun.Laws`), and specified
transformations `η : 1 → RL`, `ε : LR → 1` (one term each, `Adj`). The laws `Adj.Laws` are
typing, naturality and the two triangle equations

`ε_{Lx} ∘ L(η_x) = 1_{Lx}`, `R(ε_y) ∘ η_{Ry} = 1_{Ry}`,

each a rule derivable at arbitrary terms and hypotheses, with its object guards.

With `Φ(f) = R(f) ∘ η_x` for `f : Lx → y` and `Ψ(g) = ε_y ∘ L(g)` for `g : x → Ry`:

* `phi_hom`, `psi_hom`, `phi_congr`, `psi_congr`: typing and compatibility with arrow
  equality;
* `psi_phi`: `Ψ(Φ(f)) = f`; `phi_psi`: `Φ(Ψ(g)) = g` (the paper's two displayed chains);
* `phi_nat_right`: `Φ(b ∘ f) = R(b) ∘ Φ(f)`; `phi_nat_left`: `Φ(f ∘ L(a)) = Φ(f) ∘ a`
  (together the paper's `Φ(b ∘ f ∘ L(a)) = R(b) ∘ Φ(f) ∘ a`).

Conversely (`section Converse`), for *supplied* natural inverse hom correspondences `Φ`, `Ψ`
(terms `phi`, `psi` with laws `CorrLaws`), with `η_x = Φ(1_{Lx})` and `ε_y = Ψ(1_{Ry})`:

* `corr_phi_formula`: `Φ(f) = R(f) ∘ η_x`; `corr_psi_formula`: `Ψ(g) = ε_y ∘ L(g)`;
* `corr_psi_nat_left`, `corr_psi_nat_right`: naturality of `Ψ`, derived from that of `Φ`;
* `corr_tri_left`, `corr_tri_right`: the triangle equations;
* `corr_eta_nat`, `corr_eps_nat`: naturality of the unit and the counit.

No hom-set is enumerated and no function-space object is assumed.

An instance with every hypothesis discharged: the preorder `(ℕ, ≤)` as a thin presented
category `natLe`, with `L(x) = 2x` and `R(y) = ⌊y / 2⌋`. The typing theorems become the Galois
connection `2x ≤ y ↔ x ≤ ⌊y / 2⌋` (`galois_closed`); it uses `half_mono`.
-/

namespace LeanProofs.IPRA.Foundations.Adjunction

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.PresentedCategory
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

/-- A specified functor between presentations. -/
structure Fun where
  /-- The object map `ob(a)`; variable `0 = a`. -/
  ob : PTm 1
  /-- The arrow map `ar(a, b, f)` for `f : a → b`; variables `0 = a`, `1 = b`, `2 = f`. -/
  ar : PTm 3

namespace Fun

variable (F : Fun) {n : ℕ}

/-- The object `F(a)`. -/
def o (a : PTm n) : PTm n := Syn.subst ![a] F.ob
/-- The arrow `F(f) : F(a) → F(b)` for `f : a → b`. -/
def m (a b f : PTm n) : PTm n := Syn.subst ![a, b, f] F.ar

/-- The laws of a functor `C → D`. -/
structure Laws (C D : Pres) : Prop where
  ob_obj : ∀ {n : ℕ} {Γ : List (Fm PTm n)} {a : PTm n},
    (Γ ⊢[PRAAx] C.obj a) → (Γ ⊢[PRAAx] D.obj (F.o a))
  ar_hom : ∀ {n : ℕ} {Γ : List (Fm PTm n)} {a b f : PTm n},
    (Γ ⊢[PRAAx] C.hom a b f) → (Γ ⊢[PRAAx] D.hom (F.o a) (F.o b) (F.m a b f))
  ar_congr : ∀ {n : ℕ} {Γ : List (Fm PTm n)} {a b f g : PTm n},
    (Γ ⊢[PRAAx] C.eqv a b f g) → (Γ ⊢[PRAAx] D.eqv (F.o a) (F.o b) (F.m a b f) (F.m a b g))
  ar_id : ∀ {n : ℕ} {Γ : List (Fm PTm n)} {a : PTm n},
    (Γ ⊢[PRAAx] C.obj a) →
      (Γ ⊢[PRAAx] D.eqv (F.o a) (F.o a) (F.m a a (C.id1 a)) (D.id1 (F.o a)))
  ar_comp : ∀ {n : ℕ} {Γ : List (Fm PTm n)} {a b d f g : PTm n},
    (Γ ⊢[PRAAx] C.hom a b f) → (Γ ⊢[PRAAx] C.hom b d g) →
      (Γ ⊢[PRAAx] D.eqv (F.o a) (F.o d) (F.m a d (C.comp a b d g f))
        (D.comp (F.o a) (F.o b) (F.o d) (F.m b d g) (F.m a b f)))

end Fun

/-- The data of an adjunction `L ⊣ R` given by unit and counit. -/
structure Adj where
  /-- The left adjoint `L : C → D`. -/
  L : Fun
  /-- The right adjoint `R : D → C`. -/
  R : Fun
  /-- The unit `η_x : x → R(L(x))`; variable `0 = x`. -/
  eta : PTm 1
  /-- The counit `ε_y : L(R(y)) → y`; variable `0 = y`. -/
  eps : PTm 1

namespace Adj

variable (A : Adj) {n : ℕ}

/-- `η_x`. -/
def η (x : PTm n) : PTm n := Syn.subst ![x] A.eta
/-- `ε_y`. -/
def ε (y : PTm n) : PTm n := Syn.subst ![y] A.eps
/-- `R(L(x))`. -/
abbrev RL (x : PTm n) : PTm n := A.R.o (A.L.o x)
/-- `L(R(y))`. -/
abbrev LR (y : PTm n) : PTm n := A.L.o (A.R.o y)

/-- `Φ(f) = R(f) ∘ η_x : x → R(y)` for `f : L(x) → y`. -/
def Φ (C : Pres) (x y f : PTm n) : PTm n :=
  C.comp x (A.RL x) (A.R.o y) (A.R.m (A.L.o x) y f) (A.η x)

/-- `Ψ(g) = ε_y ∘ L(g) : L(x) → y` for `g : x → R(y)`. -/
def Ψ (D : Pres) (x y g : PTm n) : PTm n :=
  D.comp (A.L.o x) (A.LR y) y (A.ε y) (A.L.m x (A.R.o y) g)

/-- Typing and naturality of unit and counit, and the triangle equations. -/
structure Laws (C D : Pres) : Prop where
  eta_hom : ∀ {n : ℕ} {Γ : List (Fm PTm n)} {x : PTm n},
    (Γ ⊢[PRAAx] C.obj x) → (Γ ⊢[PRAAx] C.hom x (A.RL x) (A.η x))
  eta_nat : ∀ {n : ℕ} {Γ : List (Fm PTm n)} {x x' a : PTm n},
    (Γ ⊢[PRAAx] C.obj x) → (Γ ⊢[PRAAx] C.obj x') → (Γ ⊢[PRAAx] C.hom x x' a) →
      (Γ ⊢[PRAAx] C.eqv x (A.RL x') (C.comp x x' (A.RL x') (A.η x') a)
        (C.comp x (A.RL x) (A.RL x') (A.R.m (A.L.o x) (A.L.o x') (A.L.m x x' a)) (A.η x)))
  eps_hom : ∀ {n : ℕ} {Γ : List (Fm PTm n)} {y : PTm n},
    (Γ ⊢[PRAAx] D.obj y) → (Γ ⊢[PRAAx] D.hom (A.LR y) y (A.ε y))
  eps_nat : ∀ {n : ℕ} {Γ : List (Fm PTm n)} {y y' b : PTm n},
    (Γ ⊢[PRAAx] D.obj y) → (Γ ⊢[PRAAx] D.obj y') → (Γ ⊢[PRAAx] D.hom y y' b) →
      (Γ ⊢[PRAAx] D.eqv (A.LR y) y' (D.comp (A.LR y) y y' b (A.ε y))
        (D.comp (A.LR y) (A.LR y') y' (A.ε y') (A.L.m (A.R.o y) (A.R.o y') (A.R.m y y' b))))
  tri_left : ∀ {n : ℕ} {Γ : List (Fm PTm n)} {x : PTm n},
    (Γ ⊢[PRAAx] C.obj x) →
      (Γ ⊢[PRAAx] D.eqv (A.L.o x) (A.L.o x)
        (D.comp (A.L.o x) (A.LR (A.L.o x)) (A.L.o x) (A.ε (A.L.o x)) (A.L.m x (A.RL x) (A.η x)))
        (D.id1 (A.L.o x)))
  tri_right : ∀ {n : ℕ} {Γ : List (Fm PTm n)} {y : PTm n},
    (Γ ⊢[PRAAx] D.obj y) →
      (Γ ⊢[PRAAx] C.eqv (A.R.o y) (A.R.o y)
        (C.comp (A.R.o y) (A.RL (A.R.o y)) (A.R.o y) (A.R.m (A.LR y) y (A.ε y)) (A.η (A.R.o y)))
        (C.id1 (A.R.o y)))

end Adj

/-! ## The hom correspondences of an adjunction -/

section Correspondence

variable {C D : Pres} (LC : C.Laws) (LD : D.Laws) {A : Adj} (FL : A.L.Laws C D)
  (FR : A.R.Laws D C) (AL : A.Laws C D) {n : ℕ} {Γ : List (Fm PTm n)}

include LC FR AL in
/-- `Φ(f) : x → R(y)` for `f : L(x) → y`. -/
theorem phi_hom {x y f : PTm n} (hx : Γ ⊢[PRAAx] C.obj x)
    (hf : Γ ⊢[PRAAx] D.hom (A.L.o x) y f) : Γ ⊢[PRAAx] C.hom x (A.R.o y) (A.Φ C x y f) :=
  LC.comp_hom (AL.eta_hom hx) (FR.ar_hom hf)

include LD FL AL in
/-- `Ψ(g) : L(x) → y` for `g : x → R(y)`. -/
theorem psi_hom {x y g : PTm n} (hy : Γ ⊢[PRAAx] D.obj y)
    (hg : Γ ⊢[PRAAx] C.hom x (A.R.o y) g) : Γ ⊢[PRAAx] D.hom (A.L.o x) y (A.Ψ D x y g) :=
  LD.comp_hom (FL.ar_hom hg) (AL.eps_hom hy)

include LC FR AL in
/-- `Φ` respects arrow equality. -/
theorem phi_congr {x y f f' : PTm n} (hx : Γ ⊢[PRAAx] C.obj x)
    (h : Γ ⊢[PRAAx] D.eqv (A.L.o x) y f f') :
    Γ ⊢[PRAAx] C.eqv x (A.R.o y) (A.Φ C x y f) (A.Φ C x y f') :=
  LC.comp_congr (LC.eqv_refl (AL.eta_hom hx)) (FR.ar_congr h)

include LD FL AL in
/-- `Ψ` respects arrow equality. -/
theorem psi_congr {x y g g' : PTm n} (hy : Γ ⊢[PRAAx] D.obj y)
    (h : Γ ⊢[PRAAx] C.eqv x (A.R.o y) g g') :
    Γ ⊢[PRAAx] D.eqv (A.L.o x) y (A.Ψ D x y g) (A.Ψ D x y g') :=
  LD.comp_congr (FL.ar_congr h) (LD.eqv_refl (AL.eps_hom hy))

include LD FL FR AL in
/-- `Ψ(Φ(f)) = ε_y ∘ LR(f) ∘ L(η_x) = f ∘ ε_{Lx} ∘ L(η_x) = f`. -/
theorem psi_phi {x y f : PTm n} (hx : Γ ⊢[PRAAx] C.obj x) (hy : Γ ⊢[PRAAx] D.obj y)
    (hf : Γ ⊢[PRAAx] D.hom (A.L.o x) y f) :
    Γ ⊢[PRAAx] D.eqv (A.L.o x) y (A.Ψ D x y (A.Φ C x y f)) f := by
  have hη := AL.eta_hom hx
  have hRf := FR.ar_hom hf
  have hLη := FL.ar_hom hη
  have hLRf := FL.ar_hom hRf
  have hLx := FL.ob_obj hx
  have hεy := AL.eps_hom hy
  have hεL := AL.eps_hom hLx
  -- `L(R(f) ∘ η_x) = LR(f) ∘ L(η_x)`
  have t₁ := LD.comp_congr (FL.ar_comp hη hRf) (LD.eqv_refl hεy)
  -- `ε_y ∘ (LR(f) ∘ L(η_x)) = (ε_y ∘ LR(f)) ∘ L(η_x)`
  have t₂ := LD.eqv_symm (LD.assoc hLη hLRf hεy)
  -- naturality of the counit at `f`: `ε_y ∘ LR(f) = f ∘ ε_{Lx}`
  have t₃ := LD.comp_congr (LD.eqv_refl hLη) (LD.eqv_symm (AL.eps_nat hLx hy hf))
  -- `(f ∘ ε_{Lx}) ∘ L(η_x) = f ∘ (ε_{Lx} ∘ L(η_x))`
  have t₄ := LD.assoc hLη hεL hf
  -- the left triangle
  have t₅ := LD.comp_congr (AL.tri_left hx) (LD.eqv_refl hf)
  have t₆ := LD.id_right hf
  exact LD.eqv_trans t₁ (LD.eqv_trans t₂ (LD.eqv_trans t₃ (LD.eqv_trans t₄ (LD.eqv_trans t₅ t₆))))

include LC FL FR AL in
/-- `Φ(Ψ(g)) = R(ε_y) ∘ RL(g) ∘ η_x = R(ε_y) ∘ η_{Ry} ∘ g = g`. -/
theorem phi_psi {x y g : PTm n} (hx : Γ ⊢[PRAAx] C.obj x) (hy : Γ ⊢[PRAAx] D.obj y)
    (hg : Γ ⊢[PRAAx] C.hom x (A.R.o y) g) :
    Γ ⊢[PRAAx] C.eqv x (A.R.o y) (A.Φ C x y (A.Ψ D x y g)) g := by
  have hη := AL.eta_hom hx
  have hLg := FL.ar_hom hg
  have hRLg := FR.ar_hom hLg
  have hεy := AL.eps_hom hy
  have hRε := FR.ar_hom hεy
  have hRy := FR.ob_obj hy
  have hηR := AL.eta_hom hRy
  -- `R(ε_y ∘ L(g)) = R(ε_y) ∘ RL(g)`
  have t₁ := LC.comp_congr (LC.eqv_refl hη) (FR.ar_comp hLg hεy)
  -- `(R(ε_y) ∘ RL(g)) ∘ η_x = R(ε_y) ∘ (RL(g) ∘ η_x)`
  have t₂ := LC.assoc hη hRLg hRε
  -- naturality of the unit at `g`: `RL(g) ∘ η_x = η_{Ry} ∘ g`
  have t₃ := LC.comp_congr (LC.eqv_symm (AL.eta_nat hx hRy hg)) (LC.eqv_refl hRε)
  -- `R(ε_y) ∘ (η_{Ry} ∘ g) = (R(ε_y) ∘ η_{Ry}) ∘ g`
  have t₄ := LC.eqv_symm (LC.assoc hg hηR hRε)
  -- the right triangle
  have t₅ := LC.comp_congr (LC.eqv_refl hg) (AL.tri_right hy)
  have t₆ := LC.id_left hg
  exact LC.eqv_trans t₁ (LC.eqv_trans t₂ (LC.eqv_trans t₃ (LC.eqv_trans t₄ (LC.eqv_trans t₅ t₆))))

include LC FR AL in
/-- Naturality of `Φ` in the second variable: `Φ(b ∘ f) = R(b) ∘ Φ(f)`. -/
theorem phi_nat_right {x y y' f b : PTm n} (hx : Γ ⊢[PRAAx] C.obj x)
    (hf : Γ ⊢[PRAAx] D.hom (A.L.o x) y f) (hb : Γ ⊢[PRAAx] D.hom y y' b) :
    Γ ⊢[PRAAx] C.eqv x (A.R.o y') (A.Φ C x y' (D.comp (A.L.o x) y y' b f))
      (C.comp x (A.R.o y) (A.R.o y') (A.R.m y y' b) (A.Φ C x y f)) := by
  have hη := AL.eta_hom hx
  have t₁ := LC.comp_congr (LC.eqv_refl hη) (FR.ar_comp hf hb)
  have t₂ := LC.assoc hη (FR.ar_hom hf) (FR.ar_hom hb)
  exact LC.eqv_trans t₁ t₂

include LC FL FR AL in
/-- Naturality of `Φ` in the first variable: `Φ(f ∘ L(a)) = Φ(f) ∘ a`. -/
theorem phi_nat_left {x x' y f a : PTm n} (hx : Γ ⊢[PRAAx] C.obj x)
    (hx' : Γ ⊢[PRAAx] C.obj x') (ha : Γ ⊢[PRAAx] C.hom x' x a)
    (hf : Γ ⊢[PRAAx] D.hom (A.L.o x) y f) :
    Γ ⊢[PRAAx] C.eqv x' (A.R.o y)
      (A.Φ C x' y (D.comp (A.L.o x') (A.L.o x) y f (A.L.m x' x a)))
      (C.comp x' x (A.R.o y) (A.Φ C x y f) a) := by
  have hη := AL.eta_hom hx
  have hη' := AL.eta_hom hx'
  have hLa := FL.ar_hom ha
  have hRLa := FR.ar_hom hLa
  have hRf := FR.ar_hom hf
  -- `R(f ∘ L(a)) = R(f) ∘ RL(a)`
  have t₁ := LC.comp_congr (LC.eqv_refl hη') (FR.ar_comp hLa hf)
  -- `(R(f) ∘ RL(a)) ∘ η_{x'} = R(f) ∘ (RL(a) ∘ η_{x'})`
  have t₂ := LC.assoc hη' hRLa hRf
  -- naturality of the unit at `a`
  have t₃ := LC.comp_congr (LC.eqv_symm (AL.eta_nat hx' hx ha)) (LC.eqv_refl hRf)
  -- `R(f) ∘ (η_x ∘ a) = (R(f) ∘ η_x) ∘ a`
  have t₄ := LC.eqv_symm (LC.assoc ha hη hRf)
  exact LC.eqv_trans t₁ (LC.eqv_trans t₂ (LC.eqv_trans t₃ t₄))

end Correspondence

/-! ## Conversely: unit, counit and the triangles from supplied hom correspondences -/

/-- `Φ(x, y, f)` for a supplied correspondence term; variables `0 = x`, `1 = y`, `2 = f`. -/
def ap (t : PTm 3) {n : ℕ} (x y f : PTm n) : PTm n := Syn.subst ![x, y, f] t

/-- Supplied natural inverse hom correspondences `Φ : D(Lx, y) → C(x, Ry)` and
`Ψ : C(x, Ry) → D(Lx, y)` for functors `L : C → D` and `R : D → C`. -/
structure CorrLaws (C D : Pres) (L R : Fun) (phi psi : PTm 3) : Prop where
  phi_hom : ∀ {n : ℕ} {Γ : List (Fm PTm n)} {x y f : PTm n},
    (Γ ⊢[PRAAx] C.obj x) → (Γ ⊢[PRAAx] D.obj y) → (Γ ⊢[PRAAx] D.hom (L.o x) y f) →
      (Γ ⊢[PRAAx] C.hom x (R.o y) (ap phi x y f))
  psi_hom : ∀ {n : ℕ} {Γ : List (Fm PTm n)} {x y g : PTm n},
    (Γ ⊢[PRAAx] C.obj x) → (Γ ⊢[PRAAx] D.obj y) → (Γ ⊢[PRAAx] C.hom x (R.o y) g) →
      (Γ ⊢[PRAAx] D.hom (L.o x) y (ap psi x y g))
  phi_congr : ∀ {n : ℕ} {Γ : List (Fm PTm n)} {x y f f' : PTm n},
    (Γ ⊢[PRAAx] C.obj x) → (Γ ⊢[PRAAx] D.obj y) → (Γ ⊢[PRAAx] D.eqv (L.o x) y f f') →
      (Γ ⊢[PRAAx] C.eqv x (R.o y) (ap phi x y f) (ap phi x y f'))
  psi_congr : ∀ {n : ℕ} {Γ : List (Fm PTm n)} {x y g g' : PTm n},
    (Γ ⊢[PRAAx] C.obj x) → (Γ ⊢[PRAAx] D.obj y) → (Γ ⊢[PRAAx] C.eqv x (R.o y) g g') →
      (Γ ⊢[PRAAx] D.eqv (L.o x) y (ap psi x y g) (ap psi x y g'))
  psi_phi : ∀ {n : ℕ} {Γ : List (Fm PTm n)} {x y f : PTm n},
    (Γ ⊢[PRAAx] C.obj x) → (Γ ⊢[PRAAx] D.obj y) → (Γ ⊢[PRAAx] D.hom (L.o x) y f) →
      (Γ ⊢[PRAAx] D.eqv (L.o x) y (ap psi x y (ap phi x y f)) f)
  phi_psi : ∀ {n : ℕ} {Γ : List (Fm PTm n)} {x y g : PTm n},
    (Γ ⊢[PRAAx] C.obj x) → (Γ ⊢[PRAAx] D.obj y) → (Γ ⊢[PRAAx] C.hom x (R.o y) g) →
      (Γ ⊢[PRAAx] C.eqv x (R.o y) (ap phi x y (ap psi x y g)) g)
  phi_nat_right : ∀ {n : ℕ} {Γ : List (Fm PTm n)} {x y y' f b : PTm n},
    (Γ ⊢[PRAAx] C.obj x) → (Γ ⊢[PRAAx] D.obj y) → (Γ ⊢[PRAAx] D.obj y') →
    (Γ ⊢[PRAAx] D.hom (L.o x) y f) → (Γ ⊢[PRAAx] D.hom y y' b) →
      (Γ ⊢[PRAAx] C.eqv x (R.o y') (ap phi x y' (D.comp (L.o x) y y' b f))
        (C.comp x (R.o y) (R.o y') (R.m y y' b) (ap phi x y f)))
  phi_nat_left : ∀ {n : ℕ} {Γ : List (Fm PTm n)} {x x' y f a : PTm n},
    (Γ ⊢[PRAAx] C.obj x) → (Γ ⊢[PRAAx] C.obj x') → (Γ ⊢[PRAAx] D.obj y) →
    (Γ ⊢[PRAAx] C.hom x' x a) → (Γ ⊢[PRAAx] D.hom (L.o x) y f) →
      (Γ ⊢[PRAAx] C.eqv x' (R.o y) (ap phi x' y (D.comp (L.o x') (L.o x) y f (L.m x' x a)))
        (C.comp x' x (R.o y) (ap phi x y f) a))

section Converse

variable {C D : Pres} (LC : C.Laws) (LD : D.Laws) {L R : Fun} (FL : L.Laws C D)
  (FR : R.Laws D C) {phi psi : PTm 3} (K : CorrLaws C D L R phi psi)
  {n : ℕ} {Γ : List (Fm PTm n)}

/-- The unit `η_x = Φ(1_{Lx}) : x → RL(x)`. -/
def unit (D : Pres) (L : Fun) (phi : PTm 3) (x : PTm n) : PTm n :=
  ap phi x (L.o x) (D.id1 (L.o x))

/-- The counit `ε_y = Ψ(1_{Ry}) : LR(y) → y`. -/
def counit (C : Pres) (R : Fun) (psi : PTm 3) (y : PTm n) : PTm n :=
  ap psi (R.o y) y (C.id1 (R.o y))

include LD FL K in
theorem unit_hom {x : PTm n} (hx : Γ ⊢[PRAAx] C.obj x) :
    Γ ⊢[PRAAx] C.hom x (R.o (L.o x)) (unit D L phi x) :=
  K.phi_hom hx (FL.ob_obj hx) (LD.id_hom (FL.ob_obj hx))

include LC FR K in
theorem counit_hom {y : PTm n} (hy : Γ ⊢[PRAAx] D.obj y) :
    Γ ⊢[PRAAx] D.hom (L.o (R.o y)) y (counit C R psi y) :=
  K.psi_hom (FR.ob_obj hy) hy (LC.id_hom (FR.ob_obj hy))

include LC LD FL K in
/-- `Φ(f) = Φ(f ∘ 1_{Lx}) = R(f) ∘ η_x`. -/
theorem corr_phi_formula {x y f : PTm n} (hx : Γ ⊢[PRAAx] C.obj x) (hy : Γ ⊢[PRAAx] D.obj y)
    (hf : Γ ⊢[PRAAx] D.hom (L.o x) y f) :
    Γ ⊢[PRAAx] C.eqv x (R.o y) (ap phi x y f)
      (C.comp x (R.o (L.o x)) (R.o y) (R.m (L.o x) y f) (unit D L phi x)) := by
  have hLx := FL.ob_obj hx
  have t₁ := K.phi_congr hx hy (LD.eqv_symm (LD.id_right hf))
  have t₂ := K.phi_nat_right hx hLx hy (LD.id_hom hLx) hf
  exact LC.eqv_trans t₁ t₂

include LC LD FL K in
/-- Naturality of `Ψ` in the first variable, from that of `Φ`: `Ψ(g ∘ a) = Ψ(g) ∘ L(a)`. -/
theorem corr_psi_nat_left {x x' y g a : PTm n} (hx : Γ ⊢[PRAAx] C.obj x)
    (hx' : Γ ⊢[PRAAx] C.obj x') (hy : Γ ⊢[PRAAx] D.obj y) (ha : Γ ⊢[PRAAx] C.hom x' x a)
    (hg : Γ ⊢[PRAAx] C.hom x (R.o y) g) :
    Γ ⊢[PRAAx] D.eqv (L.o x') y (ap psi x' y (C.comp x' x (R.o y) g a))
      (D.comp (L.o x') (L.o x) y (ap psi x y g) (L.m x' x a)) := by
  have hΨg := K.psi_hom hx hy hg
  have hLa := FL.ar_hom ha
  have hc := LD.comp_hom hLa hΨg
  -- `Φ(Ψ(g) ∘ L(a)) = Φ(Ψ(g)) ∘ a = g ∘ a`
  have s₁ := K.phi_nat_left hx hx' hy ha hΨg
  have s₂ := LC.comp_congr (LC.eqv_refl ha) (K.phi_psi hx hy hg)
  have s := LC.eqv_trans s₁ s₂
  -- apply `Ψ` and use `Ψ ∘ Φ = 1`
  have t₁ := K.psi_congr hx' hy (LC.eqv_symm s)
  have t₂ := K.psi_phi hx' hy hc
  exact LD.eqv_trans t₁ t₂

include LC LD FR K in
/-- Naturality of `Ψ` in the second variable, from that of `Φ`: `Ψ(R(b) ∘ g) = b ∘ Ψ(g)`. -/
theorem corr_psi_nat_right {x y y' g b : PTm n} (hx : Γ ⊢[PRAAx] C.obj x)
    (hy : Γ ⊢[PRAAx] D.obj y) (hy' : Γ ⊢[PRAAx] D.obj y') (hg : Γ ⊢[PRAAx] C.hom x (R.o y) g)
    (hb : Γ ⊢[PRAAx] D.hom y y' b) :
    Γ ⊢[PRAAx] D.eqv (L.o x) y' (ap psi x y' (C.comp x (R.o y) (R.o y') (R.m y y' b) g))
      (D.comp (L.o x) y y' b (ap psi x y g)) := by
  have hΨg := K.psi_hom hx hy hg
  have hc := LD.comp_hom hΨg hb
  -- `Φ(b ∘ Ψ(g)) = R(b) ∘ Φ(Ψ(g)) = R(b) ∘ g`
  have s₁ := K.phi_nat_right hx hy hy' hΨg hb
  have s₂ := LC.comp_congr (K.phi_psi hx hy hg) (LC.eqv_refl (FR.ar_hom hb))
  have s := LC.eqv_trans s₁ s₂
  have t₁ := K.psi_congr hx hy' (LC.eqv_symm s)
  have t₂ := K.psi_phi hx hy' hc
  exact LD.eqv_trans t₁ t₂

include LC LD FL FR K in
/-- `Ψ(g) = Ψ(1_{Ry} ∘ g) = ε_y ∘ L(g)`. -/
theorem corr_psi_formula {x y g : PTm n} (hx : Γ ⊢[PRAAx] C.obj x) (hy : Γ ⊢[PRAAx] D.obj y)
    (hg : Γ ⊢[PRAAx] C.hom x (R.o y) g) :
    Γ ⊢[PRAAx] D.eqv (L.o x) y (ap psi x y g)
      (D.comp (L.o x) (L.o (R.o y)) y (counit C R psi y) (L.m x (R.o y) g)) := by
  have hRy := FR.ob_obj hy
  have t₁ := K.psi_congr hx hy (LC.eqv_symm (LC.id_left hg))
  have t₂ := corr_psi_nat_left LC LD FL K hRy hx hy hg (LC.id_hom hRy)
  exact LD.eqv_trans t₁ t₂

include LC LD FL FR K in
/-- The left triangle: `ε_{Lx} ∘ L(η_x) = Ψ(η_x) = Ψ(Φ(1_{Lx})) = 1_{Lx}`. -/
theorem corr_tri_left {x : PTm n} (hx : Γ ⊢[PRAAx] C.obj x) :
    Γ ⊢[PRAAx] D.eqv (L.o x) (L.o x)
      (D.comp (L.o x) (L.o (R.o (L.o x))) (L.o x) (counit C R psi (L.o x))
        (L.m x (R.o (L.o x)) (unit D L phi x)))
      (D.id1 (L.o x)) := by
  have hLx := FL.ob_obj hx
  have t₁ := LD.eqv_symm (corr_psi_formula LC LD FL FR K hx hLx (unit_hom LD FL K hx))
  have t₂ := K.psi_phi hx hLx (LD.id_hom hLx)
  exact LD.eqv_trans t₁ t₂

include LC LD FL FR K in
/-- The right triangle: `R(ε_y) ∘ η_{Ry} = Φ(ε_y) = Φ(Ψ(1_{Ry})) = 1_{Ry}`. -/
theorem corr_tri_right {y : PTm n} (hy : Γ ⊢[PRAAx] D.obj y) :
    Γ ⊢[PRAAx] C.eqv (R.o y) (R.o y)
      (C.comp (R.o y) (R.o (L.o (R.o y))) (R.o y) (R.m (L.o (R.o y)) y (counit C R psi y))
        (unit D L phi (R.o y)))
      (C.id1 (R.o y)) := by
  have hRy := FR.ob_obj hy
  have t₁ := LC.eqv_symm (corr_phi_formula LC LD FL K hRy hy (counit_hom LC FR K hy))
  have t₂ := K.phi_psi hRy hy (LC.id_hom hRy)
  exact LC.eqv_trans t₁ t₂

include LC LD FL K in
/-- Naturality of the unit: `η_x ∘ a = Φ(1_{Lx} ∘ L(a)) = Φ(L(a) ∘ 1_{Lx'}) = RL(a) ∘ η_{x'}`
for `a : x' → x`. -/
theorem corr_eta_nat {x x' a : PTm n} (hx : Γ ⊢[PRAAx] C.obj x) (hx' : Γ ⊢[PRAAx] C.obj x')
    (ha : Γ ⊢[PRAAx] C.hom x' x a) :
    Γ ⊢[PRAAx] C.eqv x' (R.o (L.o x)) (C.comp x' x (R.o (L.o x)) (unit D L phi x) a)
      (C.comp x' (R.o (L.o x')) (R.o (L.o x)) (R.m (L.o x') (L.o x) (L.m x' x a))
        (unit D L phi x')) := by
  have hLx := FL.ob_obj hx
  have hLx' := FL.ob_obj hx'
  have hLa := FL.ar_hom ha
  -- `η_x ∘ a = Φ(1_{Lx} ∘ L(a))`
  have t₁ := LC.eqv_symm (K.phi_nat_left hx hx' hLx ha (LD.id_hom hLx))
  -- `1_{Lx} ∘ L(a) = L(a) = L(a) ∘ 1_{Lx'}`
  have e := LD.eqv_trans (LD.id_left hLa) (LD.eqv_symm (LD.id_right hLa))
  have t₂ := K.phi_congr hx' hLx e
  -- `Φ(L(a) ∘ 1_{Lx'}) = RL(a) ∘ Φ(1_{Lx'})`
  have t₃ := K.phi_nat_right hx' hLx' hLx (LD.id_hom hLx') hLa
  exact LC.eqv_trans t₁ (LC.eqv_trans t₂ t₃)

include LC LD FL FR K in
/-- Naturality of the counit: `b ∘ ε_y = Ψ(R(b) ∘ 1_{Ry}) = Ψ(1_{Ry'} ∘ R(b)) = ε_{y'} ∘ LR(b)`
for `b : y → y'`. -/
theorem corr_eps_nat {y y' b : PTm n} (hy : Γ ⊢[PRAAx] D.obj y) (hy' : Γ ⊢[PRAAx] D.obj y')
    (hb : Γ ⊢[PRAAx] D.hom y y' b) :
    Γ ⊢[PRAAx] D.eqv (L.o (R.o y)) y' (D.comp (L.o (R.o y)) y y' b (counit C R psi y))
      (D.comp (L.o (R.o y)) (L.o (R.o y')) y' (counit C R psi y')
        (L.m (R.o y) (R.o y') (R.m y y' b))) := by
  have hRy := FR.ob_obj hy
  have hRy' := FR.ob_obj hy'
  have hRb := FR.ar_hom hb
  -- `b ∘ ε_y = Ψ(R(b) ∘ 1_{Ry})`
  have t₁ := LD.eqv_symm (corr_psi_nat_right LC LD FR K hRy hy hy' (LC.id_hom hRy) hb)
  -- `R(b) ∘ 1_{Ry} = R(b) = 1_{Ry'} ∘ R(b)`
  have e := LC.eqv_trans (LC.id_right hRb) (LC.eqv_symm (LC.id_left hRb))
  have t₂ := K.psi_congr hRy hy' e
  -- `Ψ(1_{Ry'} ∘ R(b)) = Ψ(1_{Ry'}) ∘ L(R(b))`
  have t₃ := corr_psi_nat_left LC LD FL K hRy' hRy hy' hRb (LC.id_hom hRy')
  exact LD.eqv_trans t₁ (LD.eqv_trans t₂ t₃)

end Converse

/-! ## An instance: the Galois connection `2x ≤ y ↔ x ≤ ⌊y / 2⌋` -/

section Galois

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The preorder `(ℕ, ≤)` as a thin category: every number is an object, there is an arrow
`a → b` (with any code) exactly when `a ≤ b`, and parallel arrows are equal. -/
def natLe : Pres where
  Obj := (zero : PTm 1) ≐ zero
  Hom := le (var 0 : PTm 3) (var 1)
  Eqv := (zero : PTm 4) ≐ zero
  idt := zero
  cmp := zero

theorem natLe_obj (a : PTm n) : natLe.obj a = ((zero : PTm n) ≐ zero) := by
  simp [Pres.obj, natLe]

theorem natLe_hom (a b f : PTm n) : natLe.hom a b f = le a b := by
  simp [Pres.hom, natLe, le]

theorem natLe_eqv (a b f g : PTm n) : natLe.eqv a b f g = ((zero : PTm n) ≐ zero) := by
  simp [Pres.eqv, natLe]

theorem natLe_laws : natLe.Laws where
  eqv_refl := fun _ => by rw [natLe_eqv]; exact .eqRefl _
  eqv_symm := fun _ => by rw [natLe_eqv]; exact .eqRefl _
  eqv_trans := fun _ _ => by rw [natLe_eqv]; exact .eqRefl _
  id_hom := fun _ => by rw [natLe_hom]; exact le_refl _
  comp_hom := fun h₁ h₂ => by rw [natLe_hom] at h₁ h₂ ⊢; exact le_trans h₁ h₂
  comp_congr := fun _ _ => by rw [natLe_eqv]; exact .eqRefl _
  assoc := fun _ _ _ => by rw [natLe_eqv]; exact .eqRefl _
  id_left := fun _ => by rw [natLe_eqv]; exact .eqRefl _
  id_right := fun _ => by rw [natLe_eqv]; exact .eqRefl _

/-- `par b ≤ 1`. -/
theorem par_le_one (b : PTm n) : Γ ⊢[PRAAx] le (par b) one := by
  refine .orE (par_cases b) ?_ ?_
  · exact le_congr (Prf.hyp0 (φ := par b ≐ zero)).eqSymm (.eqRefl _) (zero_le one)
  · exact le_congr (Prf.hyp0 (φ := par b ≐ one)).eqSymm (.eqRefl _) (le_refl one)

private theorem mono_aux {a b ha hb pa pb : PTm n} (ea : Γ ⊢[PRAAx] a ≐ two * ha + pa)
    (eb : Γ ⊢[PRAAx] b ≐ two * hb + pb) (h : Γ ⊢[PRAAx] le a b) (hp : Γ ⊢[PRAAx] le pb one)
    (hlt : Γ ⊢[PRAAx] le (succ hb) ha) :
    Γ ⊢[PRAAx] le (succ (two * hb + one)) (two * hb + one) := by
  have e₁ := natEq ea; have e₂ := natEq eb
  have e₃ := natEq (eq_add_of_le h); have e₄ := natEq (eq_add_of_le hp)
  have e₅ := natEq (eq_add_of_le hlt)
  refine le_of_eq_add
    (d := monus b a + monus one pb + two * monus ha (succ hb) + pa) ?_
  apply deriveNat; ipra_simps
  linear_combination e₁ - e₂ + e₃ + e₄ + 2 * e₅

/-- Halving is monotone. -/
theorem half_mono {a b : PTm n} (h : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx] le (half a) (half b) := by
  refine .orE (lt_or_le (half b) (half a)) ?_ Prf.hyp0
  exact not_succ_le_self (two * half b + one) _
    (mono_aux (half_par a) (half_par b) h.wk (par_le_one b) Prf.hyp0)

/-- Doubling is monotone. -/
theorem double_mono {a b : PTm n} (h : Γ ⊢[PRAAx] le a b) :
    Γ ⊢[PRAAx] le (two * a) (two * b) := by
  have e := natEq (eq_add_of_le h)
  refine le_of_eq_add (d := two * monus b a) ?_
  apply deriveNat; ipra_simps
  linear_combination 2 * e

/-- `x ≤ ⌊2x / 2⌋`. -/
theorem le_half_double (x : PTm n) : Γ ⊢[PRAAx] le x (half (two * x)) := by
  -- `2x = 2 ⌊2x/2⌋ + par(2x)` with `par(2x) = 0`
  have e₁ := natEq (half_par (Γ := Γ) (two * x)); have e₂ := natEq (par_double (Γ := Γ) x)
  refine .orE (lt_or_le (half (two * x)) x) ?_ Prf.hyp0
  have e₃ := natEq (eq_add_of_le (Prf.hyp0 (Γ := Γ) (φ := lt (half (two * x)) x)))
  have e₁' := natEq (half_par (Γ := lt (half (two * x)) x :: Γ) (two * x))
  have e₂' := natEq (par_double (Γ := lt (half (two * x)) x :: Γ) x)
  refine not_succ_le_self (two * x) _ (le_of_eq_add
    (d := succ zero + two * monus x (succ (half (two * x)))) ?_)
  apply deriveNat; ipra_simps
  linear_combination -e₁' - e₂' + 2 * e₃

/-- `2 ⌊y / 2⌋ ≤ y`. -/
theorem double_half_le (y : PTm n) : Γ ⊢[PRAAx] le (two * half y) y :=
  le_of_eq_add (half_par y)

/-- The left adjoint `x ↦ 2x`. -/
def dbl : Fun where
  ob := two * (var 0 : PTm 1)
  ar := zero

/-- The right adjoint `y ↦ ⌊y / 2⌋`. -/
def hlf : Fun where
  ob := half (var 0 : PTm 1)
  ar := zero

theorem dbl_o (a : PTm n) : dbl.o a = two * a := by simp [Fun.o, dbl]

theorem hlf_o (a : PTm n) : hlf.o a = half a := by simp [Fun.o, hlf]

theorem dbl_laws : dbl.Laws natLe natLe where
  ob_obj := fun _ => by rw [natLe_obj]; exact .eqRefl _
  ar_hom := fun h => by
    rw [natLe_hom] at h ⊢; rw [dbl_o, dbl_o]
    exact double_mono h
  ar_congr := fun _ => by rw [natLe_eqv]; exact .eqRefl _
  ar_id := fun _ => by rw [natLe_eqv]; exact .eqRefl _
  ar_comp := fun _ _ => by rw [natLe_eqv]; exact .eqRefl _

theorem hlf_laws : hlf.Laws natLe natLe where
  ob_obj := fun _ => by rw [natLe_obj]; exact .eqRefl _
  ar_hom := fun h => by
    rw [natLe_hom] at h ⊢; rw [hlf_o, hlf_o]
    exact half_mono h
  ar_congr := fun _ => by rw [natLe_eqv]; exact .eqRefl _
  ar_id := fun _ => by rw [natLe_eqv]; exact .eqRefl _
  ar_comp := fun _ _ => by rw [natLe_eqv]; exact .eqRefl _

/-- Doubling is left adjoint to halving. -/
def galois : Adj where
  L := dbl
  R := hlf
  eta := zero
  eps := zero

theorem galois_laws : galois.Laws natLe natLe where
  eta_hom := fun _ => by
    rw [natLe_hom]
    show _ ⊢[PRAAx] le _ (hlf.o (dbl.o _))
    rw [dbl_o, hlf_o]
    exact le_half_double _
  eta_nat := fun _ _ _ => by rw [natLe_eqv]; exact .eqRefl _
  eps_hom := fun _ => by
    rw [natLe_hom]
    show _ ⊢[PRAAx] le (dbl.o (hlf.o _)) _
    rw [hlf_o, dbl_o]
    exact double_half_le _
  eps_nat := fun _ _ _ => by rw [natLe_eqv]; exact .eqRefl _
  tri_left := fun _ => by rw [natLe_eqv]; exact .eqRefl _
  tri_right := fun _ => by rw [natLe_eqv]; exact .eqRefl _

/-- `2x ≤ y → x ≤ ⌊y / 2⌋`: the typing of `Φ` for this adjunction. -/
theorem galois_phi {x y : PTm n} (h : Γ ⊢[PRAAx] le (two * x) y) :
    Γ ⊢[PRAAx] le x (half y) := by
  have hx : Γ ⊢[PRAAx] natLe.obj x := by rw [natLe_obj]; exact .eqRefl _
  have hf : Γ ⊢[PRAAx] natLe.hom (galois.L.o x) y zero := by
    rw [natLe_hom]
    show _ ⊢[PRAAx] le (dbl.o x) y
    rw [dbl_o]; exact h
  have r := phi_hom natLe_laws hlf_laws galois_laws hx hf
  rw [natLe_hom] at r
  have e : galois.R.o y = half y := hlf_o y
  rw [e] at r
  exact r

/-- `x ≤ ⌊y / 2⌋ → 2x ≤ y`: the typing of `Ψ` for this adjunction. -/
theorem galois_psi {x y : PTm n} (h : Γ ⊢[PRAAx] le x (half y)) :
    Γ ⊢[PRAAx] le (two * x) y := by
  have hy : Γ ⊢[PRAAx] natLe.obj y := by rw [natLe_obj]; exact .eqRefl _
  have hg : Γ ⊢[PRAAx] natLe.hom x (galois.R.o y) zero := by
    rw [natLe_hom]
    show _ ⊢[PRAAx] le x (hlf.o y)
    rw [hlf_o]; exact h
  have r := psi_hom natLe_laws dbl_laws galois_laws hy hg
  rw [natLe_hom] at r
  have e : galois.L.o x = two * x := dbl_o x
  rw [e] at r
  exact r

/-- The Galois connection as one closed sentence of iPRA: for all `x`, `y`,
`(2x ≤ y → x ≤ ⌊y / 2⌋) ∧ (x ≤ ⌊y / 2⌋ → 2x ≤ y)`. Variables: `0 = x`, `1 = y`. -/
theorem galois_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((le (two * (var 0 : PTm 2)) (var 1) ⟶ le (var 0) (half (var 1))) ⋏
      (le (var 0 : PTm 2) (half (var 1)) ⟶ le (two * (var 0)) (var 1))) :=
  closeUniv 2 (.andI (.impI (galois_phi Prf.hyp0)) (.impI (galois_psi Prf.hyp0)))

end Galois

end LeanProofs.IPRA.Foundations.Adjunction
