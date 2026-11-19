import IPRADerivations.Foundations.FormalDerivation

/-!
# Renaming the variables of polynomial expressions and of their fractions

A reusable piece of the embedding framework: two calculations carried out in different lists of
indeterminates are compared in one sentence by renaming their variables into a common list
(used for `geometry/four_metrics_ipra_2026-11-15`, where the Ricci tensor is computed in the
indeterminates `r, x, a, d, v, w` and the Maxwell stress tensor in `r, x, a, d, q`).

* `ZExp.rename f`: the expression with variable `i` replaced by variable `f i`; it commutes
  with the operations (`rename_add`, `rename_mul`, `rename_neg`, `rename_sub`, `rename_pow`);
* `ZExp.eval_rename`: the value of a renamed expression under `ρ` is the value of the
  expression under `ρ ∘ f`;
* `ZExp.der_rename`: a derivation commutes with a renaming whenever it does on the variables;
* `ZExp.Frac.rename f`: the same for fractions, compatible with `+`, `*`, `−`, the embedding,
  the half, the quotient rule (`Frac.rename_d`) and the cleared equation (`Frac.rename_eqn`);
* `ZExp.derive_imp_rename`: an implication between polynomial equations certified in every
  commutative ring stays a theorem of iPRA after any renaming of its variables (the renaming
  need not be injective: it may identify variables).
-/

namespace LeanProofs.IPRA

open LeanProofs.ConciseIPRA

namespace ZExp

variable {k n : ℕ}

/-- The expression with variable `i` replaced by variable `f i`. -/
def rename (f : Fin k → Fin n) : ZExp k → ZExp n
  | var i => var (f i)
  | lit c => lit c
  | add a b => add (rename f a) (rename f b)
  | mul a b => mul (rename f a) (rename f b)
  | neg a => neg (rename f a)

section Rules

variable (f : Fin k → Fin n) (a b : ZExp k)

@[simp] theorem rename_var (i : Fin k) : rename f (var i) = var (f i) := rfl
@[simp] theorem rename_add : rename f (a + b) = rename f a + rename f b := rfl
@[simp] theorem rename_mul : rename f (a * b) = rename f a * rename f b := rfl
@[simp] theorem rename_neg : rename f (-a) = -rename f a := rfl
@[simp] theorem rename_sub : rename f (a - b) = rename f a - rename f b := rfl
@[simp] theorem rename_ofNat (c : ℕ) :
    rename f (OfNat.ofNat c : ZExp k) = (OfNat.ofNat c : ZExp n) := rfl

@[simp] theorem rename_pow (m : ℕ) : rename f (a ^ m) = rename f a ^ m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    show rename f (pow a m) * rename f a = pow (rename f a) m * rename f a
    have ih' : rename f (pow a m) = pow (rename f a) m := ih
    rw [ih']

/-- The value of a renamed expression. -/
theorem eval_rename {R : Type} [CommRing R] (ρ : Fin n → R) (e : ZExp k) :
    eval ρ (rename f e) = eval (fun i => ρ (f i)) e := by
  induction e with
  | var i => rfl
  | lit c => rfl
  | add a b iha ihb =>
    show eval ρ (rename f a) + eval ρ (rename f b) = _
    rw [iha, ihb]; rfl
  | mul a b iha ihb =>
    show eval ρ (rename f a) * eval ρ (rename f b) = _
    rw [iha, ihb]; rfl
  | neg a iha =>
    show -eval ρ (rename f a) = _
    rw [iha]; rfl

/-- A derivation commutes with a renaming whenever it does on the variables. -/
theorem der_rename (δ : Fin k → ZExp k) (δ' : Fin n → ZExp n)
    (hδ : ∀ i, δ' (f i) = rename f (δ i)) (e : ZExp k) :
    der δ' (rename f e) = rename f (der δ e) := by
  induction e with
  | var i => exact hδ i
  | lit c => rfl
  | add a b iha ihb =>
    show der δ' (rename f a) + der δ' (rename f b) = rename f (der δ a) + rename f (der δ b)
    rw [iha, ihb]
  | mul a b iha ihb =>
    show der δ' (rename f a) * rename f b + rename f a * der δ' (rename f b)
      = rename f (der δ a) * rename f b + rename f a * rename f (der δ b)
    rw [iha, ihb]
  | neg a iha =>
    show -der δ' (rename f a) = -rename f (der δ a)
    rw [iha]

end Rules

namespace Frac

/-- The fraction with variable `i` replaced by variable `f i`. -/
def rename (f : Fin k → Fin n) (g : Frac k) : Frac n := ⟨ZExp.rename f g.num, ZExp.rename f g.den⟩

section Rules

variable (f : Fin k → Fin n) (g h : Frac k) (e : ZExp k)

@[simp] theorem rename_num : (rename f g).num = ZExp.rename f g.num := rfl
@[simp] theorem rename_den : (rename f g).den = ZExp.rename f g.den := rfl
theorem rename_add : rename f (g + h) = rename f g + rename f h := rfl
theorem rename_mul : rename f (g * h) = rename f g * rename f h := rfl
theorem rename_neg : rename f (-g) = -rename f g := rfl
theorem rename_sub : rename f (g - h) = rename f g - rename f h := rfl
theorem rename_ofZ : rename f (ofZ e) = ofZ (ZExp.rename f e) := rfl
theorem rename_half : rename f (half g) = half (rename f g) := rfl

/-- The cleared equation of renamed fractions is the renamed cleared equation. -/
theorem rename_eqn :
    eqn (rename f g) (rename f h) = (ZExp.rename f (eqn g h).1, ZExp.rename f (eqn g h).2) := rfl

/-- The quotient rule commutes with a renaming whenever the derivation does on the variables. -/
theorem rename_d (δ : Fin k → ZExp k) (δ' : Fin n → ZExp n)
    (hδ : ∀ i, δ' (f i) = ZExp.rename f (δ i)) :
    d δ' (rename f g) = rename f (d δ g) := by
  show (⟨der δ' (ZExp.rename f g.num) * ZExp.rename f g.den
      - ZExp.rename f g.num * der δ' (ZExp.rename f g.den),
      ZExp.rename f g.den * ZExp.rename f g.den⟩ : Frac n) = _
  rw [der_rename f δ δ' hδ, der_rename f δ δ' hδ]
  rfl

end Rules

end Frac

/-! ## Renaming a certified implication -/

/-- A pair of expressions, renamed. -/
def renameEq (f : Fin k → Fin n) (c : ZExp k × ZExp k) : ZExp n × ZExp n :=
  (rename f c.1, rename f c.2)

theorem holds_rename {R : Type} [CommRing R] (f : Fin k → Fin n) (ρ : Fin n → R)
    (hyps : List (ZExp k × ZExp k)) :
    Holds ρ (hyps.map (renameEq f)) ↔ Holds (fun i => ρ (f i)) hyps := by
  induction hyps with
  | nil => exact Iff.rfl
  | cons c t ih =>
    show (eval ρ (rename f c.1) = eval ρ (rename f c.2) ∧ Holds ρ (t.map (renameEq f)))
      ↔ (eval (fun i => ρ (f i)) c.1 = eval (fun i => ρ (f i)) c.2 ∧ Holds (fun i => ρ (f i)) t)
    rw [eval_rename, eval_rename, ih]

/-- An implication between polynomial equations certified in every commutative ring stays
derivable in iPRA after any renaming of its variables. -/
theorem derive_imp_rename (f : Fin k → Fin n) (hyps : List (ZExp k × ZExp k))
    (c : ZExp k × ZExp k)
    (cert : ∀ (R : Type) [CommRing R] (ρ : Fin k → R), Holds ρ hyps → eval ρ c.1 = eval ρ c.2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * n) (imp (hyps.map (renameEq f)) (renameEq f c)) :=
  derive_imp _ _ (fun R _ ρ h => by
    show eval ρ (rename f c.1) = eval ρ (rename f c.2)
    rw [eval_rename, eval_rename]
    exact cert R (fun i => ρ (f i)) ((holds_rename f ρ hyps).1 h))

end ZExp

end LeanProofs.IPRA
