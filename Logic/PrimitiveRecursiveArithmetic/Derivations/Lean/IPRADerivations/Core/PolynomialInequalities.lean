import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.PolynomialImplications

/-!
# Implications between integer polynomial equations and inequalities

`Core/PolynomialImplications` derives implications between polynomial *equations* from a
certificate valid in every commutative ring. This module adds inequalities. The statements have
the form

  `r₁ → … → r_m → r`,

where each `r` is an equation `a = b` or an inequality `a ≤ b` between integer polynomials
(`ZExp.Rel`). The certificate is a Positivstellensatz-style argument: it must hold in every
commutative ring `R` with a *cone* `C` (`Cone R`: a subset containing `0`, `1`, closed under
`+` and `*`, and containing all squares), `a ≤ b` being read as `b − a ∈ C`.

* `Cone R`, with `Cone.natCast`, `Cone.ofNat`, `Cone.pow_two`, `Cone.pow`;
* `nn_sq`: in the ring of differences `Groth (Q Γ)`, every square is the value of a term
  (`(p − q)² = (p ∸ q)² + (q ∸ p)²`), so the `Nonneg` elements of `Core/OrderCertificates` form a
  cone `nnCone Γ`;
* `ZExp.leF a b`: the quantifier-free iPRA formula for the integer inequality `a ≤ b`, the
  natural-number inequality `a⁺ + b⁻ ≤ b⁺ + a⁻` between the parts of the two integer terms;
* `ZExp.impR hyps c` and `ZExp.derive_rel`: if in every commutative ring with a cone and for
  every valuation the hypotheses give the conclusion, then
  `[] ⊢[PRAAx] univ (2k) (impR hyps c)`.

A certificate typically rewrites the slack of the conclusion as a sum of products of slacks of
the hypotheses and squares (by `ring` or `linear_combination` with the equational hypotheses)
and closes the membership by `cone_mem`. The tactic `ipra_cone R C ρ h` opens a certificate.

The cone is not assumed total or antisymmetric: no case distinction on signs is available
through this layer.
-/

namespace LeanProofs.IPRA

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open PTm (pred monus)

/-- A cone of a commutative ring: it contains `0` and `1`, is closed under addition and
multiplication, and contains every square. -/
structure Cone (R : Type) [CommRing R] where
  mem : R → Prop
  zero : mem 0
  one : mem 1
  add : ∀ {a b : R}, mem a → mem b → mem (a + b)
  mul : ∀ {a b : R}, mem a → mem b → mem (a * b)
  sq : ∀ a : R, mem (a * a)

namespace Cone

variable {R : Type} [CommRing R] (C : Cone R)

/-- Membership transported along an equation: the usual last step of a certificate. -/
theorem of_eq {a b : R} (h : C.mem a) (e : b = a) : C.mem b := e ▸ h

theorem natCast (k : ℕ) : C.mem (k : R) := by
  induction k with
  | zero => rw [Nat.cast_zero]; exact C.zero
  | succ k ih => rw [Nat.cast_succ]; exact C.add ih C.one

theorem ofNat (k : ℕ) [k.AtLeastTwo] : C.mem (OfNat.ofNat k : R) := by
  have h : ((OfNat.ofNat k : ℕ) : R) = OfNat.ofNat k := Nat.cast_ofNat
  rw [← h]
  exact C.natCast _

theorem pow_two (a : R) : C.mem (a ^ 2) := by
  rw [_root_.pow_two]
  exact C.sq a

theorem pow {a : R} (h : C.mem a) (k : ℕ) : C.mem (a ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact C.one
  | succ k ih => rw [pow_succ]; exact C.mul ih h

end Cone

/-! ## The cone of the ring of differences -/

section NN

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- A square in the ring of differences is the value of a term. -/
theorem nn_sq (z : Groth (Q Γ)) : Nonneg Γ (z * z) := by
  refine Groth.ind (fun a b => ?_) z
  refine Q.ind (fun p => ?_) a
  refine Q.ind (fun q => ?_) b
  refine ⟨monus p q * monus p q + monus q p * monus q p, ?_⟩
  have e₁ := natEq (monus_max (Γ := Γ) p q)
  have e₂ := natEq (monus_mul (Γ := Γ) p q)
  simp only [Q.mk_add, Q.mk_mul, Q.mk_zero, map_add, map_mul, map_zero] at e₁ e₂ ⊢
  rw [Groth.mk_eq_sub]
  linear_combination (-(Groth.ι (Q.mk Γ p) - Groth.ι (Q.mk Γ q) + Groth.ι (Q.mk Γ (monus p q)) -
    Groth.ι (Q.mk Γ (monus q p)))) * e₁ - 2 * e₂

/-- The cone of the values of terms. -/
def nnCone (Γ : List (Fm PTm n)) : Cone (Groth (Q Γ)) where
  mem := Nonneg Γ
  zero := nn_zero
  one := nn_one
  add := nn_add
  mul := nn_mul
  sq := nn_sq

end NN

namespace ZExp

variable {k : ℕ}

/-- An equation or an inequality between two expressions. -/
inductive Rel (k : ℕ) : Type
  | eq (a b : ZExp k) : Rel k
  | le (a b : ZExp k) : Rel k

/-- The integer inequality `a ≤ b`, as a quantifier-free iPRA formula. -/
def leF (a b : ZExp k) : Fm PTm (2 * k) :=
  LeanProofs.IPRA.le ((toZT a).pos + (toZT b).neg) ((toZT b).pos + (toZT a).neg)

/-- The iPRA formula of a relation. -/
def Rel.fm : Rel k → Fm PTm (2 * k)
  | .eq a b => eqF a b
  | .le a b => leF a b

section Sem

variable {R : Type} [CommRing R] (C : Cone R) (ρ : Fin k → R)

/-- The relation holds under the valuation, with `a ≤ b` read as `b − a ∈ C`. -/
def Rel.holds : Rel k → Prop
  | .eq a b => eval ρ a = eval ρ b
  | .le a b => C.mem (eval ρ b - eval ρ a)

@[simp] theorem Rel.holds_eq (a b : ZExp k) :
    (Rel.eq a b).holds C ρ = (eval ρ a = eval ρ b) := rfl
@[simp] theorem Rel.holds_le (a b : ZExp k) :
    (Rel.le a b).holds C ρ = C.mem (eval ρ b - eval ρ a) := rfl

/-- All the listed relations hold. -/
def HoldsR : List (Rel k) → Prop
  | [] => True
  | h :: t => h.holds C ρ ∧ HoldsR t

@[simp] theorem holdsR_nil : HoldsR C ρ ([] : List (Rel k)) = True := rfl
@[simp] theorem holdsR_cons (h : Rel k) (t : List (Rel k)) :
    HoldsR C ρ (h :: t) = (h.holds C ρ ∧ HoldsR C ρ t) := rfl

end Sem

/-- The formula `r₁ → … → r_m → r`. -/
def impR (hyps : List (Rel k)) (c : Rel k) : Fm PTm (2 * k) :=
  hyps.foldr (fun h φ => h.fm ⟶ φ) c.fm

theorem impR_nil (c : Rel k) : impR [] c = c.fm := rfl

theorem impR_cons (h : Rel k) (t : List (Rel k)) (c : Rel k) :
    impR (h :: t) c = (h.fm ⟶ impR t c) := rfl

section Bridge

variable {Γ : List (Fm PTm (2 * k))}

private theorem slack_eq (a b : ZExp k) :
    Groth.ι (Q.mk Γ ((toZT b).pos + (toZT a).neg)) - Groth.ι (Q.mk Γ ((toZT a).pos + (toZT b).neg)) =
      eval (val Γ) b - eval (val Γ) a := by
  rw [← toZ_toZT, ← toZ_toZT]
  simp only [ZT.toZ, Q.mk_add, map_add]
  ring

theorem holds_of_fm (r : Rel k) (h : Γ ⊢[PRAAx] r.fm) : r.holds (nnCone Γ) (val Γ) := by
  cases r with
  | eq a b =>
    show eval (val Γ) a = eval (val Γ) b
    rw [← toZ_toZT, ← toZ_toZT]
    exact ZT.toZ_eq h
  | le a b =>
    show Nonneg Γ (eval (val Γ) b - eval (val Γ) a)
    have hs := nn_sl (Γ := Γ) (a := (toZT a).pos + (toZT b).neg) (b := (toZT b).pos + (toZT a).neg) h
    rw [sl_def, slack_eq] at hs
    exact hs

theorem fm_of_holds (r : Rel k) (h : r.holds (nnCone Γ) (val Γ)) : Γ ⊢[PRAAx] r.fm := by
  cases r with
  | eq a b =>
    refine ZT.derive ?_
    rw [toZ_toZT, toZ_toZT]
    exact h
  | le a b =>
    refine le_of_nonneg ?_
    rw [slack_eq]
    exact h

end Bridge

/-- The open form, with the hypotheses already assumed collected in `done`. -/
theorem derive_rel_open (c : Rel k) :
    ∀ (hyps done : List (Rel k)) (Γ : List (Fm PTm (2 * k))),
      (∀ h ∈ done, Γ ⊢[PRAAx] h.fm) →
      (∀ (R : Type) [CommRing R] (C : Cone R) (ρ : Fin k → R), (∀ h ∈ done, h.holds C ρ) →
        HoldsR C ρ hyps → c.holds C ρ) →
      (Γ ⊢[PRAAx] impR hyps c)
  | [], done, Γ, hd, cert => by
    rw [impR_nil]
    exact fm_of_holds c (cert _ (nnCone Γ) (val Γ) (fun h hh => holds_of_fm h (hd h hh)) trivial)
  | h :: t, done, Γ, hd, cert => by
    rw [impR_cons]
    refine .impI (derive_rel_open c t (h :: done) _ ?_ ?_)
    · intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact Prf.hyp0
      · exact (hd g hg).wk
    · intro R _ C ρ hdone ht
      exact cert R C ρ (fun g hg => hdone g (List.mem_cons_of_mem _ hg))
        ⟨hdone h List.mem_cons_self, ht⟩

/-- An implication between integer polynomial equations and inequalities that holds in every
commutative ring with a cone is a theorem of iPRA, universally closed over its `2k`
natural-number variables. -/
theorem derive_rel (hyps : List (Rel k)) (c : Rel k)
    (cert : ∀ (R : Type) [CommRing R] (C : Cone R) (ρ : Fin k → R), HoldsR C ρ hyps → c.holds C ρ) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * k) (impR hyps c) :=
  closeUniv (2 * k) (derive_rel_open c hyps [] [] (fun _ hh => nomatch hh)
    (fun R _ C ρ _ h => cert R C ρ h))

end ZExp

end LeanProofs.IPRA

/-- Prove a membership `C.mem e` in a cone for `e` built from hypotheses, numerals and squares by
`+`, `*` and natural powers. -/
macro "cone_mem" : tactic =>
  `(tactic| repeat (first
      | assumption
      | exact LeanProofs.IPRA.Cone.zero _
      | exact LeanProofs.IPRA.Cone.one _
      | exact LeanProofs.IPRA.Cone.sq _ _
      | exact LeanProofs.IPRA.Cone.pow_two _ _
      | exact LeanProofs.IPRA.Cone.ofNat _ _
      | exact LeanProofs.IPRA.Cone.natCast _ _
      | apply LeanProofs.IPRA.Cone.add
      | apply LeanProofs.IPRA.Cone.mul
      | apply LeanProofs.IPRA.Cone.pow))

/-- Start a certificate for `ZExp.derive_rel`: `ipra_cone R C ρ h` introduces the ring `R`, the
cone `C`, the valuation `ρ` and the hypotheses `h`, and normalizes the evaluations;
`ipra_cone R C ρ h [defs]` first unfolds the listed definitions. An inequality hypothesis
`a ≤ b` becomes `C.mem (b − a)`, and `C.mem b` when `a` is `0`. -/
syntax "ipra_cone " ident ident ident ident (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| ipra_cone $R:ident $C:ident $ρ:ident $h:ident) =>
    `(tactic| (intro $R:ident _ $C:ident $ρ:ident $h:ident
               simp only [LeanProofs.IPRA.ZExp.holdsR_nil, LeanProofs.IPRA.ZExp.holdsR_cons,
                 LeanProofs.IPRA.ZExp.Rel.holds_eq, LeanProofs.IPRA.ZExp.Rel.holds_le,
                 LeanProofs.IPRA.ZExp.dot, LeanProofs.IPRA.ZExp.cross, LeanProofs.IPRA.ZExp.det3,
                 LeanProofs.IPRA.ZExp.dot2, LeanProofs.IPRA.ZExp.det2,
                 LeanProofs.IPRA.ZExp.eval_var, LeanProofs.IPRA.ZExp.eval_lit,
                 LeanProofs.IPRA.ZExp.eval_zero, LeanProofs.IPRA.ZExp.eval_one,
                 LeanProofs.IPRA.ZExp.eval_numeral, LeanProofs.IPRA.ZExp.eval_add,
                 LeanProofs.IPRA.ZExp.eval_mul, LeanProofs.IPRA.ZExp.eval_neg,
                 LeanProofs.IPRA.ZExp.eval_sub, LeanProofs.IPRA.ZExp.eval_pow, and_true, sub_zero]
                 at $h:ident ⊢))
  | `(tactic| ipra_cone $R:ident $C:ident $ρ:ident $h:ident [$ls,*]) =>
    `(tactic| (intro $R:ident _ $C:ident $ρ:ident $h:ident
               simp only [$ls,*, LeanProofs.IPRA.ZExp.holdsR_nil, LeanProofs.IPRA.ZExp.holdsR_cons,
                 LeanProofs.IPRA.ZExp.Rel.holds_eq, LeanProofs.IPRA.ZExp.Rel.holds_le,
                 LeanProofs.IPRA.ZExp.dot, LeanProofs.IPRA.ZExp.cross, LeanProofs.IPRA.ZExp.det3,
                 LeanProofs.IPRA.ZExp.dot2, LeanProofs.IPRA.ZExp.det2,
                 LeanProofs.IPRA.ZExp.eval_var, LeanProofs.IPRA.ZExp.eval_lit,
                 LeanProofs.IPRA.ZExp.eval_zero, LeanProofs.IPRA.ZExp.eval_one,
                 LeanProofs.IPRA.ZExp.eval_numeral, LeanProofs.IPRA.ZExp.eval_add,
                 LeanProofs.IPRA.ZExp.eval_mul, LeanProofs.IPRA.ZExp.eval_neg,
                 LeanProofs.IPRA.ZExp.eval_sub, LeanProofs.IPRA.ZExp.eval_pow, and_true, sub_zero]
                 at $h:ident ⊢))
