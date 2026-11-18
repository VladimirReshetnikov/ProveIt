import IPRADerivations.Core.Tactic

/-!
# Implications between integer polynomial equations

Many theorems of the packets have the form

  `h₁ = h₁' → … → h_r = h_r' → c = c'`

for integer polynomials in finitely many integer variables: an exact identity (`r = 0`) or an
identity modulo defining relations such as `s² + c² = 1`. This module turns such a statement
into a closed iPRA theorem from one certificate that is valid in every commutative ring.

* `ZExp k`: polynomial expressions in `k` integer variables, with `+`, `*`, `-`, numerals and
  natural powers;
* `ZExp.eval ρ e`: the value in a commutative ring under a valuation `ρ`;
* `ZExp.toZT e`: the integer term of `Core/Integers`. The integer variable `i` is the
  difference of the natural-number variables `2i` and `2i + 1`, so a statement about `k`
  integers is an iPRA sentence with `2k` universally quantified natural numbers;
* `ZExp.imp hyps c`: the iPRA formula `h₁ = h₁' → … → c = c'`, each equation being the
  quantifier-free `ZT.eq`;
* `ZExp.derive_imp`: if in every commutative ring and for every valuation the hypotheses give
  the conclusion, then `[] ⊢[PRAAx] univ (2k) (imp hyps c)`.

The certificate is checked in the ring of differences `Groth (Q Γ)` of the terms modulo
provable equality, which is a commutative ring but neither `ℤ` nor a domain. So the
certificate must be a ring identity, typically `ring` or `linear_combination`; cancellation of
a nonzero factor is not available here (see `Core/IntCancel`).

The tactic `ipra_poly R ρ h` introduces the ring, the valuation and the hypotheses of a
certificate under the given names and normalizes the evaluations; `ipra_poly R ρ h [defs]` first
unfolds the given definitions.

`ZExp.Vec3` with `dot`, `cross`, `det3`, and `ZExp.Vec2` with `dot2`, `det2`, are triples and
pairs of expressions with the vector operations.
-/

namespace LeanProofs.IPRA

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm

/-- Integer polynomial expressions in `k` integer variables. -/
inductive ZExp (k : ℕ) : Type
  | var (i : Fin k) : ZExp k
  | lit (c : ℕ) : ZExp k
  | add (a b : ZExp k) : ZExp k
  | mul (a b : ZExp k) : ZExp k
  | neg (a : ZExp k) : ZExp k

namespace ZExp

variable {k : ℕ}

instance : Add (ZExp k) := ⟨add⟩
instance : Mul (ZExp k) := ⟨mul⟩
instance : Neg (ZExp k) := ⟨neg⟩
instance : Sub (ZExp k) := ⟨fun a b => add a (neg b)⟩
instance (c : ℕ) : OfNat (ZExp k) c := ⟨lit c⟩

/-- Natural powers. -/
def pow (a : ZExp k) : ℕ → ZExp k
  | 0 => lit 1
  | m + 1 => mul (pow a m) a

instance : Pow (ZExp k) ℕ := ⟨pow⟩

/-! ## Evaluation in a commutative ring -/

section Eval

variable {R : Type} [CommRing R] (ρ : Fin k → R)

/-- The value of an expression. -/
def eval : ZExp k → R
  | var i => ρ i
  | lit c => (c : R)
  | add a b => eval a + eval b
  | mul a b => eval a * eval b
  | neg a => -eval a

@[simp] theorem eval_var (i : Fin k) : eval ρ (var i) = ρ i := rfl
@[simp] theorem eval_lit (c : ℕ) : eval ρ (lit c : ZExp k) = (c : R) := rfl
@[simp] theorem eval_ofNat (c : ℕ) : eval ρ (OfNat.ofNat c : ZExp k) = (c : R) := rfl
@[simp] theorem eval_zero : eval ρ (0 : ZExp k) = 0 := Nat.cast_zero
@[simp] theorem eval_one : eval ρ (1 : ZExp k) = 1 := Nat.cast_one
@[simp] theorem eval_numeral (c : ℕ) [c.AtLeastTwo] :
    eval ρ (no_index (OfNat.ofNat c) : ZExp k) = (OfNat.ofNat c : R) := Nat.cast_ofNat
@[simp] theorem eval_add (a b : ZExp k) : eval ρ (a + b) = eval ρ a + eval ρ b := rfl
@[simp] theorem eval_mul (a b : ZExp k) : eval ρ (a * b) = eval ρ a * eval ρ b := rfl
@[simp] theorem eval_neg (a : ZExp k) : eval ρ (-a) = -eval ρ a := rfl
@[simp] theorem eval_sub (a b : ZExp k) : eval ρ (a - b) = eval ρ a - eval ρ b :=
  (sub_eq_add_neg _ _).symm

@[simp] theorem eval_pow (a : ZExp k) (m : ℕ) : eval ρ (a ^ m) = eval ρ a ^ m := by
  induction m with
  | zero => show ((1 : ℕ) : R) = _; simp
  | succ m ih =>
    show eval ρ (pow a m) * eval ρ a = _
    have ih' : eval ρ (pow a m) = eval ρ a ^ m := ih
    rw [ih', pow_succ]

/-- All the listed equations hold under the valuation. -/
def Holds : List (ZExp k × ZExp k) → Prop
  | [] => True
  | h :: t => eval ρ h.1 = eval ρ h.2 ∧ Holds t

@[simp] theorem holds_nil : Holds ρ ([] : List (ZExp k × ZExp k)) = True := rfl
@[simp] theorem holds_cons (h : ZExp k × ZExp k) (t : List (ZExp k × ZExp k)) :
    Holds ρ (h :: t) = (eval ρ h.1 = eval ρ h.2 ∧ Holds ρ t) := rfl

end Eval

/-! ## The integer term and its evaluation -/

/-- The integer term of an expression: variable `i` is `var (2i) − var (2i + 1)`. -/
def toZT : ZExp k → ZT (2 * k)
  | var i => ZT.var2 ⟨2 * i.val, by have := i.isLt; omega⟩ ⟨2 * i.val + 1, by have := i.isLt; omega⟩
  | lit c => ZT.natLit c
  | add a b => toZT a + toZT b
  | mul a b => toZT a * toZT b
  | neg a => -toZT a

/-- The valuation of the integer variables in the ring of differences of `Q Γ`. -/
def val (Γ : List (Fm PTm (2 * k))) (i : Fin k) : Groth (Q Γ) :=
  V Γ ⟨2 * i.val, by have := i.isLt; omega⟩ - V Γ ⟨2 * i.val + 1, by have := i.isLt; omega⟩

theorem toZ_toZT (Γ : List (Fm PTm (2 * k))) (e : ZExp k) :
    ZT.toZ Γ (toZT e) = eval (val Γ) e := by
  induction e with
  | var i => rfl
  | lit c => simp [toZT, eval]
  | add a b iha ihb => simp [toZT, eval, iha, ihb]
  | mul a b iha ihb => simp [toZT, eval, iha, ihb]
  | neg a iha => simp [toZT, eval, iha]

/-! ## Implications -/

/-- The equation `a = b`, as a quantifier-free iPRA formula. -/
def eqF (a b : ZExp k) : Fm PTm (2 * k) := ZT.eq (toZT a) (toZT b)

/-- The formula `h₁ = h₁' → … → h_r = h_r' → c = c'`. -/
def imp (hyps : List (ZExp k × ZExp k)) (c : ZExp k × ZExp k) : Fm PTm (2 * k) :=
  hyps.foldr (fun h φ => eqF h.1 h.2 ⟶ φ) (eqF c.1 c.2)

theorem imp_nil (c : ZExp k × ZExp k) : imp [] c = eqF c.1 c.2 := rfl

theorem imp_cons (h : ZExp k × ZExp k) (t : List (ZExp k × ZExp k)) (c : ZExp k × ZExp k) :
    imp (h :: t) c = (eqF h.1 h.2 ⟶ imp t c) := rfl

/-- The open form, with the hypotheses already assumed collected in `done`. -/
theorem derive_imp_open (c : ZExp k × ZExp k) :
    ∀ (hyps done : List (ZExp k × ZExp k)) (Γ : List (Fm PTm (2 * k))),
      (∀ h ∈ done, Γ ⊢[PRAAx] eqF h.1 h.2) →
      (∀ (R : Type) [CommRing R] (ρ : Fin k → R), (∀ h ∈ done, eval ρ h.1 = eval ρ h.2) →
        Holds ρ hyps → eval ρ c.1 = eval ρ c.2) →
      (Γ ⊢[PRAAx] imp hyps c)
  | [], done, Γ, hd, cert => by
    rw [imp_nil]
    refine ZT.derive ?_
    rw [toZ_toZT, toZ_toZT]
    refine cert _ (val Γ) (fun h hh => ?_) trivial
    rw [← toZ_toZT, ← toZ_toZT]
    exact ZT.toZ_eq (hd h hh)
  | h :: t, done, Γ, hd, cert => by
    rw [imp_cons]
    refine .impI (derive_imp_open c t (h :: done) _ ?_ ?_)
    · intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact Prf.hyp0
      · exact (hd g hg).wk
    · intro R _ ρ hdone ht
      exact cert R ρ (fun g hg => hdone g (List.mem_cons_of_mem _ hg))
        ⟨hdone h List.mem_cons_self, ht⟩

/-- An implication between integer polynomial equations that holds in every commutative ring is
a theorem of iPRA, universally closed over its `2k` natural-number variables. -/
theorem derive_imp (hyps : List (ZExp k × ZExp k)) (c : ZExp k × ZExp k)
    (cert : ∀ (R : Type) [CommRing R] (ρ : Fin k → R), Holds ρ hyps → eval ρ c.1 = eval ρ c.2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * k) (imp hyps c) :=
  closeUniv (2 * k) (derive_imp_open c hyps [] [] (fun _ hh => nomatch hh)
    (fun R _ ρ _ h => cert R ρ h))

/-! ## Vectors of expressions -/

/-- A triple of expressions: a point or a line of the projective plane, or a vector of space. -/
structure Vec3 (k : ℕ) where
  x : ZExp k
  y : ZExp k
  z : ZExp k

/-- The dot product. -/
def dot (u v : Vec3 k) : ZExp k := u.x * v.x + u.y * v.y + u.z * v.z

/-- The cross product. -/
def cross (u v : Vec3 k) : Vec3 k :=
  ⟨u.y * v.z - u.z * v.y, u.z * v.x - u.x * v.z, u.x * v.y - u.y * v.x⟩

/-- The determinant with rows `u`, `v`, `w`. -/
def det3 (u v w : Vec3 k) : ZExp k := dot u (cross v w)

/-- A pair of expressions: a point or a vector of the plane. -/
structure Vec2 (k : ℕ) where
  x : ZExp k
  y : ZExp k

/-- The planar dot product. -/
def dot2 (u v : Vec2 k) : ZExp k := u.x * v.x + u.y * v.y

/-- The planar determinant `u.x v.y − u.y v.x`. -/
def det2 (u v : Vec2 k) : ZExp k := u.x * v.y - u.y * v.x

end ZExp

end LeanProofs.IPRA

/-- Start a certificate for `ZExp.derive_imp`: `ipra_poly R ρ h` introduces the ring `R`, the
valuation `ρ` and the hypotheses `h` (a conjunction, or `True` when there are none), and
normalizes the evaluations. `ipra_poly R ρ h [defs]` first unfolds the listed definitions. -/
syntax "ipra_poly " ident ident ident (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| ipra_poly $R:ident $ρ:ident $h:ident) =>
    `(tactic| (intro $R:ident _ $ρ:ident $h:ident
               simp only [LeanProofs.IPRA.ZExp.holds_nil, LeanProofs.IPRA.ZExp.holds_cons,
                 LeanProofs.IPRA.ZExp.dot, LeanProofs.IPRA.ZExp.cross, LeanProofs.IPRA.ZExp.det3,
                 LeanProofs.IPRA.ZExp.dot2, LeanProofs.IPRA.ZExp.det2,
                 LeanProofs.IPRA.ZExp.eval_var, LeanProofs.IPRA.ZExp.eval_lit,
                 LeanProofs.IPRA.ZExp.eval_zero, LeanProofs.IPRA.ZExp.eval_one,
                 LeanProofs.IPRA.ZExp.eval_numeral, LeanProofs.IPRA.ZExp.eval_add,
                 LeanProofs.IPRA.ZExp.eval_mul, LeanProofs.IPRA.ZExp.eval_neg,
                 LeanProofs.IPRA.ZExp.eval_sub, LeanProofs.IPRA.ZExp.eval_pow, and_true]
                 at $h:ident ⊢))
  | `(tactic| ipra_poly $R:ident $ρ:ident $h:ident [$ls,*]) =>
    `(tactic| (intro $R:ident _ $ρ:ident $h:ident
               simp only [$ls,*, LeanProofs.IPRA.ZExp.holds_nil, LeanProofs.IPRA.ZExp.holds_cons,
                 LeanProofs.IPRA.ZExp.dot, LeanProofs.IPRA.ZExp.cross, LeanProofs.IPRA.ZExp.det3,
                 LeanProofs.IPRA.ZExp.dot2, LeanProofs.IPRA.ZExp.det2,
                 LeanProofs.IPRA.ZExp.eval_var, LeanProofs.IPRA.ZExp.eval_lit,
                 LeanProofs.IPRA.ZExp.eval_zero, LeanProofs.IPRA.ZExp.eval_one,
                 LeanProofs.IPRA.ZExp.eval_numeral, LeanProofs.IPRA.ZExp.eval_add,
                 LeanProofs.IPRA.ZExp.eval_mul, LeanProofs.IPRA.ZExp.eval_neg,
                 LeanProofs.IPRA.ZExp.eval_sub, LeanProofs.IPRA.ZExp.eval_pow, and_true]
                 at $h:ident ⊢))
