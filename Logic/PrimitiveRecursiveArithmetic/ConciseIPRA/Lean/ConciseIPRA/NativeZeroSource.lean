import ConciseIPRA.NativeEq

/-!
# Transport needs no literal-zero source

`ZPrf` is the kernel `NPrf` with one more restriction on its transport rule:
the source `s` of the equation `s = t` must not be the literal term `0`.  The
condition is on syntax only: a variable, a successor and an iterator term are
all allowed sources, whatever their value.

`zprf_iff_nprf` proves that the restricted calculus derives the same sequents.
This is the theorem of the package `Research/source_dispatch` (Theorem
"Literal-zero source elimination"), here for the equational transport rule.
The proof follows the package:

* reflexivity, symmetry at a nonzero source, transitivity through a nonzero
  middle term and rewriting inside a term are immediate (`eqRefl`, `eqSymm`,
  `eqTrans`, `rwR`, `rwL`);
* two nonzero terms that are both provably `0` are provably equal
  (`zeroJoin`), through the term `I(0, 0; u. 0)`;
* with `Z v = sel v 1 0`, `H v = sel v 1 2`, `N n = I(n, 0; u. Z u)`,
  `R n = I(n, 0; u. H u)` and `L n = N (R n)`, equation induction gives the
  unconditional equations `L (S v) = Z v` (`lS`) and `v = sel (Z v) v 0`
  (`filt`);
* from `0 = t`, equation induction with `t` fixed gives `n = I(n, t; u. S u)`
  for every `n`; at `n = 1` this is `1 = S t`, so `1 = L 1 = L (S t) = Z t`,
  and the filter identity turns `Z t = 1` into `t = 0` (`zeroSymm`);
* symmetry, transitivity and congruence without restriction follow by a case
  distinction on whether a term is literally `0`, and with them the
  unrestricted transport rule (`trF`).

No structural rule of the restricted calculus is needed: substitution is not
admissible in it in general (it can turn a variable source into `0`), and the
proof never substitutes into a derivation.

The argument uses only five rules, collected in the class `ZKernel`, and is
carried out for every derivability predicate that has them.  `ZPrf` is one
instance; `NativeMinimal` uses another.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open Tm (zero succ iter one)

variable {n m : ℕ}

/-- Derivability with transport restricted to sources other than the literal
`0`. -/
inductive ZPrf : {n : ℕ} → List (NFm n) → NFm n → Prop
  | hyp {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (h : A ∈ Γ) : ZPrf Γ A
  | iterZero {n : ℕ} {Γ : List (NFm n)} (a : Tm n) (h : Tm (n + 1)) :
      ZPrf Γ (.eq (iter zero a h) a)
  | iterSucc {n : ℕ} {Γ : List (NFm n)} (c a : Tm n) (h : Tm (n + 1)) :
      ZPrf Γ (.eq (iter (succ c) a h) (Syn.subst (inst (iter c a h)) h))
  /-- Tr: from `s = t` and `a(s) = b(s)` infer `a(t) = b(t)`, provided `s` is
  not the literal `0`. -/
  | trEq {n : ℕ} {Γ : List (NFm n)} (a b : Tm (n + 1)) {s t : Tm n} (hs : s ≠ zero)
      (h₁ : ZPrf Γ (.eq s t))
      (h₂ : ZPrf Γ (.eq (Syn.subst (inst s) a) (Syn.subst (inst s) b))) :
      ZPrf Γ (.eq (Syn.subst (inst t) a) (Syn.subst (inst t) b))
  | qE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 1)} (t : Tm n)
      (h₁ : ZPrf Γ (.Q B)) (h₂ : ZPrf Γ (B.subst (inst zero))) : ZPrf Γ (B.subst (inst t))
  | dE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 2)} {A : NFm n}
      (h₁ : ZPrf Γ (.D B)) (h₂ : ZPrf (.Q B :: Γ.map NFm.shift) A.shift) : ZPrf Γ A
  | dICase {n : ℕ} {Γ : List (NFm n)} (B : NFm (n + 2)) (t : Tm n)
      (h : ZPrf (((B.subst (up (inst t))).subst (inst zero)).shift :: Γ.map NFm.shift)
        ((B.subst (up (inst t))).subst (repl (succ (var 0))))) :
      ZPrf Γ (.D B)
  | qIInd {n : ℕ} {Γ : List (NFm n)} (s₁ s₂ : Tm (n + 1))
      (h : ZPrf (NFm.eq s₁ s₂ :: Γ.map NFm.shift)
        ((NFm.eq s₁ s₂).subst (repl (succ (var 0))))) :
      ZPrf Γ (.Q (.eq s₁ s₂))

namespace Tm

theorem iter_ne_zero (c a : Tm n) (h : Tm (n + 1)) : iter c a h ≠ zero := fun e => by cases e

theorem succ_ne_zero (t : Tm n) : succ t ≠ zero := fun e => by cases e

theorem var_ne_zero (i : Fin n) : (Syn.var i : Tm n) ≠ zero :=
  fun e => by have e' : Tm.var i = Tm.zero := e; cases e'

theorem sel_ne_zero (c a b : Tm n) : Tm.sel c a b ≠ zero := iter_ne_zero _ _ _

/-- The zero test `sel v 1 0`. -/
def tZ (v : Tm n) : Tm n := Tm.sel v one zero
/-- `sel v 0 1`. -/
def tK (v : Tm n) : Tm n := Tm.sel v zero one
/-- `sel v 1 2`. -/
def tH (v : Tm n) : Tm n := Tm.sel v one (succ one)
/-- `I(c, 0; u. Z u)`, with values `0, 1, 0` at `0, 1, 2`. -/
def tN (c : Tm n) : Tm n := iter c zero (tZ (Syn.var 0))
/-- `I(c, 0; u. H u)`, the counter `0, 1, 2, 2, …`. -/
def tR (c : Tm n) : Tm n := iter c zero (tH (Syn.var 0))
/-- `N (R c)`, which is `1` exactly at `c = 1`. -/
def tL (c : Tm n) : Tm n := tN (tR c)

@[simp] theorem subst_tZ (σ : Fin n → Tm m) (v : Tm n) :
    Syn.subst σ (tZ v) = tZ (Syn.subst σ v) := by simp [tZ]
@[simp] theorem subst_tK (σ : Fin n → Tm m) (v : Tm n) :
    Syn.subst σ (tK v) = tK (Syn.subst σ v) := by simp [tK]
@[simp] theorem subst_tH (σ : Fin n → Tm m) (v : Tm n) :
    Syn.subst σ (tH v) = tH (Syn.subst σ v) := by simp [tH]
@[simp] theorem subst_tN (σ : Fin n → Tm m) (c : Tm n) :
    Syn.subst σ (tN c) = tN (Syn.subst σ c) := by simp [tN]
@[simp] theorem subst_tR (σ : Fin n → Tm m) (c : Tm n) :
    Syn.subst σ (tR c) = tR (Syn.subst σ c) := by simp [tR]
@[simp] theorem subst_tL (σ : Fin n → Tm m) (c : Tm n) :
    Syn.subst σ (tL c) = tL (Syn.subst σ c) := by simp [tL]

end Tm

open Tm (tZ tK tH tN tR tL iter_ne_zero succ_ne_zero var_ne_zero sel_ne_zero)

/-- The rules that the elimination of literal-zero sources uses: hypothesis, the
two computation equations, transport at a source other than the literal `0`,
and equation induction.  No logical rule is among them: the case distinctions
of the argument are inductions that ignore their hypothesis (the observation of
the package `Research/guarded_source`). -/
class ZKernel (P : ∀ {n : ℕ}, List (NFm n) → NFm n → Prop) : Prop where
  hyp : ∀ {n : ℕ} {Γ : List (NFm n)} {A : NFm n}, A ∈ Γ → P Γ A
  iterZero : ∀ {n : ℕ} {Γ : List (NFm n)} (a : Tm n) (h : Tm (n + 1)),
    P Γ (.eq (iter zero a h) a)
  iterSucc : ∀ {n : ℕ} {Γ : List (NFm n)} (c a : Tm n) (h : Tm (n + 1)),
    P Γ (.eq (iter (succ c) a h) (Syn.subst (inst (iter c a h)) h))
  trEq : ∀ {n : ℕ} {Γ : List (NFm n)} (a b : Tm (n + 1)) {s t : Tm n}, s ≠ zero →
    P Γ (.eq s t) → P Γ (.eq (Syn.subst (inst s) a) (Syn.subst (inst s) b)) →
    P Γ (.eq (Syn.subst (inst t) a) (Syn.subst (inst t) b))
  eqInd : ∀ {n : ℕ} {Γ : List (NFm n)} (s t : Tm (n + 1)) (u : Tm n),
    P Γ ((NFm.eq s t).subst (inst zero)) →
    P (NFm.eq s t :: Γ.map NFm.shift) ((NFm.eq s t).subst (repl (succ (Syn.var 0)))) →
    P Γ ((NFm.eq s t).subst (inst u))

namespace ZKernel

variable {P : ∀ {n : ℕ}, List (NFm n) → NFm n → Prop} [ZKernel @P] {Γ : List (NFm n)}

omit [ZKernel @P] in
theorem castEq {A B : NFm n} (h : P Γ A) (e : A = B) : P Γ B := e ▸ h

/-! ## The safe equality rules -/

/-- The transport rule with the template and its two instances named. -/
theorem trE {a b : Tm (n + 1)} (H : NFm (n + 1)) (hH : H = .eq a b) {s t : Tm n}
    (hs : s ≠ zero) {A A' : NFm n} (h₁ : P Γ (.eq s t)) (hA : H.subst (inst s) = A)
    (hA' : H.subst (inst t) = A') (h₂ : P Γ A) : P Γ A' := by
  subst hH hA hA'
  exact trEq a b hs h₁ h₂

theorem eqRefl (t : Tm n) : P Γ (.eq t t) :=
  trE (.eq (Syn.var 0) (Syn.shift t)) rfl (iter_ne_zero _ _ _) (iterZero t (Syn.var 0))
    (by simp) (by simp) (iterZero t (Syn.var 0))

theorem eqSymm {s t : Tm n} (hs : s ≠ zero) (h : P Γ (.eq s t)) : P Γ (.eq t s) :=
  trE (.eq (Syn.var 0) (Syn.shift s)) rfl hs h (by simp) (by simp) (eqRefl s)

theorem eqTrans {s t u : Tm n} (ht : t ≠ zero) (h₁ : P Γ (.eq s t))
    (h₂ : P Γ (.eq t u)) : P Γ (.eq s u) :=
  trE (.eq (Syn.shift s) (Syn.var 0)) rfl ht h₂ (by simp) (by simp) h₁

/-- Rewriting on the right of an equation, at a nonzero source. -/
theorem rwR (a : Tm (n + 1)) {s t x r r' : Tm n} (e : P Γ (.eq s t))
    (hr : Syn.subst (inst s) a = r) (hr' : Syn.subst (inst t) a = r')
    (h : P Γ (.eq x r)) (hs : s ≠ zero) : P Γ (.eq x r') :=
  trE (.eq (Syn.shift x) a) rfl hs e (by simp [hr]) (by simp [hr']) h

/-- Rewriting on the left of an equation, at a nonzero source. -/
theorem rwL (a : Tm (n + 1)) {s t x r r' : Tm n} (e : P Γ (.eq s t))
    (hr : Syn.subst (inst s) a = r) (hr' : Syn.subst (inst t) a = r')
    (h : P Γ (.eq r x)) (hs : s ≠ zero) : P Γ (.eq r' x) :=
  trE (.eq a (Syn.shift x)) rfl hs e (by simp [hr]) (by simp [hr']) h

/-- Replacement of equals inside a term, at a nonzero source. -/
theorem eqCongr (a : Tm (n + 1)) {s t : Tm n} (hs : s ≠ zero) (e : P Γ (.eq s t)) :
    P Γ (.eq (Syn.subst (inst s) a) (Syn.subst (inst t) a)) :=
  rwR a e rfl rfl (eqRefl _) hs

/-- Two terms equal to a common nonzero term are equal. -/
theorem join {p q r : Tm n} (hr : r ≠ zero) (hq : q ≠ zero) (h₁ : P Γ (.eq p r))
    (h₂ : P Γ (.eq q r)) : P Γ (.eq p q) :=
  eqTrans hr h₁ (eqSymm hq h₂)

theorem selZ (a b : Tm n) : P Γ (.eq (Tm.sel zero a b) a) := iterZero a _

theorem selS (c a b : Tm n) : P Γ (.eq (Tm.sel (succ c) a b) b) := by
  have h := iterSucc (P := @P) (Γ := Γ) c a (Syn.shift b)
  rw [Syn.subst_inst_shift] at h
  exact h

/-! ## Joining two nonzero terms that are zero -/

/-- A nonzero term that is provably `0` is provably `I(0, 0; u. 0)`. -/
theorem toZ0 {p : Tm n} (hp : p ≠ zero) (h : P Γ (.eq p zero)) :
    P Γ (.eq p (iter zero zero zero)) := by
  have s1 : P Γ (.eq (iter zero zero zero) (iter zero p zero)) :=
    rwL (iter zero (Syn.var 0) zero) h (by simp) (by simp) (eqRefl _) hp
  have s2 := eqSymm (iter_ne_zero _ _ _) s1
  exact rwL (Syn.var 0) (iterZero p zero) (by simp) (by simp) s2 (iter_ne_zero _ _ _)

theorem zeroJoin {p q : Tm n} (hp : p ≠ zero) (hq : q ≠ zero) (h₁ : P Γ (.eq p zero))
    (h₂ : P Γ (.eq q zero)) : P Γ (.eq p q) :=
  join (iter_ne_zero _ _ _) hq (toZ0 hp h₁) (toZ0 hq h₂)

/-! ## The singleton test -/

theorem tZ_zero : P Γ (.eq (tZ zero) one) := selZ _ _
theorem tZ_succ (c : Tm n) : P Γ (.eq (tZ (succ c)) zero) := selS _ _ _
theorem tZ_one : P Γ (.eq (tZ one) zero) := selS _ _ _
theorem tK_zero : P Γ (.eq (tK zero) zero) := selZ _ _
theorem tK_succ (c : Tm n) : P Γ (.eq (tK (succ c)) one) := selS _ _ _
theorem tH_zero : P Γ (.eq (tH zero) one) := selZ _ _
theorem tH_succ (c : Tm n) : P Γ (.eq (tH (succ c)) (succ one)) := selS _ _ _

theorem tN_zero : P Γ (.eq (tN zero) zero) := iterZero _ _

theorem tN_succ (c : Tm n) : P Γ (.eq (tN (succ c)) (tZ (tN c))) :=
  castEq (iterSucc c zero (tZ (Syn.var 0))) (by simp [tN])

theorem tR_zero : P Γ (.eq (tR zero) zero) := iterZero _ _

theorem tR_succ (c : Tm n) : P Γ (.eq (tR (succ c)) (tH (tR c))) :=
  castEq (iterSucc c zero (tH (Syn.var 0))) (by simp [tR])

theorem hK_zero : P Γ (.eq (tH zero) (succ (tK zero))) := by
  have g : P Γ (.eq (succ (tK zero)) (succ zero)) :=
    rwR (succ (Syn.var 0)) tK_zero (by simp) (by simp) (eqRefl _) (sel_ne_zero _ _ _)
  have f : P Γ (.eq (tH zero) (succ zero)) := tH_zero
  exact join (succ_ne_zero _) (succ_ne_zero _) f g

theorem hK_succ (z : Tm n) : P Γ (.eq (tH (succ z)) (succ (tK (succ z)))) := by
  have g : P Γ (.eq (succ (tK (succ z))) (succ one)) :=
    rwR (succ (Syn.var 0)) (tK_succ z) (by simp) (by simp) (eqRefl _) (sel_ne_zero _ _ _)
  exact join (succ_ne_zero _) (succ_ne_zero _) (tH_succ z) g

/-- `H v = S (K v)`. -/
theorem hK (v : Tm n) : P Γ (.eq (tH v) (succ (tK v))) :=
  castEq (eqInd (tH (Syn.var 0)) (succ (tK (Syn.var 0))) v (castEq hK_zero (by simp))
    (castEq (hK_succ (Syn.var 0)) (by simp))) (by simp)

theorem tR_one : P Γ (.eq (tR one) one) := by
  have h1 : P Γ (.eq (tR one) (tH (tR zero))) := tR_succ zero
  have h2 : P Γ (.eq (tR one) (tH zero)) :=
    rwR (tH (Syn.var 0)) tR_zero (by simp) (by simp) h1 (iter_ne_zero _ _ _)
  exact rwR (Syn.var 0) tH_zero (by simp) (by simp) h2 (sel_ne_zero _ _ _)

theorem tR_succ_succ (v : Tm n) : P Γ (.eq (tR (succ (succ v))) (succ one)) := by
  have a2 : P Γ (.eq (tR (succ v)) (succ (tK (tR v)))) :=
    rwR (Syn.var 0) (hK (tR v)) (by simp) (by simp) (tR_succ v) (sel_ne_zero _ _ _)
  have b2 : P Γ (.eq (tR (succ (succ v))) (tH (succ (tK (tR v))))) :=
    rwR (tH (Syn.var 0)) a2 (by simp) (by simp) (tR_succ (succ v)) (iter_ne_zero _ _ _)
  exact rwR (Syn.var 0) (tH_succ (tK (tR v))) (by simp) (by simp) b2 (sel_ne_zero _ _ _)

theorem tN_one : P Γ (.eq (tN one) one) := by
  have h1 : P Γ (.eq (tN one) (tZ (tN zero))) := tN_succ zero
  have h2 : P Γ (.eq (tN one) (tZ zero)) :=
    rwR (tZ (Syn.var 0)) tN_zero (by simp) (by simp) h1 (iter_ne_zero _ _ _)
  exact rwR (Syn.var 0) tZ_zero (by simp) (by simp) h2 (sel_ne_zero _ _ _)

theorem tN_two : P Γ (.eq (tN (succ one)) zero) := by
  have h2 : P Γ (.eq (tN (succ one)) (tZ one)) :=
    rwR (tZ (Syn.var 0)) tN_one (by simp) (by simp) (tN_succ one) (iter_ne_zero _ _ _)
  exact rwR (Syn.var 0) tZ_one (by simp) (by simp) h2 (sel_ne_zero _ _ _)

theorem tL_one : P Γ (.eq (tL one) one) := by
  have h0 : P Γ (.eq (tL one) (tN (tR one))) := eqRefl _
  have h1 : P Γ (.eq (tL one) (tN one)) :=
    rwR (tN (Syn.var 0)) tR_one (by simp) (by simp) h0 (iter_ne_zero _ _ _)
  exact rwR (Syn.var 0) tN_one (by simp) (by simp) h1 (iter_ne_zero _ _ _)

theorem tL_succ_succ (v : Tm n) : P Γ (.eq (tL (succ (succ v))) zero) := by
  have h0 : P Γ (.eq (tL (succ (succ v))) (tN (tR (succ (succ v))))) := eqRefl _
  have h1 : P Γ (.eq (tL (succ (succ v))) (tN (succ one))) :=
    rwR (tN (Syn.var 0)) (tR_succ_succ v) (by simp) (by simp) h0 (iter_ne_zero _ _ _)
  exact rwR (Syn.var 0) tN_two (by simp) (by simp) h1 (iter_ne_zero _ _ _)

/-- **`L (S v) = Z v`**: the test `L` at a successor is the zero test of the
predecessor. -/
theorem lS (v : Tm n) : P Γ (.eq (tL (succ v)) (tZ v)) := by
  have h0 : P Γ (.eq (tL (succ zero)) (tZ zero)) :=
    join (r := one) (succ_ne_zero _) (sel_ne_zero _ _ _) tL_one tZ_zero
  have hS : ∀ {Δ : List (NFm (n + 1))},
      P Δ (.eq (tL (succ (succ (Syn.var 0)))) (tZ (succ (Syn.var 0)))) :=
    zeroJoin (iter_ne_zero _ _ _) (sel_ne_zero _ _ _) (tL_succ_succ _) (tZ_succ _)
  exact castEq (eqInd (tL (succ (Syn.var 0))) (tZ (Syn.var 0)) v (castEq h0 (by simp))
    (castEq hS (by simp))) (by simp)

theorem filt_zero : P Γ (.eq zero (Tm.sel (tZ zero) zero zero)) := by
  have c2 : P Γ (.eq (Tm.sel (tZ zero) zero zero) (Tm.sel one zero zero)) :=
    rwR (Tm.sel (Syn.var 0) zero zero) tZ_zero (by simp) (by simp) (eqRefl _) (sel_ne_zero _ _ _)
  have c3 : P Γ (.eq (Tm.sel one zero zero) zero) := selS _ _ _
  exact eqSymm (sel_ne_zero _ _ _)
    (rwR (Syn.var 0) c3 (by simp) (by simp) c2 (sel_ne_zero _ _ _))

theorem filt_succ (z : Tm n) :
    P Γ (.eq (succ z) (Tm.sel (tZ (succ z)) (succ z) zero)) := by
  have c2 : P Γ (.eq (Tm.sel (tZ (succ z)) (succ z) zero) (Tm.sel zero (succ z) zero)) :=
    rwR (Tm.sel (Syn.var 0) (Syn.shift (succ z)) zero) (tZ_succ z) (by simp)
      (by simp) (eqRefl _) (sel_ne_zero _ _ _)
  exact eqSymm (sel_ne_zero _ _ _)
    (rwR (Syn.var 0) (selZ (succ z) zero) (by simp) (by simp) c2 (sel_ne_zero _ _ _))

/-- **The filter identity** `v = sel (Z v) v 0`. -/
theorem filt (v : Tm n) : P Γ (.eq v (Tm.sel (tZ v) v zero)) :=
  castEq (eqInd (Syn.var 0) (Tm.sel (tZ (Syn.var 0)) (Syn.var 0) zero) v
    (castEq filt_zero (by simp)) (castEq (filt_succ (Syn.var 0)) (by simp))) (by simp)

/-! ## Turning a zero-source equation around -/

/-- **Zero-source symmetry**: from `0 = t` infer `t = 0`. -/
theorem zeroSymm {t : Tm n} (ht : t ≠ zero) (h : P Γ (.eq zero t)) :
    P Γ (.eq t zero) := by
  -- the invariant `u = I(u, t; w. S w)`, by equation induction with `t` fixed
  have inv : ∀ u : Tm n, P Γ (.eq u (iter u t (succ (Syn.var 0)))) := by
    intro u
    have b0 : P Γ (.eq zero (iter zero t (succ (Syn.var 0)))) :=
      rwR (Syn.var 0) (eqSymm (iter_ne_zero _ _ _) (iterZero t (succ (Syn.var 0)))) (by simp)
        (by simp) h ht
    have bS : P (NFm.eq (Syn.var 0) (iter (Syn.var 0) (Syn.shift t) (succ (Syn.var 0)))
          :: Γ.map NFm.shift)
        (.eq (succ (Syn.var 0)) (iter (succ (Syn.var 0)) (Syn.shift t) (succ (Syn.var 0)))) := by
      have c2 : P (NFm.eq (Syn.var 0) (iter (Syn.var 0) (Syn.shift t) (succ (Syn.var 0)))
            :: Γ.map NFm.shift)
          (.eq (succ (Syn.var 0)) (succ (iter (Syn.var 0) (Syn.shift t) (succ (Syn.var 0))))) :=
        rwR (succ (Syn.var 0)) (hyp List.mem_cons_self) (by simp) (by simp) (eqRefl _)
          (var_ne_zero 0)
      have c3 : P (NFm.eq (Syn.var 0) (iter (Syn.var 0) (Syn.shift t) (succ (Syn.var 0)))
            :: Γ.map NFm.shift)
          (.eq (iter (succ (Syn.var 0)) (Syn.shift t) (succ (Syn.var 0)))
            (succ (iter (Syn.var 0) (Syn.shift t) (succ (Syn.var 0))))) :=
        castEq (iterSucc (Syn.var 0) (Syn.shift t) (succ (Syn.var 0))) (by simp)
      exact rwR (Syn.var 0) (eqSymm (iter_ne_zero _ _ _) c3) (by simp) (by simp)
        c2 (succ_ne_zero _)
    exact castEq (eqInd (Syn.var 0) (iter (Syn.var 0) (Syn.shift t) (succ (Syn.var 0))) u
      (castEq b0 (by simp)) (castEq bS (by simp))) (by simp)
  -- `1 = S t`
  have d1 : P Γ (.eq (iter one t (succ (Syn.var 0))) (succ (iter zero t (succ (Syn.var 0))))) :=
    castEq (iterSucc zero t (succ (Syn.var 0))) (by simp [one])
  have d2 : P Γ (.eq (iter one t (succ (Syn.var 0))) (succ t)) :=
    rwR (succ (Syn.var 0)) (iterZero t (succ (Syn.var 0))) (by simp) (by simp)
      d1 (iter_ne_zero _ _ _)
  have d3 : P Γ (.eq one (succ t)) :=
    rwR (Syn.var 0) d2 (by simp) (by simp) (inv one) (iter_ne_zero _ _ _)
  -- `Z t = 1`
  have e2 : P Γ (.eq (tL one) (tL (succ t))) :=
    rwR (tL (Syn.var 0)) d3 (by simp) (by simp) (eqRefl (tL one)) (succ_ne_zero _)
  have e3 : P Γ (.eq one (tL (succ t))) :=
    rwL (Syn.var 0) tL_one (by simp) (by simp) e2 (iter_ne_zero _ _ _)
  have e4 : P Γ (.eq one (tZ t)) :=
    rwR (Syn.var 0) (lS t) (by simp) (by simp) e3 (iter_ne_zero _ _ _)
  have e5 : P Γ (.eq (tZ t) one) := eqSymm (succ_ne_zero _) e4
  -- the filter
  have f2 : P Γ (.eq t (Tm.sel one t zero)) :=
    rwR (Tm.sel (Syn.var 0) (Syn.shift t) zero) e5 (by simp) (by simp) (filt t)
      (sel_ne_zero _ _ _)
  have f3 : P Γ (.eq (Tm.sel one t zero) zero) := selS _ _ _
  exact rwR (Syn.var 0) f3 (by simp) (by simp) f2 (sel_ne_zero _ _ _)

/-! ## The unrestricted equality rules -/

theorem symmF {s t : Tm n} (h : P Γ (.eq s t)) : P Γ (.eq t s) := by
  by_cases hs : s = zero
  · subst hs
    by_cases ht : t = zero
    · subst ht; exact h
    · exact zeroSymm ht h
  · exact eqSymm hs h

theorem transF {r s t : Tm n} (h₁ : P Γ (.eq r s)) (h₂ : P Γ (.eq s t)) :
    P Γ (.eq r t) := by
  by_cases hs : s = zero
  · subst hs
    by_cases hr : r = zero
    · subst hr; exact h₂
    · by_cases ht : t = zero
      · subst ht; exact h₁
      · exact zeroJoin hr ht h₁ (zeroSymm ht h₂)
  · exact eqTrans hs h₁ h₂

theorem congrF (a : Tm (n + 1)) {s t : Tm n} (h : P Γ (.eq s t)) :
    P Γ (.eq (Syn.subst (inst s) a) (Syn.subst (inst t) a)) := by
  by_cases hs : s = zero
  · subst hs
    by_cases ht : t = zero
    · subst ht; exact eqRefl _
    · exact symmF (eqCongr a ht (zeroSymm ht h))
  · exact eqCongr a hs h

/-- **The transport rule without the restriction on its source.** -/
theorem trF (a b : Tm (n + 1)) {s t : Tm n} (h₁ : P Γ (.eq s t))
    (h₂ : P Γ (.eq (Syn.subst (inst s) a) (Syn.subst (inst s) b))) :
    P Γ (.eq (Syn.subst (inst t) a) (Syn.subst (inst t) b)) :=
  transF (transF (symmF (congrF a h₁)) h₂) (congrF b h₁)

end ZKernel

namespace ZPrf

variable {Γ : List (NFm n)}

theorem toNPrf {A : NFm n} (h : ZPrf Γ A) : NPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | trEq a b _ _ _ ih₁ ih₂ => exact .trEq a b ih₁ ih₂
  | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dICase B t _ ih => exact .dICase B t ih
  | qIInd s t _ ih => exact .qIInd s t ih

/-- Equation induction. -/
theorem eqInd (s t : Tm (n + 1)) (u : Tm n) (h0 : ZPrf Γ ((NFm.eq s t).subst (inst zero)))
    (hS : ZPrf (NFm.eq s t :: Γ.map NFm.shift)
      ((NFm.eq s t).subst (repl (succ (Syn.var 0))))) :
    ZPrf Γ ((NFm.eq s t).subst (inst u)) :=
  .qE u (.qIInd s t hS) h0

instance : ZKernel @ZPrf :=
  ⟨fun h => .hyp h, fun a h => .iterZero a h, fun c a h => .iterSucc c a h,
    fun a b => fun hs h₁ h₂ => .trEq a b hs h₁ h₂, eqInd⟩

end ZPrf

variable {Γ : List (NFm n)} {A : NFm n}

theorem NPrf.toZPrf (h : NPrf Γ A) : ZPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | @trOne _ _ h s t u _ _ ih₁ ih₂ =>
    have e := ZKernel.symmF (ZKernel.trF h (Syn.shift u) ih₁ (by simpa using ih₂))
    simpa using e
  | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dICase B t _ ih => exact .dICase B t ih
  | qIInd s t _ ih => exact .qIInd s t ih

/-- **Literal-zero source elimination.**  Restricting transport to sources
other than the literal `0` does not change the derivable sequents. -/
theorem zprf_iff_nprf : ZPrf Γ A ↔ NPrf Γ A := ⟨ZPrf.toNPrf, NPrf.toZPrf⟩

end LeanProofs.ConciseIPRA
