import IPRADerivations.Foundations.BoundedReflection

/-!
# A compiler from bounded formulas to bits

Packet: `foundations/ipra_bounded_reflection_2026-11-16` (`thm:reflection` and `thm:choice`); the
same compiler is the starting point of the FINER, STRIVE, SCOPE and TAPIR framework packets.

A bounded formula `A : BF` is built from equations between terms, `∧`, `∨`, `¬` and the bounded
quantifiers `∀ i < b` and `∃ i < b`. It has one free parameter `y`; under a quantifier the body
is read at the pair `⟨i, y⟩`, so any number of variables is available by pairing. Two
interpretations are defined by recursion, at an arbitrary term `y` of any context:

* `fmAt A y`, the iPRA formula;
* `bitAt A y`, a primitive-recursive term: `eqb` for equations, product for `∧`, `sg (a + b)` for
  `∨`, `1 ∸ a` for `¬`, and the aggregators `allB`, `exB` of `Foundations/BoundedReflection`
  for the quantifiers.

Derived, by recursion on `A` (each case is an iPRA derivation; no induction on a quantified
formula is used):

* `bf_reflect` (`thm:reflection`): `fmAt A y ↔ bitAt A y = 1`;
* `bf_cases`: `bitAt A y` is `0` or `1`;
* `bf_dec` (`thm:reflection`): `fmAt A y ∨ ¬ fmAt A y`;
* `bf_choice`, `bf_least` (`thm:choice`): from `∃ i < b, A(⟨i, y⟩)`, the primitive-recursive
  witness `w = bfWit b A y` satisfies `w < b`, `A(⟨w, y⟩)`, and `¬ A(⟨j, y⟩)` for `j < w`.

`bitAt_subst` and `fmAt_subst` say that both interpretations commute with substitution.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.BoundedFormulas

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open LeanProofs.IPRA.Foundations.BoundedReflection
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

/-! ## Syntax and the two interpretations -/

/-- Bounded formulas in one packed parameter. -/
inductive BF : Type
  | eq (s t : PTm 1) : BF
  | and (A B : BF) : BF
  | or (A B : BF) : BF
  | not (A : BF) : BF
  /-- `∀ i < b(y), A(⟨i, y⟩)`. -/
  | all (b : PTm 1) (A : BF) : BF
  /-- `∃ i < b(y), A(⟨i, y⟩)`. -/
  | ex (b : PTm 1) (A : BF) : BF

/-- A one-parameter term read at `y`. -/
def at1 {m : ℕ} (s : PTm 1) (y : PTm m) : PTm m := Syn.subst ![y] s

theorem at1_subst {m k : ℕ} (s : PTm 1) (σ : Fin m → PTm k) (y : PTm m) :
    Syn.subst σ (at1 s y) = at1 s (Syn.subst σ y) := by
  unfold at1
  rw [Syn.subst_subst]
  congr 1; funext j; fin_cases j; rfl

/-- The bit of `A` at `y`. -/
def bitAt : BF → (m : ℕ) → PTm m → PTm m
  | .eq s t, _, y => eqb (at1 s y) (at1 t y)
  | .and A B, m, y => bitAt A m y * bitAt B m y
  | .or A B, m, y => sg (bitAt A m y + bitAt B m y)
  | .not A, m, y => monus one (bitAt A m y)
  | .all b A, _, y => allB (bitAt A 2 (pairT (var 0) (var 1))) (at1 b y) y
  | .ex b A, _, y => exB (bitAt A 2 (pairT (var 0) (var 1))) (at1 b y) y

/-- The formula of `A` at `y`. -/
def fmAt : BF → (m : ℕ) → PTm m → Fm PTm m
  | .eq s t, _, y => at1 s y ≐ at1 t y
  | .and A B, m, y => fmAt A m y ⋏ fmAt B m y
  | .or A B, m, y => fmAt A m y ⋎ fmAt B m y
  | .not A, m, y => neg (fmAt A m y)
  | .all b A, m, y =>
      Fm.all (lt (var 0) (Syn.shift (at1 b y)) ⟶ fmAt A (m + 1) (pairT (var 0) (Syn.shift y)))
  | .ex b A, m, y =>
      Fm.ex (lt (var 0) (Syn.shift (at1 b y)) ⋏ fmAt A (m + 1) (pairT (var 0) (Syn.shift y)))

/-- The body of a quantifier over `A`: index `0`, parameter `1`. -/
abbrev body (A : BF) : PTm 2 := bitAt A 2 (pairT (var 0) (var 1))

/-! ## Substitution -/

theorem bitAt_subst (A : BF) : ∀ {m k : ℕ} (σ : Fin m → PTm k) (y : PTm m),
    Syn.subst σ (bitAt A m y) = bitAt A k (Syn.subst σ y) := by
  induction A with
  | eq s t => intro m k σ y; simp only [bitAt, subst_eqb, at1_subst]
  | and A B ihA ihB => intro m k σ y; simp only [bitAt, PTm.subst_mul, ihA, ihB]
  | or A B ihA ihB =>
    intro m k σ y
    simp only [bitAt, PTm.subst_monus, PTm.subst_add, ConciseIPRA.PTm.subst_succ,
      ConciseIPRA.PTm.subst_zero, ihA, ihB]
  | not A ih =>
    intro m k σ y
    simp only [bitAt, PTm.subst_monus, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, ih]
  | all b A _ => intro m k σ y; simp only [bitAt, subst_ap2, at1_subst]
  | ex b A _ =>
    intro m k σ y
    simp only [bitAt, PTm.subst_monus, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, subst_ap2,
      at1_subst]

theorem inst2_body (A : BF) {m : ℕ} (i y : PTm m) : inst2 (body A) i y = bitAt A m (pairT i y) := by
  unfold inst2
  rw [bitAt_subst]
  congr 1
  simp

theorem subst_up_shift' {m k : ℕ} (σ : Fin m → PTm k) (t : PTm m) :
    Syn.subst (Syn.up σ) (Syn.shift t) = Syn.shift (Syn.subst σ t) := by
  rw [Syn.subst_shift, Syn.shift_subst]; simp

theorem fmAt_subst (A : BF) : ∀ {m k : ℕ} (σ : Fin m → PTm k) (y : PTm m),
    (fmAt A m y).subst σ = fmAt A k (Syn.subst σ y) := by
  induction A with
  | eq s t => intro m k σ y; simp only [fmAt, Fm.subst_eq, at1_subst]
  | and A B ihA ihB => intro m k σ y; simp only [fmAt, Fm.subst_and, ihA, ihB]
  | or A B ihA ihB => intro m k σ y; simp only [fmAt, Fm.subst_or, ihA, ihB]
  | not A ih => intro m k σ y; simp only [fmAt, subst_neg, ih]
  | all b A ih =>
    intro m k σ y
    simp only [fmAt, Fm.subst_all, Fm.subst_imp, subst_lt, ih, subst_pairT, Syn.subst_var, Syn.up_zero,
      subst_up_shift', at1_subst]
  | ex b A ih =>
    intro m k σ y
    simp only [fmAt, Fm.subst_ex, Fm.subst_and, subst_lt, ih, subst_pairT, Syn.subst_var, Syn.up_zero,
      subst_up_shift', at1_subst]

/-! ## Bit lemmas -/

section Bits

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem sg_of_pos {x c : PTm n} (h : Γ ⊢[PRAAx] x ≐ succ c) : Γ ⊢[PRAAx] sg x ≐ one :=
  (congrMonus (.eqRefl _) (congrMonus (.eqRefl _) h)).eqTrans (sg_succ c)

theorem sg_of_zero {x : PTm n} (h : Γ ⊢[PRAAx] x ≐ zero) : Γ ⊢[PRAAx] sg x ≐ zero :=
  (congrMonus (.eqRefl _) (congrMonus (.eqRefl _) h)).eqTrans sg_zero

theorem or_left {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ one) : Γ ⊢[PRAAx] sg (a + b) ≐ one :=
  sg_of_pos (c := b) ((congrAdd h (.eqRefl _)).eqTrans (by ipra_ring))

theorem or_right {a b : PTm n} (h : Γ ⊢[PRAAx] b ≐ one) : Γ ⊢[PRAAx] sg (a + b) ≐ one :=
  sg_of_pos (c := a) ((congrAdd (.eqRefl _) h).eqTrans (by ipra_ring))

theorem or_none {a b : PTm n} (ha : Γ ⊢[PRAAx] a ≐ zero) (hb : Γ ⊢[PRAAx] b ≐ zero) :
    Γ ⊢[PRAAx] sg (a + b) ≐ zero :=
  sg_of_zero ((congrAdd ha hb).eqTrans (add_zero _))

theorem and_both {a b : PTm n} (ha : Γ ⊢[PRAAx] a ≐ one) (hb : Γ ⊢[PRAAx] b ≐ one) :
    Γ ⊢[PRAAx] a * b ≐ one :=
  (congrMul ha hb).eqTrans (one_mul _)

theorem and_zero_left {a b : PTm n} (ha : Γ ⊢[PRAAx] a ≐ zero) : Γ ⊢[PRAAx] a * b ≐ zero :=
  (congrMul ha (.eqRefl _)).eqTrans (zero_mul _)

theorem and_zero_right {a b : PTm n} (hb : Γ ⊢[PRAAx] b ≐ zero) : Γ ⊢[PRAAx] a * b ≐ zero :=
  (congrMul (.eqRefl _) hb).eqTrans (mul_zero _)

theorem not_of_zero {a : PTm n} (h : Γ ⊢[PRAAx] a ≐ zero) : Γ ⊢[PRAAx] monus one a ≐ one :=
  (congrMonus (.eqRefl _) h).eqTrans (monus_zero _)

theorem not_of_one {a : PTm n} (h : Γ ⊢[PRAAx] a ≐ one) : Γ ⊢[PRAAx] monus one a ≐ zero :=
  (congrMonus (.eqRefl _) h).eqTrans (le_refl one)

/-- `0 = 1` in context: anything follows from `a = 0` and `a = 1`. -/
theorem clash {a : PTm n} (φ : Fm PTm n) (h₀ : Γ ⊢[PRAAx] a ≐ zero) (h₁ : Γ ⊢[PRAAx] a ≐ one) :
    Γ ⊢[PRAAx] φ :=
  one_ne_zero φ (h₁.eqSymm.eqTrans h₀)

end Bits

/-! ## Reflection -/

/-- The three facts carried through the recursion. -/
def Refl (A : BF) (m : ℕ) (Δ : List (Fm PTm m)) (y : PTm m) : Prop :=
  (Δ ⊢[PRAAx] fmAt A m y ⟶ (bitAt A m y ≐ one)) ∧
    (Δ ⊢[PRAAx] (bitAt A m y ≐ one) ⟶ fmAt A m y) ∧
    (Δ ⊢[PRAAx] (bitAt A m y ≐ zero) ⋎ (bitAt A m y ≐ one))

theorem reflect (A : BF) : ∀ {m : ℕ} {Δ : List (Fm PTm m)} (y : PTm m), Refl A m Δ y := by
  induction A with
  | eq s t =>
    intro m Δ y
    refine ⟨?_, ?_, ?_⟩
    · exact .impI (eqb_of_eq Prf.hyp0)
    · exact .impI (eq_of_eqb Prf.hyp0)
    · exact eqb_cases _ _
  | and A B ihA ihB =>
    intro m Δ y
    refine ⟨?_, ?_, ?_⟩
    · exact .impI (and_both (.impE (ihA y).1 (Prf.andE₁ Prf.hyp0)) (.impE (ihB y).1 (Prf.andE₂ Prf.hyp0)))
    · refine .impI (.andI ?_ ?_)
      · refine .orE (ihA y).2.2 ?_ (.impE (ihA y).2.1 Prf.hyp0)
        exact clash _ (and_zero_left Prf.hyp0) Prf.hyp1
      · refine .orE (ihB y).2.2 ?_ (.impE (ihB y).2.1 Prf.hyp0)
        exact clash _ (and_zero_right Prf.hyp0) Prf.hyp1
    · refine .orE (ihA y).2.2 (.orI₁ (and_zero_left Prf.hyp0)) ?_
      exact .orE (ihB y).2.2 (.orI₁ (and_zero_right Prf.hyp0)) (.orI₂ (and_both Prf.hyp1 Prf.hyp0))
  | or A B ihA ihB =>
    intro m Δ y
    refine ⟨?_, ?_, ?_⟩
    · exact .impI (.orE Prf.hyp0 (or_left (.impE (ihA y).1 Prf.hyp0)) (or_right (.impE (ihB y).1 Prf.hyp0)))
    · refine .impI (.orE (ihA y).2.2 ?_ (.orI₁ (.impE (ihA y).2.1 Prf.hyp0)))
      refine .orE (ihB y).2.2 ?_ (.orI₂ (.impE (ihB y).2.1 Prf.hyp0))
      exact clash _ (or_none Prf.hyp1 Prf.hyp0) Prf.hyp1.wk
    · exact sg_cases _
  | not A ih =>
    intro m Δ y
    refine ⟨?_, ?_, ?_⟩
    · refine .impI (.orE (ih y).2.2 (not_of_zero Prf.hyp0) ?_)
      exact .botE _ (.impE Prf.hyp1 (.impE (ih y).2.1 Prf.hyp0))
    · exact .impI (.impI (clash _ (not_of_one (.impE (ih y).1 Prf.hyp0)) Prf.hyp1))
    · exact .orE (ih y).2.2 (.orI₂ (not_of_zero Prf.hyp0)) (.orI₁ (not_of_one Prf.hyp0))
  | all b A ih =>
    intro m Δ y
    refine ⟨?_, ?_, ?_⟩
    · refine .impI (all_intro (body A) (.allI (.impI ?_)))
      have hA := Prf.impE (Prf.hyp0 (Ax := PRAAx) (Γ := Δ)
        (φ := Fm.all (lt (var 0) (Syn.shift (at1 b y)) ⟶ fmAt A (m + 1) (pairT (var 0) (Syn.shift y))))).allOpen.wk
        Prf.hyp0
      have hb := Prf.impE (ih (pairT (var 0) (Syn.shift y))).1 hA
      rw [inst2_body]
      exact .impI (clash _ Prf.hyp0 hb.wk)
    · refine .impI ?_
      have r := all_reflect (body A) (Prf.hyp0 (Ax := PRAAx) (Γ := Δ) (φ := bitAt (.all b A) m y ≐ one))
      refine .allI (.impI ?_)
      have hn := Prf.impE r.allOpen.wk Prf.hyp0
      rw [inst2_body] at hn
      exact .orE (ih (pairT (var 0) (Syn.shift y))).2.2 (.botE _ (.impE hn.wk Prf.hyp0))
        (.impE (ih (pairT (var 0) (Syn.shift y))).2.1 Prf.hyp0)
    · exact all_cases (body A) _ _
  | ex b A ih =>
    intro m Δ y
    refine ⟨?_, ?_, ?_⟩
    · refine .impI (Prf.exE Prf.hyp0 ?_)
      have e : Fm.shift (bitAt (.ex b A) m y ≐ one) =
          (exB (body A) (Syn.shift (at1 b y)) (Syn.shift y) ≐ one) := by
        simp [Fm.shift, Syn.shift, bitAt]
      rw [e]
      refine ex_intro (body A) ?_ (Prf.andE₁ Prf.hyp0)
      rw [inst2_body]
      exact .impI (clash _ Prf.hyp0
        (Prf.impE (ih (pairT (var 0) (Syn.shift y))).1 (Prf.andE₂ Prf.hyp0)).wk)
    · refine .impI ?_
      have w := ex_elim (body A) (Prf.hyp0 (Ax := PRAAx) (Γ := Δ) (φ := bitAt (.ex b A) m y ≐ one))
      have hn := Prf.andE₂ w
      rw [inst2_body] at hn
      have hA := Prf.orE (ih (pairT (wit (body A) (at1 b y) y) y)).2.2 (.botE _ (.impE hn.wk Prf.hyp0))
        (.impE (ih (pairT (wit (body A) (at1 b y) y) y)).2.1 Prf.hyp0)
      refine Prf.exI (wit (body A) (at1 b y) y) ?_
      have e : (lt (var 0) (Syn.shift (at1 b y)) ⋏ fmAt A (m + 1) (pairT (var 0) (Syn.shift y))).subst
            (Syn.inst (wit (body A) (at1 b y) y)) =
          (lt (wit (body A) (at1 b y) y) (at1 b y) ⋏ fmAt A m (pairT (wit (body A) (at1 b y) y) y)) := by
        simp [fmAt_subst]
      rw [e]
      exact .andI (Prf.andE₁ w) hA
    · exact ex_cases (body A) _ _

/-! ## The theorems -/

section Theorems

variable {m : ℕ} {Δ : List (Fm PTm m)}

/-- `thm:reflection`: `A(y) ↔ e_A(y) = 1`. -/
theorem bf_reflect (A : BF) (y : PTm m) : Δ ⊢[PRAAx] Fm.iff (fmAt A m y) (bitAt A m y ≐ one) :=
  Prf.iffI (reflect A y).1 (reflect A y).2.1

/-- The bit is `0` or `1`. -/
theorem bf_cases (A : BF) (y : PTm m) : Δ ⊢[PRAAx] (bitAt A m y ≐ zero) ⋎ (bitAt A m y ≐ one) :=
  (reflect A y).2.2

/-- `thm:reflection`: a bounded formula is decidable. -/
theorem bf_dec (A : BF) (y : PTm m) : Δ ⊢[PRAAx] fmAt A m y ⋎ neg (fmAt A m y) := by
  refine .orE (bf_cases A y) (.orI₂ (.impI ?_)) (.orI₁ (.impE (reflect A y).2.1 Prf.hyp0))
  exact clash _ Prf.hyp1 (.impE (reflect A y).1 Prf.hyp0)

/-- The least witness of `∃ i < b, A(⟨i, y⟩)`, or `b(y)` if there is none. -/
abbrev bfWit (b : PTm 1) (A : BF) (y : PTm m) : PTm m := wit (body A) (at1 b y) y

/-- `thm:choice`: a bounded existential statement yields its primitive-recursive witness. -/
theorem bf_choice (b : PTm 1) (A : BF) (y : PTm m) (h : Δ ⊢[PRAAx] fmAt (.ex b A) m y) :
    Δ ⊢[PRAAx] lt (bfWit b A y) (at1 b y) ⋏ fmAt A m (pairT (bfWit b A y) y) := by
  have w := ex_elim (body A) (.impE (reflect (.ex b A) y).1 h)
  have hn := Prf.andE₂ w
  rw [inst2_body] at hn
  exact .andI (Prf.andE₁ w) (.orE (bf_cases A _) (.botE _ (.impE hn.wk Prf.hyp0))
    (.impE (reflect A _).2.1 Prf.hyp0))

/-- `thm:choice`: the witness is the least one. -/
theorem bf_least (b : PTm 1) (A : BF) (y j : PTm m) (hj : Δ ⊢[PRAAx] lt j (bfWit b A y)) :
    Δ ⊢[PRAAx] neg (fmAt A m (pairT j y)) := by
  have z := ex_least (body A) hj
  rw [inst2_body] at z
  exact .impI (clash _ z.wk (.impE (reflect A _).1 Prf.hyp0))

end Theorems

end LeanProofs.IPRA.Foundations.BoundedFormulas
