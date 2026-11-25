import IPRADerivations.Core.Gcd
import IPRADerivations.Core.LinearCombination

/-!
# Bézout's identity in iPRA

The extended Euclidean algorithm, alongside the remainders `(x_k, y_k)` of
`Core.Gcd`. The coefficients are carried in sign-free form: with quotient
`q_k = x_k div y_k`, the sequences `S_{k+1} = S_{k−1} + q_k S_k` and
`T_{k+1} = T_{k−1} + q_k T_k` (each a pair `(S_k, S_{k+1})` by simultaneous recursion),
and a parity `ε_k` that flips at every active step. Once `y_k = 0` every sequence is
frozen. The invariant, by induction on `k`, is

* `ε_k = 0`, `x_k + T_k b = S_k a`, `y_k + S_{k+1} a = T_{k+1} b`, or
* `ε_k = 1`, `x_k + S_k a = T_k b`, `y_k + T_{k+1} b = S_{k+1} a`.

At `k = b + 1`, where `y_k = 0` and `x_k = gcd(a, b)`, this is Bézout's identity with
natural-number coefficients `u = S_{b+1}`, `v = T_{b+1}`:
`gcd(a, b) + v b = u a` or `gcd(a, b) + u a = v b`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA

open LeanProofs.ConciseIPRA
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

namespace Bezout

/-! ## The coefficient sequences -/

/-- Step variables: `0 = k`, `1 = current`, `2 = next`, `3 = a`, `4 = b`. -/
abbrev yk : PTm 5 := ey (var 0) ![var 3, var 4]
abbrev xk : PTm 5 := ex (var 0) ![var 3, var 4]
abbrev act : PTm 5 := sg yk
abbrev qk : PTm 5 := quo xk yk

abbrev cs₁ : PTm 5 := act * var 2 + monus one act * var 1
abbrev cs₂ : PTm 5 := act * (var 1 + qk * var 2) + monus one act * var 2
abbrev es : PTm 5 := act * monus one (var 1) + monus one act * var 1

/-- A coefficient pair `(c_k, c_{k+1})` with base `(b₁, b₂)`. -/
abbrev cur (b₁ b₂ : PTm 2) (k a b : PTm n) : PTm n := sim₁ b₁ b₂ cs₁ cs₂ k ![a, b]
abbrev nxt (b₁ b₂ : PTm 2) (k a b : PTm n) : PTm n := sim₂ b₁ b₂ cs₁ cs₂ k ![a, b]
/-- `ε_k`. -/
abbrev eps (k a b : PTm n) : PTm n := sim₁ zero zero es es k ![a, b]

@[simp] theorem subst_cur {m : ℕ} (σ : Fin n → PTm m) (b₁ b₂ : PTm 2) (k a b : PTm n) :
    Syn.subst σ (cur b₁ b₂ k a b) = cur b₁ b₂ (Syn.subst σ k) (Syn.subst σ a) (Syn.subst σ b) := by
  rw [subst_sim₁]; congr 1; funext i; fin_cases i <;> rfl
@[simp] theorem subst_nxt {m : ℕ} (σ : Fin n → PTm m) (b₁ b₂ : PTm 2) (k a b : PTm n) :
    Syn.subst σ (nxt b₁ b₂ k a b) = nxt b₁ b₂ (Syn.subst σ k) (Syn.subst σ a) (Syn.subst σ b) := by
  rw [subst_sim₂]; congr 1; funext i; fin_cases i <;> rfl
@[simp] theorem subst_eps {m : ℕ} (σ : Fin n → PTm m) (k a b : PTm n) :
    Syn.subst σ (eps k a b) = eps (Syn.subst σ k) (Syn.subst σ a) (Syn.subst σ b) := by
  rw [subst_sim₁]; congr 1; funext i; fin_cases i <;> rfl

theorem cur_succ (b₁ b₂ : PTm 2) (k a b : PTm n) :
    Γ ⊢[PRAAx] cur b₁ b₂ (succ k) a b ≐ sg (ey k ![a, b]) * nxt b₁ b₂ k a b
      + monus one (sg (ey k ![a, b])) * cur b₁ b₂ k a b := by
  have h := sim₁_succ (Γ := Γ) b₁ b₂ cs₁ cs₂ ![a, b] k
  simp only [PTm.subst_add, PTm.subst_mul, PTm.subst_monus, subst_ap2, subst_ex2,
    subst_ey2, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.subst_var,
    Fin.cases_zero, finCases_one, finCases_two, finCases_three, finCases_four,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h; exact h

theorem nxt_succ (b₁ b₂ : PTm 2) (k a b : PTm n) :
    Γ ⊢[PRAAx] nxt b₁ b₂ (succ k) a b ≐ sg (ey k ![a, b]) * (cur b₁ b₂ k a b
      + quo (ex k ![a, b]) (ey k ![a, b]) * nxt b₁ b₂ k a b)
      + monus one (sg (ey k ![a, b])) * nxt b₁ b₂ k a b := by
  have h := sim₂_succ (Γ := Γ) b₁ b₂ cs₁ cs₂ ![a, b] k
  simp only [PTm.subst_add, PTm.subst_mul, PTm.subst_monus, subst_ap2, subst_ex2,
    subst_ey2, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.subst_var,
    Fin.cases_zero, finCases_one, finCases_two, finCases_three, finCases_four,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h; exact h

theorem eps_succ (k a b : PTm n) :
    Γ ⊢[PRAAx] eps (succ k) a b ≐ sg (ey k ![a, b]) * monus one (eps k a b)
      + monus one (sg (ey k ![a, b])) * eps k a b := by
  have h := sim₁_succ (Γ := Γ) zero zero es es ![a, b] k
  simp only [PTm.subst_add, PTm.subst_mul, PTm.subst_monus, subst_ap2, subst_ex2,
    subst_ey2, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.subst_var,
    Fin.cases_zero, finCases_one, finCases_two, finCases_three, finCases_four,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h; exact h

/-- A guarded combination `s·u + (1 ∸ s)·v` with `s = sg y`. -/
theorem guard_zero {y u v : PTm n} (h : Γ ⊢[PRAAx] y ≐ zero) :
    Γ ⊢[PRAAx] sg y * u + monus one (sg y) * v ≐ v := by
  have hs : Γ ⊢[PRAAx] sg y ≐ zero :=
    (congrMonus (.eqRefl _) (congrMonus (.eqRefl _) h)).eqTrans sg_zero
  refine (congrAdd (congrMul hs (.eqRefl _)) (congrMul ((congrMonus (.eqRefl _) hs).eqTrans
    (monus_zero _)) (.eqRefl _))).eqTrans ?_
  exact (congrAdd (zero_mul _) (one_mul _)).eqTrans (zero_add _)

theorem guard_succ {y c u v : PTm n} (h : Γ ⊢[PRAAx] y ≐ succ c) :
    Γ ⊢[PRAAx] sg y * u + monus one (sg y) * v ≐ u := by
  have hs : Γ ⊢[PRAAx] sg y ≐ one :=
    (congrMonus (.eqRefl _) (congrMonus (.eqRefl _) h)).eqTrans (sg_succ _)
  refine (congrAdd (congrMul hs (.eqRefl _)) (congrMul ((congrMonus (.eqRefl _) hs).eqTrans
    (monus_self _)) (.eqRefl _))).eqTrans ?_
  exact (congrAdd (one_mul _) (zero_mul _)).eqTrans (add_zero _)

/-! ## The invariant -/

/-- Variables: `0 = k`, `1 = a`, `2 = b`. -/
abbrev X : PTm 3 := ex (var 0) ![var 1, var 2]
abbrev Y : PTm 3 := ey (var 0) ![var 1, var 2]
abbrev Sc : PTm 3 := cur one zero (var 0) (var 1) (var 2)
abbrev Sn : PTm 3 := nxt one zero (var 0) (var 1) (var 2)
abbrev Tc : PTm 3 := cur zero one (var 0) (var 1) (var 2)
abbrev Tn : PTm 3 := nxt zero one (var 0) (var 1) (var 2)
abbrev E : PTm 3 := eps (var 0) (var 1) (var 2)

abbrev X' : PTm 3 := ex (succ (var 0)) ![var 1, var 2]
abbrev Y' : PTm 3 := ey (succ (var 0)) ![var 1, var 2]
abbrev Sc' : PTm 3 := cur one zero (succ (var 0)) (var 1) (var 2)
abbrev Sn' : PTm 3 := nxt one zero (succ (var 0)) (var 1) (var 2)
abbrev Tc' : PTm 3 := cur zero one (succ (var 0)) (var 1) (var 2)
abbrev Tn' : PTm 3 := nxt zero one (succ (var 0)) (var 1) (var 2)
abbrev E' : PTm 3 := eps (succ (var 0)) (var 1) (var 2)

/-- The even and odd forms of the invariant at `(x, y, S, S', T, T', ε)`. -/
abbrev evenF (x y s s' t t' e : PTm 3) : Fm PTm 3 :=
  (e ≐ zero) ⋏ ((x + t * var 2 ≐ s * var 1) ⋏ (y + s' * var 1 ≐ t' * var 2))
abbrev oddF (x y s s' t t' e : PTm 3) : Fm PTm 3 :=
  (e ≐ one) ⋏ ((x + s * var 1 ≐ t * var 2) ⋏ (y + t' * var 2 ≐ s' * var 1))

abbrev inv : Fm PTm 3 := evenF X Y Sc Sn Tc Tn E ⋎ oddF X Y Sc Sn Tc Tn E

theorem eq3 {Δ : List (Fm PTm 3)} {x x₁ t t₁ s s₁ c d : PTm 3} (hx : Δ ⊢[PRAAx] x₁ ≐ x)
    (ht : Δ ⊢[PRAAx] t₁ ≐ t) (hs : Δ ⊢[PRAAx] s₁ ≐ s) (h : Δ ⊢[PRAAx] x + t * c ≐ s * d) :
    Δ ⊢[PRAAx] x₁ + t₁ * c ≐ s₁ * d :=
  (congrAdd hx (congrMul ht (.eqRefl _))).eqTrans (h.eqTrans (congrMul hs.eqSymm (.eqRefl _)))

/-- Transport of the invariant along equalities of all seven components. -/
theorem transport {Δ : List (Fm PTm 3)} {x y s s' t t' e x₁ y₁ s₁ s₁' t₁ t₁' e₁ : PTm 3}
    (hx : Δ ⊢[PRAAx] x₁ ≐ x) (hy : Δ ⊢[PRAAx] y₁ ≐ y) (hs : Δ ⊢[PRAAx] s₁ ≐ s)
    (hs' : Δ ⊢[PRAAx] s₁' ≐ s') (ht : Δ ⊢[PRAAx] t₁ ≐ t) (ht' : Δ ⊢[PRAAx] t₁' ≐ t')
    (he : Δ ⊢[PRAAx] e₁ ≐ e)
    (h : Δ ⊢[PRAAx] evenF x y s s' t t' e ⋎ oddF x y s s' t t' e) :
    Δ ⊢[PRAAx] evenF x₁ y₁ s₁ s₁' t₁ t₁' e₁ ⋎ oddF x₁ y₁ s₁ s₁' t₁ t₁' e₁ := by
  refine .orE h ?_ ?_
  · exact .orI₁ (.andI (he.wk.eqTrans (Prf.andE₁ Prf.hyp0))
      (.andI (eq3 hx.wk ht.wk hs.wk (Prf.andE₁ (Prf.andE₂ Prf.hyp0)))
        (eq3 hy.wk hs'.wk ht'.wk (Prf.andE₂ (Prf.andE₂ Prf.hyp0)))))
  · exact .orI₂ (.andI (he.wk.eqTrans (Prf.andE₁ Prf.hyp0))
      (.andI (eq3 hx.wk hs.wk ht.wk (Prf.andE₁ (Prf.andE₂ Prf.hyp0)))
        (eq3 hy.wk ht'.wk hs'.wk (Prf.andE₂ (Prf.andE₂ Prf.hyp0)))))

/-- The active step: `ε` flips and `r + (T + q T') b = (S + q S') a` follows from the
old equations and `x = q y + r`. -/
theorem active_eq {Δ : List (Fm PTm 3)} {x y r q s s' t t' c d : PTm 3}
    (h₁ : Δ ⊢[PRAAx] x + t * c ≐ s * d) (h₂ : Δ ⊢[PRAAx] y + s' * d ≐ t' * c)
    (hd : Δ ⊢[PRAAx] x ≐ y * q + r) :
    Δ ⊢[PRAAx] r + (t + q * t') * c ≐ (s + q * s') * d := by
  refine withEq h₁ fun e₁ => withEq h₂ fun e₂ => withEq hd fun e₃ => ?_
  ipra_lc e₁ - e₃ - Groth.ι (Q.mk Δ q) * e₂

theorem invariant_open : ([] : List (Fm PTm 3)) ⊢[PRAAx] inv := by
  refine ind _ ⟨⟨trivial, trivial, trivial⟩, trivial, trivial, trivial⟩ ?_ ?_
  · simp only [Fm.subst_or, Fm.subst_and, Fm.subst_eq, PTm.subst_add, PTm.subst_mul, subst_cur,
      subst_nxt, subst_eps, subst_ex2, subst_ey2, Syn.subst_var, Syn.inst_zero, Syn.inst_one,
      inst_two, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    have z₁ := sim₁_zero (Γ := ([] : List (Fm PTm 2))) one zero cs₁ cs₂ ![var 0, var 1]
    have z₂ := sim₂_zero (Γ := ([] : List (Fm PTm 2))) one zero cs₁ cs₂ ![var 0, var 1]
    have z₃ := sim₁_zero (Γ := ([] : List (Fm PTm 2))) zero one cs₁ cs₂ ![var 0, var 1]
    have z₄ := sim₂_zero (Γ := ([] : List (Fm PTm 2))) zero one cs₁ cs₂ ![var 0, var 1]
    have z₅ := sim₁_zero (Γ := ([] : List (Fm PTm 2))) zero zero es es ![var 0, var 1]
    simp only [ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at z₁ z₂ z₃ z₄ z₅
    refine .orI₁ (.andI z₅ (.andI ?_ ?_))
    · refine withEq (ex_zero (Γ := ([] : List (Fm PTm 2))) (var 0) (var 1)) fun f₁ => withEq z₁ fun f₂ =>
        withEq z₃ fun f₃ => ?_
      apply deriveNat; ipra_simps; rw [f₁, f₂, f₃]; ring
    · refine withEq (ey_zero (Γ := ([] : List (Fm PTm 2))) (var 0) (var 1)) fun f₁ => withEq z₂ fun f₂ =>
        withEq z₄ fun f₃ => ?_
      apply deriveNat; ipra_simps; rw [f₁, f₂, f₃]; ring
  · simp only [Fm.subst_or, Fm.subst_and, Fm.subst_eq, PTm.subst_add, PTm.subst_mul, subst_cur,
      subst_nxt, subst_eps, subst_ex2, subst_ey2, Syn.subst_var, Syn.repl_zero, repl_one, repl_two,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    have hSc := cur_succ (Γ := [inv]) one zero (var 0) (var 1) (var 2)
    have hSn := nxt_succ (Γ := [inv]) one zero (var 0) (var 1) (var 2)
    have hTc := cur_succ (Γ := [inv]) zero one (var 0) (var 1) (var 2)
    have hTn := nxt_succ (Γ := [inv]) zero one (var 0) (var 1) (var 2)
    have hE := eps_succ (Γ := [inv]) (var 0) (var 1) (var 2)
    refine .orE (zero_or_succ Y) ?_ ?_
    · -- y_k = 0: everything is frozen.
      have hy : ((Y ≐ zero) :: [inv]) ⊢[PRAAx] Y ≐ zero := Prf.hyp0
      have hs := e_step_zero hy
      exact transport (Prf.andE₁ hs) ((Prf.andE₂ hs).eqTrans hy.eqSymm) (hSc.wk.eqTrans (guard_zero hy))
        (hSn.wk.eqTrans (guard_zero hy)) (hTc.wk.eqTrans (guard_zero hy)) (hTn.wk.eqTrans (guard_zero hy))
        (hE.wk.eqTrans (guard_zero hy)) Prf.hyp1
    · -- y_k = S c: an active step.
      have hy : ((Y ≐ succ (pred Y)) :: [inv]) ⊢[PRAAx] Y ≐ succ (pred Y) := Prf.hyp0
      have hs := e_step_succ hy
      have hd := Prf.andE₁ (div_mod_at (x := X) hy)
      have hSc' := hSc.wk.eqTrans (guard_succ hy)
      have hSn' := hSn.wk.eqTrans (guard_succ hy)
      have hTc' := hTc.wk.eqTrans (guard_succ hy)
      have hTn' := hTn.wk.eqTrans (guard_succ hy)
      have hE' := hE.wk.eqTrans (guard_succ hy)
      refine .orE (Prf.hyp1 : ((Y ≐ succ (pred Y)) :: [inv]) ⊢[PRAAx] inv) ?_ ?_
      · -- even: the new state is odd.
        have h₁ : (evenF X Y Sc Sn Tc Tn E :: (Y ≐ succ (pred Y)) :: [inv]) ⊢[PRAAx]
            X + Tc * var 2 ≐ Sc * var 1 := Prf.andE₁ (Prf.andE₂ Prf.hyp0)
        have h₂ : (evenF X Y Sc Sn Tc Tn E :: (Y ≐ succ (pred Y)) :: [inv]) ⊢[PRAAx]
            Y + Sn * var 1 ≐ Tn * var 2 := Prf.andE₂ (Prf.andE₂ Prf.hyp0)
        refine .orI₂ (.andI ((hE'.wk.eqTrans (congrMonus (.eqRefl _) (Prf.andE₁ Prf.hyp0))).eqTrans
          (monus_zero _)) (.andI ?_ ?_))
        · exact eq3 (Prf.andE₁ hs).wk hSc'.wk hTc'.wk h₂
        · exact eq3 (Prf.andE₂ hs).wk hTn'.wk hSn'.wk (active_eq h₁ h₂ hd.wk)
      · -- odd: the new state is even.
        have h₁ : (oddF X Y Sc Sn Tc Tn E :: (Y ≐ succ (pred Y)) :: [inv]) ⊢[PRAAx]
            X + Sc * var 1 ≐ Tc * var 2 := Prf.andE₁ (Prf.andE₂ Prf.hyp0)
        have h₂ : (oddF X Y Sc Sn Tc Tn E :: (Y ≐ succ (pred Y)) :: [inv]) ⊢[PRAAx]
            Y + Tn * var 2 ≐ Sn * var 1 := Prf.andE₂ (Prf.andE₂ Prf.hyp0)
        refine .orI₁ (.andI ((hE'.wk.eqTrans (congrMonus (.eqRefl _) (Prf.andE₁ Prf.hyp0))).eqTrans
          (monus_self _)) (.andI ?_ ?_))
        · exact eq3 (Prf.andE₁ hs).wk hTc'.wk hSc'.wk h₂
        · exact eq3 (Prf.andE₂ hs).wk hSn'.wk hTn'.wk (active_eq h₁ h₂ hd.wk)

end Bezout

/-- Bézout's identity: `gcd(a, b) + v b = u a` or `gcd(a, b) + u a = v b`, with
`u = S_{b+1}`, `v = T_{b+1}`; variables `0 = a`, `1 = b`. -/
abbrev bezoutFormula : Fm PTm 2 :=
  (gcd (var 0) (var 1) + Bezout.cur zero one (succ (var 1)) (var 0) (var 1) * var 1
      ≐ Bezout.cur one zero (succ (var 1)) (var 0) (var 1) * var 0) ⋎
    (gcd (var 0) (var 1) + Bezout.cur one zero (succ (var 1)) (var 0) (var 1) * var 0
      ≐ Bezout.cur zero one (succ (var 1)) (var 0) (var 1) * var 1)

theorem bezout : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 bezoutFormula := by
  refine closeUniv 2 ?_
  have h := inst (Γ := ([] : List (Fm PTm 2))) Bezout.invariant_open
    (![succ (var 1), var 0, var 1] : Fin 3 → PTm 2)
  simp only [Fm.subst_or, Fm.subst_and, Fm.subst_eq, PTm.subst_add, PTm.subst_mul,
    Bezout.subst_cur, Bezout.subst_nxt, Bezout.subst_eps, subst_ex2, subst_ey2, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at h
  exact .orE h (.orI₁ (Prf.andE₁ (Prf.andE₂ Prf.hyp0))) (.orI₂ (Prf.andE₁ (Prf.andE₂ Prf.hyp0)))

end LeanProofs.IPRA
