import ConciseIPRA.NativeModels

/-!
# The progressive reading of `Q`: soundness of the uniform rules

`RPrf` is the calculus of the package `Research/uniform_progress`.  It has the
terms and the formulas of the kernel and seven rules: hypothesis, the two
computation equations, transport in an equation template, and three rules
whose mode is read off the root of the matrix alone.  With `η_B(a) = a` when
`B` is a literal equation and `η_B(a) = 0` when `B` is compound, they are

* `QE`: from `Q_y B` and `B(η_B(a))` infer `B(η_B(a) + n)`;
* `DE`: from `D_{x,y} B` and a derivation of `A` from `Q_y B(b, y)` with `b`
  fresh, infer `A`;
* `DI`: from `B(t, η_B(z)) ⊢ B(t, S z)` with `z` fresh infer `D_{x,y} B`.

No rule looks at a witness, so every rule is stable under substitution.  The
price is the meaning of `Q`: at a compound matrix it is the conditional
closure `B(0) → ∀ y, B(y)` of the kernel, and at a literal equation `E` it is
*progressivity*, `∀ y, (E(y) → E(S y))`.

`NFm.rd` is that reading, as a formula of the kernel: `Q_y E` becomes
`∀ y, (E(y) → E(S y))` and `D_{x,y} E` becomes `∃ x ∀ y, (E(x, y) → E(x, S y))`
for a literal equation `E`, with the connectives of `NativeLogic`, and the
binders at compound matrices are unchanged.

* `RPrf.toNPrf`: every derivation of `RPrf` is, under the reading, a
  derivation of the kernel;
* `rprf_sound_pra`: hence a derivation in iPRA;
* `rprf_consistent`: `RPrf` does not derive `0 = 1`.

The one rule that needs an argument is `QE` at an equation: from
progressivity and `E(a)` the kernel proves `E(a + n)` by an equation induction
on `n` (`NPrf.progE`).

This is one direction of the bridge between `RPrf` and the kernel.  The
converse, a translation of kernel derivations into `RPrf` with both formula
round trips, is not formalized.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm
open Tm (zero succ iter)

variable {n m : ℕ}

namespace NFm

/-- The formula is a literal equation. -/
def isEq : {n : ℕ} → NFm n → Bool
  | _, .eq _ _ => true
  | _, _ => false

/-- The start of the uniform rules: the given term at a literal equation, and
`0` at a compound matrix. -/
def eta {k : ℕ} (B : NFm k) (a : Tm n) : Tm n := if B.isEq then a else zero

/-- Progressivity of a matrix: `∀ y, (E(y) → E(S y))`. -/
def prog (E : NFm (n + 1)) : NFm n := all (imp E (E.subst (repl (succ (Syn.var 0)))))

theorem prog_subst (E : NFm (n + 1)) (σ : Fin n → Tm m) :
    (prog E).subst σ = prog (E.subst (up σ)) := by
  simp only [prog, all_subst, imp_subst, subst_repl_succ]

/-- The progressive reading, as a formula of the kernel. -/
def rd : {n : ℕ} → NFm n → NFm n
  | _, .eq s t => .eq s t
  | _, .Q B => if B.isEq then prog (rd B) else .Q (rd B)
  | _, .D B => if B.isEq then ex (prog (rd B)) else .D (rd B)

theorem isEq_subst (A : NFm n) (σ : Fin n → Tm m) : (A.subst σ).isEq = A.isEq := by
  cases A <;> rfl

theorem rd_subst (A : NFm n) : ∀ {m : ℕ} (σ : Fin n → Tm m),
    rd (A.subst σ) = (rd A).subst σ := by
  induction A with intro m σ
  | eq s t => rfl
  | Q B ih =>
    show (if (B.subst (up σ)).isEq then prog (rd (B.subst (up σ)))
        else NFm.Q (rd (B.subst (up σ))))
      = (if B.isEq then prog (rd B) else NFm.Q (rd B)).subst σ
    rw [isEq_subst, ih]
    cases B.isEq
    · rfl
    · exact (prog_subst _ σ).symm
  | D B ih =>
    show (if (B.subst (up (up σ))).isEq then ex (prog (rd (B.subst (up (up σ)))))
        else NFm.D (rd (B.subst (up (up σ)))))
      = (if B.isEq then ex (prog (rd B)) else NFm.D (rd B)).subst σ
    rw [isEq_subst, ih]
    cases B.isEq
    · rfl
    · show ex (prog ((rd B).subst (up (up σ)))) = (ex (prog (rd B))).subst σ
      rw [ex_subst, prog_subst]

theorem rd_shift (A : NFm n) : rd A.shift = (rd A).shift := rd_subst A _

theorem map_rd_shift (Γ : List (NFm n)) :
    (Γ.map NFm.shift).map rd = (Γ.map rd).map NFm.shift := by
  rw [List.map_map, List.map_map]
  exact List.map_congr_left fun A _ => rd_shift A

theorem subst_repl_inst (B : NFm (n + 1)) (d : Tm (n + 1)) (u : Tm n) :
    (B.subst (repl d)).subst (inst u) = B.subst (inst (Syn.subst (inst u) d)) := by
  rw [subst_subst]
  refine B.subst_ext (Fin.cases ?_ fun j => ?_) <;> simp

theorem subst_repl_repl (B : NFm (n + 1)) (d r : Tm (n + 1)) :
    (B.subst (repl d)).subst (repl r) = B.subst (repl (Syn.subst (repl r) d)) := by
  rw [subst_subst]
  refine B.subst_ext (Fin.cases ?_ fun j => ?_) <;> simp

end NFm

/-- Derivability with the seven uniform rules. -/
inductive RPrf : {n : ℕ} → List (NFm n) → NFm n → Prop
  | hyp {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (h : A ∈ Γ) : RPrf Γ A
  | iterZero {n : ℕ} {Γ : List (NFm n)} (a : Tm n) (h : Tm (n + 1)) :
      RPrf Γ (.eq (iter zero a h) a)
  | iterSucc {n : ℕ} {Γ : List (NFm n)} (c a : Tm n) (h : Tm (n + 1)) :
      RPrf Γ (.eq (iter (succ c) a h) (Syn.subst (inst (iter c a h)) h))
  /-- Transport in an equation template: from `s = t` and `p(s) = q(s)` infer
  `p(t) = q(t)`. -/
  | trEq {n : ℕ} {Γ : List (NFm n)} (p q : Tm (n + 1)) {s t : Tm n} (h₁ : RPrf Γ (.eq s t))
      (h₂ : RPrf Γ (.eq (Syn.subst (inst s) p) (Syn.subst (inst s) q))) :
      RPrf Γ (.eq (Syn.subst (inst t) p) (Syn.subst (inst t) q))
  /-- `QE`: from `Q_y B` and `B(η_B(a))` infer `B(η_B(a) + c)`, the sum being
  the iterator of the successor with the counter `η_B(a)` and the
  initializer `c`. -/
  | qE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 1)} (a c : Tm n) (h₁ : RPrf Γ (.Q B))
      (h₂ : RPrf Γ (B.subst (inst (NFm.eta B a)))) :
      RPrf Γ (B.subst (inst (Tm.add c (NFm.eta B a))))
  | dE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 2)} {A : NFm n} (h₁ : RPrf Γ (.D B))
      (h₂ : RPrf (.Q B :: Γ.map NFm.shift) A.shift) : RPrf Γ A
  /-- `DI`: from `B(t, η_B(z)) ⊢ B(t, S z)` with `z` fresh infer `D_{x,y} B`. -/
  | dI {n : ℕ} {Γ : List (NFm n)} (B : NFm (n + 2)) (t : Tm n)
      (h : RPrf ((B.subst (up (inst t))).subst (repl (NFm.eta B (Syn.var 0)))
          :: Γ.map NFm.shift)
        ((B.subst (up (inst t))).subst (repl (succ (var 0))))) : RPrf Γ (.D B)

variable {Γ : List (NFm n)} {A : NFm n}

namespace NPrf

theorem zeroAdd (a : Tm n) : NPrf Γ (.eq (Tm.add zero a) a) :=
  (NPrf.ofPrf (Q.exact (a := Tm.add zero a) (b := a) (Q.zero_add (Q.mk [] a)))).ofNil

theorem succAdd (x y : Tm n) : NPrf Γ (.eq (Tm.add (succ x) y) (succ (Tm.add x y))) :=
  (NPrf.ofPrf (Q.exact (a := Tm.add (succ x) y) (b := succ (Tm.add x y))
    (Q.succ_add (Q.mk [] x) (Q.mk [] y)))).ofNil

/-- **Progressive elimination.**  From `∀ y, (E(y) → E(S y))` and `E(a)` the
kernel proves `E(c + a)`, by an equation induction on `c`. -/
theorem progE (s t : Tm (n + 1)) (a c : Tm n) (h₁ : NPrf Γ (NFm.prog (.eq s t)))
    (h₂ : NPrf Γ ((NFm.eq s t).subst (inst a))) :
    NPrf Γ ((NFm.eq s t).subst (inst (Tm.add c a))) := by
  have ed : ∀ u : Tm n,
      Syn.subst (inst u) (Tm.add (Syn.var 0) (Syn.shift a)) = Tm.add u a := fun u => by simp
  have ed' : Syn.subst (repl (succ (Syn.var 0))) (Tm.add (Syn.var 0) (Syn.shift a))
      = Tm.add (succ (Syn.var 0)) (Syn.shift a) := by simp [Syn.subst_repl_shift]
  rw [← ed c, ← NFm.subst_repl_inst]
  show NPrf Γ ((NFm.eq (Syn.subst (repl (Tm.add (Syn.var 0) (Syn.shift a))) s)
    (Syn.subst (repl (Tm.add (Syn.var 0) (Syn.shift a))) t)).subst (inst c))
  refine NPrf.eqInd _ _ c ?_ ?_
  · show NPrf Γ (((NFm.eq s t).subst (repl (Tm.add (Syn.var 0) (Syn.shift a)))).subst
      (inst zero))
    rw [NFm.subst_repl_inst, ed]
    exact NPrf.tr (NFm.eq s t) (NPrf.eqSymm (NPrf.zeroAdd a)) h₂
  · show NPrf ((NFm.eq s t).subst (repl (Tm.add (Syn.var 0) (Syn.shift a)))
        :: Γ.map NFm.shift)
      (((NFm.eq s t).subst (repl (Tm.add (Syn.var 0) (Syn.shift a)))).subst
        (repl (succ (Syn.var 0))))
    have hp : NPrf ((NFm.eq s t).subst (repl (Tm.add (Syn.var 0) (Syn.shift a)))
          :: Γ.map NFm.shift)
        (NFm.prog ((NFm.eq s t).subst (up fun i => Syn.var i.succ))) := by
      rw [← NFm.prog_subst]
      exact h₁.shift.wk
    have ha := NPrf.allE (Tm.add (Syn.var 0) (Syn.shift a)) hp
    rw [NFm.imp_subst, NFm.subst_repl_inst] at ha
    simp only [Tm.subst_succ, Syn.subst_var, Syn.inst_zero] at ha
    rw [NFm.subst_dummy_up_inst, NFm.subst_dummy_up_inst] at ha
    have hs := NPrf.impE ha NPrf.hyp0
    rw [NFm.subst_repl_repl, ed']
    have k := NPrf.tr ((NFm.eq s t).subst (up fun i => Syn.var i.succ))
      (NPrf.eqSymm (NPrf.succAdd (Syn.var 0) (Syn.shift a)))
      (by rw [NFm.subst_dummy_up_inst]; exact hs)
    rw [NFm.subst_dummy_up_inst] at k
    exact k

end NPrf

/-- **Soundness of the uniform rules.**  Under the progressive reading every
derivation of `RPrf` is a derivation of the kernel. -/
theorem RPrf.toNPrf (h : RPrf Γ A) : NPrf (Γ.map NFm.rd) A.rd := by
  induction h with
  | hyp h => exact .hyp (List.mem_map_of_mem h)
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | trEq p q _ _ ih₁ ih₂ => exact NPrf.tr (.eq p q) ih₁ ih₂
  | @qE _ Γ B a c _ _ ih₁ ih₂ =>
    rw [NFm.rd_subst] at ih₂ ⊢
    cases B with
    | eq s t => exact NPrf.progE s t a c ih₁ ih₂
    | Q B' => exact .qE _ ih₁ ih₂
    | D B' => exact .qE _ ih₁ ih₂
  | @dE _ Γ B A _ _ ih₁ ih₂ =>
    rw [List.map_cons, NFm.map_rd_shift, NFm.rd_shift] at ih₂
    cases B with
    | eq s t => exact NPrf.exE ih₁ ih₂
    | Q B' => exact .dE ih₁ ih₂
    | D B' => exact .dE ih₁ ih₂
  | @dI _ Γ B t _ ih =>
    rw [List.map_cons, NFm.map_rd_shift] at ih
    simp only [NFm.rd_subst] at ih
    cases B with
    | eq s₁ s₂ =>
      rw [show NFm.eta (NFm.eq s₁ s₂) (Syn.var 0 : Tm (_ + 1)) = Syn.var 0 from rfl,
        NFm.subst_repl_var] at ih
      refine NPrf.exI t ?_
      rw [NFm.prog_subst]
      exact NPrf.allI (NPrf.impI ih)
    | Q B' =>
      refine .dICase _ t ?_
      rw [NFm.shift_subst_inst_zero]
      exact ih
    | D B' =>
      refine .dICase _ t ?_
      rw [NFm.shift_subst_inst_zero]
      exact ih

/-- Under the progressive reading every derivation of `RPrf` is a derivation
in iPRA. -/
theorem rprf_sound_pra (h : RPrf Γ A) :
    (Γ.map fun X => X.rd.toPRA) ⊢[PRAAx] A.rd.toPRA := by
  have k := native_iff_pra.1 h.toNPrf
  rwa [List.map_map] at k

/-- **The uniform rules are consistent.** -/
theorem rprf_consistent : ¬ RPrf ([] : List (NFm 0)) NFm.bot := fun h =>
  native_consistent h.toNPrf

end LeanProofs.ConciseIPRA
