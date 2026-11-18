import IPRADerivations.Core.ClockedDescent

/-!
# Fusion and simulation of iterations (`ipra_presentations_to_witnesses`)

Packet: `foundations/ipra_presentations_to_witnesses`, Section 2: Theorem `thm:fusion`
("Proof-preserving fusion"), Theorem `thm:simulation` ("Quantifier-free simulation") and
Corollary `cor:squaring` ("Transport through repeated squaring").

For a unary step term `f` the iterate is the primitive recursion
`iter f 0 x = x`, `iter f (n + 1) x = f(iter f n x)` (`iter_zero`, `iter_succ`).

* `fusion` (`thm:fusion`): if iPRA derives `h(f(x)) = g(h(x))`, then it derives
  `h(iter f n x) = iter g n (h(x))` for all `n`, `x`; closed form `fusion_closed`. The
  invariant is the equation itself, with `x` free.
* `simulation` (`thm:simulation`): for a quantifier-free `R(x, y)`, if `R(x, y)` gives
  `R(f(x), g(y))`, then `R(x, y)` gives `R(iter f n x, iter g n y)` for every `n`;
  `simulation_all` is the form with the universal quantifier over `n` under the hypothesis.
* `squaring` (`cor:squaring`): if `h(a · b) = h(a) ⋆ h(b)` for binary terms `·`, `⋆`, then
  `h(s_n) = t_n` for `s_0 = x`, `s_{n+1} = s_n · s_n`, `t_0 = h(x)`, `t_{n+1} = t_n ⋆ t_n`.
  No associativity is used.

The local hypotheses are rules derivable at arbitrary terms and hypotheses, which is
equivalent to the supplied closed derivations of the packet. Guards belong in `R`.

Instances with the local derivation supplied: `double_iter` (`h(x) = 2x`, `f = +1`, `g = +2`)
and `square_squaring` (`h(a) = a²` between two copies of multiplication).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.IterationFusion

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.ClockedDescent (subst_QF')
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)

variable {k : ℕ} {Γ : List (Fm PTm k)}

/-! ## Application of a unary term and iteration -/

/-- `t(y)` for a one-variable term `t`. -/
def app1 (t : PTm 1) (y : PTm k) : PTm k := Syn.subst ![y] t

@[simp] theorem subst_app1 {m : ℕ} (σ : Fin k → PTm m) (t : PTm 1) (y : PTm k) :
    Syn.subst σ (app1 t y) = app1 t (Syn.subst σ y) := by
  simp only [app1, Syn.subst_subst]
  congr 1; funext j; fin_cases j; rfl

theorem congrApp1 (t : PTm 1) {y y' : PTm k} (h : Γ ⊢[PRAAx] y ≐ y') :
    Γ ⊢[PRAAx] app1 t y ≐ app1 t y' :=
  Prf.eqCongr t fun j => by fin_cases j; exact h

/-- The step of the iteration; variables `0 = n`, `1 = iter f n x`, `2 = x`. -/
def iterStep (f : PTm 1) : PTm 3 := app1 f (var 1)

/-- `iter f n x = f^n(x)`. -/
abbrev iter (f : PTm 1) (n x : PTm k) : PTm k := ap2 (rec2 (var 0) (iterStep f)) n x

theorem iter_zero (f : PTm 1) (x : PTm k) : Γ ⊢[PRAAx] iter f zero x ≐ x := by
  simpa using rec2_zero (Γ := Γ) (var 0) (iterStep f) x

theorem iter_succ (f : PTm 1) (n x : PTm k) :
    Γ ⊢[PRAAx] iter f (succ n) x ≐ app1 f (iter f n x) := by
  have h := rec2_succ (Γ := Γ) (var 0) (iterStep f) n x
  have e : Syn.subst ![n, ap2 (rec2 (var 0) (iterStep f)) n x, x] (iterStep f) =
      app1 f (iter f n x) := by
    simp only [iterStep, subst_app1, Syn.subst_var]
    rfl
  rw [e] at h
  exact h

/-! ## Fusion -/

section Fusion

variable {f g h : PTm 1}

theorem fusion_step
    (hloc : ∀ {k : ℕ} {Γ : List (Fm PTm k)} (x : PTm k),
      Γ ⊢[PRAAx] app1 h (app1 f x) ≐ app1 g (app1 h x)) {n x : PTm k}
    (ih : Γ ⊢[PRAAx] app1 h (iter f n x) ≐ iter g n (app1 h x)) :
    Γ ⊢[PRAAx] app1 h (iter f (succ n) x) ≐ iter g (succ n) (app1 h x) :=
  (congrApp1 h (iter_succ f n x)).eqTrans
    ((hloc _).eqTrans ((congrApp1 g ih).eqTrans (iter_succ g n _).eqSymm))

/-- Variables: `0 = n`, `1 = x`. -/
private def fusF (f g h : PTm 1) : Fm PTm 2 :=
  app1 h (iter f (var 0) (var 1)) ≐ iter g (var 0) (app1 h (var 1))

private theorem fus₀
    (hloc : ∀ {k : ℕ} {Γ : List (Fm PTm k)} (x : PTm k),
      Γ ⊢[PRAAx] app1 h (app1 f x) ≐ app1 g (app1 h x)) :
    ([] : List (Fm PTm 2)) ⊢[PRAAx] fusF f g h := by
  refine ind _ trivial ?_ ?_
  · simp only [fusF, Fm.subst_eq, subst_app1, subst_ap2, Syn.subst_var, Syn.inst_zero,
      Syn.inst_one, ConciseIPRA.PTm.subst_zero]
    exact (congrApp1 h (iter_zero f _)).eqTrans (iter_zero g _).eqSymm
  · simp only [fusF, Fm.subst_eq, subst_app1, subst_ap2, Syn.subst_var, Syn.repl_zero, repl_one,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    have ih : [fusF f g h] ⊢[PRAAx]
        app1 h (iter f (var 0) (var 1)) ≐ iter g (var 0) (app1 h (var 1)) := Prf.hyp0
    exact fusion_step hloc ih

/-- `thm:fusion`: from `h(f(x)) = g(h(x))`, `h(iter f n x) = iter g n (h(x))`. -/
theorem fusion
    (hloc : ∀ {k : ℕ} {Γ : List (Fm PTm k)} (x : PTm k),
      Γ ⊢[PRAAx] app1 h (app1 f x) ≐ app1 g (app1 h x)) (n x : PTm k) :
    Γ ⊢[PRAAx] app1 h (iter f n x) ≐ iter g n (app1 h x) := by
  have i := inst (Γ := Γ) (fus₀ hloc) (![n, x] : Fin 2 → PTm k)
  simpa [fusF] using i

/-- `thm:fusion` as a closed sentence. Variables: `0 = n`, `1 = x`. -/
theorem fusion_closed
    (hloc : ∀ {k : ℕ} {Γ : List (Fm PTm k)} (x : PTm k),
      Γ ⊢[PRAAx] app1 h (app1 f x) ≐ app1 g (app1 h x)) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (app1 h (iter f (var 0) (var 1)) ≐ iter g (var 0) (app1 h (var 1))) :=
  closeUniv 2 (fusion hloc _ _)

end Fusion

/-! ## Simulation -/

/-- `R(a, b)` for a two-variable formula `R`. -/
def rel (R : Fm PTm 2) (a b : PTm k) : Fm PTm k := R.subst ![a, b]

@[simp] theorem subst_rel {m : ℕ} (σ : Fin k → PTm m) (R : Fm PTm 2) (a b : PTm k) :
    (rel R a b).subst σ = rel R (Syn.subst σ a) (Syn.subst σ b) := by
  simp only [rel, Fm.subst_subst]
  congr 1; funext j; fin_cases j <;> rfl

theorem rel_congr (R : Fm PTm 2) {a a' b b' : PTm k} (ha : Γ ⊢[PRAAx] a ≐ a')
    (hb : Γ ⊢[PRAAx] b ≐ b') (hr : Γ ⊢[PRAAx] rel R a b) : Γ ⊢[PRAAx] rel R a' b' :=
  Prf.eqSubst R ![a, b] ![a', b'] (fun i => by
    fin_cases i
    · exact ha
    · exact hb) hr

section Simulation

variable {R : Fm PTm 2} {f g : PTm 1}

/-- Variables: `0 = n`, `1 = x`, `2 = y`. -/
private def simF (R : Fm PTm 2) (f g : PTm 1) : Fm PTm 3 :=
  rel R (var 1) (var 2) ⟶ rel R (iter f (var 0) (var 1)) (iter g (var 0) (var 2))

private theorem sim₀ (hqf : R.QF)
    (hloc : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {x y : PTm k},
      (Γ ⊢[PRAAx] rel R x y) → (Γ ⊢[PRAAx] rel R (app1 f x) (app1 g y))) :
    ([] : List (Fm PTm 3)) ⊢[PRAAx] simF R f g := by
  refine ind _ ⟨subst_QF' hqf _, subst_QF' hqf _⟩ ?_ ?_
  · simp only [simF, Fm.subst_imp, subst_rel, subst_ap2, Syn.subst_var, Syn.inst_zero,
      Syn.inst_one, inst_two, ConciseIPRA.PTm.subst_zero]
    exact .impI (rel_congr R (iter_zero f _).eqSymm (iter_zero g _).eqSymm Prf.hyp0)
  · simp only [simF, Fm.subst_imp, subst_rel, subst_ap2, Syn.subst_var, Syn.repl_zero, repl_one,
      repl_two, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    have ih : [simF R f g] ⊢[PRAAx]
        rel R (var 1) (var 2) ⟶ rel R (iter f (var 0) (var 1)) (iter g (var 0) (var 2)) :=
      Prf.hyp0
    exact .impI (rel_congr R (iter_succ f _ _).eqSymm (iter_succ g _ _).eqSymm
      (hloc (.impE ih.wk Prf.hyp0)))

/-- `thm:simulation`: a quantifier-free relation preserved by one step of `f` and `g` is
preserved by `n` steps. -/
theorem simulation (hqf : R.QF)
    (hloc : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {x y : PTm k},
      (Γ ⊢[PRAAx] rel R x y) → (Γ ⊢[PRAAx] rel R (app1 f x) (app1 g y)))
    {x y : PTm k} (h : Γ ⊢[PRAAx] rel R x y) (n : PTm k) :
    Γ ⊢[PRAAx] rel R (iter f n x) (iter g n y) := by
  have i := inst (Γ := Γ) (sim₀ hqf hloc) (![n, x, y] : Fin 3 → PTm k)
  simp [simF] at i
  exact .impE i h

/-- `thm:simulation` with the quantifier over the number of steps:
`R(x, y) ⊢ ∀n R(iter f n x, iter g n y)`. -/
theorem simulation_all (hqf : R.QF)
    (hloc : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {x y : PTm k},
      (Γ ⊢[PRAAx] rel R x y) → (Γ ⊢[PRAAx] rel R (app1 f x) (app1 g y)))
    {x y : PTm k} (h : Γ ⊢[PRAAx] rel R x y) :
    Γ ⊢[PRAAx] Fm.all (rel R (iter f (var 0) (Syn.shift x)) (iter g (var 0) (Syn.shift y))) := by
  refine .allI ?_
  have h' := h.shift
  have e : Fm.shift (rel R x y) = rel R (Syn.shift x) (Syn.shift y) := by
    simp [Fm.shift, Syn.shift]
  rw [e] at h'
  exact simulation hqf hloc h' _

end Simulation

/-! ## Repeated squaring -/

/-- The squaring step `a ↦ a · a` of a binary term. -/
def sq (m : PTm 2) : PTm 1 := inst2 m (var 0) (var 0)

theorem app1_sq (m : PTm 2) (a : PTm k) : app1 (sq m) a = inst2 m a a := by
  simp [app1, sq]

/-- `cor:squaring`: a map with `h(a · b) = h(a) ⋆ h(b)` commutes with repeated squaring:
`h(s_n) = t_n` for `s_{n+1} = s_n · s_n` and `t_{n+1} = t_n ⋆ t_n`. -/
theorem squaring {m s : PTm 2} {h : PTm 1}
    (hmul : ∀ {k : ℕ} {Γ : List (Fm PTm k)} (a b : PTm k),
      Γ ⊢[PRAAx] app1 h (inst2 m a b) ≐ inst2 s (app1 h a) (app1 h b)) (n x : PTm k) :
    Γ ⊢[PRAAx] app1 h (iter (sq m) n x) ≐ iter (sq s) n (app1 h x) :=
  fusion (fun x => by rw [app1_sq, app1_sq]; exact hmul x x) n x

/-! ## Instances -/

/-- `x ↦ x + 1`. -/
def stepOne : PTm 1 := succ (var 0)
/-- `y ↦ y + 2`. -/
def stepTwo : PTm 1 := succ (succ (var 0))
/-- `x ↦ 2x`. -/
def dblMap : PTm 1 := two * var 0

/-- Doubling intertwines `+1` and `+2`: `2 · iter (+1) n x = iter (+2) n (2x)`, a closed
sentence with the local derivation supplied. -/
theorem double_iter : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (app1 dblMap (iter stepOne (var 0) (var 1)) ≐ iter stepTwo (var 0) (app1 dblMap (var 1))) :=
  fusion_closed (fun {k Γ} x => by
    have e₁ : app1 dblMap (app1 stepOne x) = two * succ x := by simp [app1, dblMap, stepOne]
    have e₂ : app1 stepTwo (app1 dblMap x) = succ (succ (two * x)) := by
      simp [app1, dblMap, stepTwo]
    rw [e₁, e₂]
    apply deriveNat; ipra_simps; ring)

/-- Multiplication `a · b`; variables `0 = a`, `1 = b`. -/
def mulT : PTm 2 := var 0 * var 1
/-- `a ↦ a²`. -/
def sqMap : PTm 1 := var 0 * var 0

/-- Squaring is multiplicative, so it commutes with repeated squaring: with
`s_{n+1} = s_n · s_n`, `(s_n)² = t_n` where `t_0 = x²`, `t_{n+1} = t_n · t_n`. -/
theorem square_squaring : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (app1 sqMap (iter (sq mulT) (var 0) (var 1)) ≐
      iter (sq mulT) (var 0) (app1 sqMap (var 1))) :=
  closeUniv 2 (squaring (fun {k Γ} a b => by
    have e₁ : app1 sqMap (inst2 mulT a b) = (a * b) * (a * b) := by
      simp [app1, sqMap, mulT, inst2]
    have e₂ : inst2 mulT (app1 sqMap a) (app1 sqMap b) = (a * a) * (b * b) := by
      simp [app1, sqMap, mulT, inst2]
    rw [e₁, e₂]
    apply deriveNat; ipra_simps; ring) _ _)

end LeanProofs.IPRA.Foundations.IterationFusion
