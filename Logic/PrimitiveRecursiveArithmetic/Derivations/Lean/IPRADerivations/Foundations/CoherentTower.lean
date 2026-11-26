import IPRADerivations.Foundations.BoundedReflection
import IPRADerivations.Foundations.FiniteSetExponential
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.CommonLemmas
import IPRADerivations.Core.InductionTactic

/-!
# Coherent points from bounded surjective liftings (`ipra_categorical_methods`, `thm:tower`)

Packet: `foundations/ipra_categorical_methods`, Section 5, Subsection "The missing positive
resource: finite liftings", Theorem `thm:tower`.

A tower (`Tower`) is given by fixed terms: a bound `b(n)`, a membership test `V(a, n)` (read as
true when nonzero; for a Boolean `V` this is `V = 1`) and bonding maps `p(c, n)`, with

`A_n = {a < b(n) : V(a, n) ≠ 0}`, `p(·, n) : A_{n+1} → A_n`.

The lifting contract (`Tower.Lifting`, the packet's (5.3)) says that iPRA derives, for
`a ∈ A_n`, the bounded existence of `c < b(n + 1)` with `c ∈ A_{n+1}` and `p(c, n) = a`. It is
stated for the single test `T(c, ⟨n, a⟩) = V(c, n + 1) · [p(c, n) = a]`; `Lifting.of_conj`
obtains it from the conjunction form of the packet. No validity of the bonding maps on all of
`A_{n+1}` is needed for the conclusion.

The selector `sel(n, a)` is the least `c < b(n + 1)` passing the test (bounded search), and
the point is defined by primitive recursion, `pt(0, a₀) = a₀`, `pt(n + 1, a₀) = sel(n, pt(n, a₀))`
(`pt_zero`, `pt_succ`), with the supplied `a₀` kept as a numerical parameter. Then, for
`a₀ ∈ A_0`:

* `pt_mem`: `pt(n, a₀) ∈ A_n` for every `n`;
* `pt_coherent`: `p(pt(n + 1, a₀), n) = pt(n, a₀)` for every `n`;
* `tower_closed`: both, as one closed sentence of iPRA.

The induction is on the quantifier-free formula `a₀ ∈ A_0 → pt(n, a₀) ∈ A_n`; there is no
induction on an assertion that a whole tail exists.

`ex_mono` is the general rule `∃x A`, `A ⊢ B` gives `∃x B`.

Instance with every hypothesis discharged: the full binary tree, `A_n = [2^n]` with
truncation `c ↦ c mod 2^n` (`binary`, `binary_lifting`, `binary_closed`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.CoherentTower

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.BoundedReflection (wit bounded_choice one_ne_zero)
open LeanProofs.IPRA.Foundations.FiniteSetExponential (rem_of_lt)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (pw_pos' eq_of_eqb_ne)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {k : ℕ} {Γ : List (Fm PTm k)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Two general rules -/

/-- From `∃x A` and a derivation of `B` from `A`, `∃x B`. -/
theorem ex_mono {A B : Fm PTm (k + 1)} (h : Γ ⊢[PRAAx] Fm.ex A)
    (hAB : (A :: Γ.map Fm.shift) ⊢[PRAAx] B) : Γ ⊢[PRAAx] Fm.ex B := by
  refine .exE h ?_
  exact .exI (var 0) (by simpa only [Fm.shift, Fm.subst_ex, Fm.subst_up_succ_inst,
    List.map_cons] using hAB)

private alias eqb_congr' := Common.congrEqb

/-! ## Towers -/

/-- The data of a tower of finite sets. -/
structure Tower where
  /-- The bound `b(n)`; variable `0 = n`. -/
  b : PTm 1
  /-- The membership test `V(a, n)`, true when nonzero; variables `0 = a`, `1 = n`. -/
  V : PTm 2
  /-- The bonding map `p(c, n)` from level `n + 1` to level `n`; variables `0 = c`, `1 = n`. -/
  p : PTm 2

namespace Tower

variable (W : Tower)

/-- `b(n)`. -/
def bd (n : PTm k) : PTm k := Syn.subst ![n] W.b

@[simp] theorem subst_bd {m : ℕ} (σ : Fin k → PTm m) (n : PTm k) :
    Syn.subst σ (W.bd n) = W.bd (Syn.subst σ n) := by
  simp only [bd, Syn.subst_subst]
  congr 1; funext j; fin_cases j; rfl

/-- `a ∈ A_n`: `a < b(n)` and `V(a, n) ≠ 0`. -/
def mem (n a : PTm k) : Fm PTm k := lt a (W.bd n) ⋏ neg (inst2 W.V a n ≐ zero)

@[simp] theorem subst_mem {m : ℕ} (σ : Fin k → PTm m) (n a : PTm k) :
    (W.mem n a).subst σ = W.mem (Syn.subst σ n) (Syn.subst σ a) := by
  simp [mem]

/-- The lift test `T(c, ⟨n, a⟩) = V(c, n + 1) · [p(c, n) = a]`; variables `0 = c`,
`1 = ⟨n, a⟩`. -/
def T : PTm 2 :=
  inst2 W.V (var 0) (succ (fstT (var 1))) * eqb (inst2 W.p (var 0) (fstT (var 1))) (sndT (var 1))

/-- The selected lift `sel(n, a)`: the least `c < b(n + 1)` passing the test. -/
def sel (n a : PTm k) : PTm k := wit W.T (W.bd (succ n)) (pairT n a)

@[simp] theorem subst_sel {m : ℕ} (σ : Fin k → PTm m) (n a : PTm k) :
    Syn.subst σ (W.sel n a) = W.sel (Syn.subst σ n) (Syn.subst σ a) := by
  simp [sel]

/-- The step of the recursion; variables `0 = n`, `1 = pt(n, a₀)`, `2 = a₀`. -/
def stepT : PTm 3 := W.sel (var 0) (var 1)

/-- The point `pt(n, a₀)`. -/
def pt (n a₀ : PTm k) : PTm k := ap2 (rec2 (var 0) W.stepT) n a₀

@[simp] theorem subst_pt {m : ℕ} (σ : Fin k → PTm m) (n a₀ : PTm k) :
    Syn.subst σ (W.pt n a₀) = W.pt (Syn.subst σ n) (Syn.subst σ a₀) := by
  simp [pt]

/-- The lifting contract: for `a ∈ A_n` there is `c < b(n + 1)` passing the lift test. Stated
as a rule derivable at arbitrary terms and under arbitrary hypotheses. -/
structure Lifting : Prop where
  lift : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {n a : PTm k}, (Γ ⊢[PRAAx] W.mem n a) →
    (Γ ⊢[PRAAx] Fm.ex (lt (var 0) (Syn.shift (W.bd (succ n))) ⋏
      neg (inst2 W.T (var 0) (Syn.shift (pairT n a)) ≐ zero)))

end Tower

open Tower

section Laws

variable (W : Tower)

theorem T_at (c n a : PTm k) :
    Γ ⊢[PRAAx] inst2 W.T c (pairT n a) ≐ inst2 W.V c (succ n) * eqb (inst2 W.p c n) a := by
  have e : inst2 W.T c (pairT n a) =
      inst2 W.V c (succ (fstT (pairT n a))) *
        eqb (inst2 W.p c (fstT (pairT n a))) (sndT (pairT n a)) := by
    show Syn.subst ![c, pairT n a] W.T = _
    simp [Tower.T]
  rw [e]
  exact congrMul (congrInst2 W.V (.eqRefl _) (congrSucc (fst_pair _ _)))
    (eqb_congr' (congrInst2 W.p (.eqRefl _) (fst_pair _ _)) (snd_pair _ _))

/-- A candidate in `A_{n+1}` over `a` passes the test. -/
theorem T_ne_of {c n a : PTm k} (hV : Γ ⊢[PRAAx] neg (inst2 W.V c (succ n) ≐ zero))
    (hp : Γ ⊢[PRAAx] inst2 W.p c n ≐ a) : Γ ⊢[PRAAx] neg (inst2 W.T c (pairT n a) ≐ zero) := by
  refine .impI (.impE hV.wk ?_)
  have t := (T_at (Γ := (inst2 W.T c (pairT n a) ≐ zero) :: Γ) W c n a).eqSymm.eqTrans Prf.hyp0
  have one : ((inst2 W.T c (pairT n a) ≐ zero) :: Γ) ⊢[PRAAx]
      inst2 W.V c (succ n) ≐ inst2 W.V c (succ n) * succ zero :=
    (one_mul _).eqSymm.eqTrans (mul_comm _ _)
  exact (one.eqTrans (congrMul (.eqRefl _) (eqb_of_eq hp.wk).eqSymm)).eqTrans t

/-- A candidate passing the test has `V(c, n + 1) ≠ 0`. -/
theorem T_ne_V {c n a : PTm k} (h : Γ ⊢[PRAAx] neg (inst2 W.T c (pairT n a) ≐ zero)) :
    Γ ⊢[PRAAx] neg (inst2 W.V c (succ n) ≐ zero) := by
  refine .impI (.impE h.wk ?_)
  exact (T_at W c n a).eqTrans ((congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _))

/-- A candidate passing the test has `p(c, n) = a`. -/
theorem T_ne_p {c n a : PTm k} (h : Γ ⊢[PRAAx] neg (inst2 W.T c (pairT n a) ≐ zero)) :
    Γ ⊢[PRAAx] inst2 W.p c n ≐ a := by
  refine eq_of_eqb_ne (.impI (.impE h.wk ?_))
  exact (T_at W c n a).eqTrans ((congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero _))

/-- The lifting contract from the conjunction form of the packet:
`∃ c < b(n + 1). (V(c, n + 1) ≠ 0 ∧ p(c, n) = a)`. -/
theorem Lifting.of_conj
    (h : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {n a : PTm k}, (Γ ⊢[PRAAx] W.mem n a) →
      (Γ ⊢[PRAAx] Fm.ex (lt (var 0) (Syn.shift (W.bd (succ n))) ⋏
        (neg (inst2 W.V (var 0) (succ (Syn.shift n)) ≐ zero) ⋏
          (inst2 W.p (var 0) (Syn.shift n) ≐ Syn.shift a))))) : W.Lifting where
  lift := fun hm => by
    refine ex_mono (h hm) ?_
    rw [shift_pairT]
    exact .andI (.andE₁ Prf.hyp0)
      (T_ne_of W (.andE₁ (.andE₂ Prf.hyp0)) (.andE₂ (.andE₂ Prf.hyp0)))

theorem pt_zero (a₀ : PTm k) : Γ ⊢[PRAAx] W.pt zero a₀ ≐ a₀ := by
  simpa [Tower.pt] using rec2_zero (Γ := Γ) (var 0) W.stepT a₀

theorem pt_succ (n a₀ : PTm k) : Γ ⊢[PRAAx] W.pt (succ n) a₀ ≐ W.sel n (W.pt n a₀) := by
  have h := rec2_succ (Γ := Γ) (var 0) W.stepT n a₀
  have e : Syn.subst ![n, ap2 (rec2 (var 0) W.stepT) n a₀, a₀] W.stepT = W.sel n (W.pt n a₀) := by
    simp [Tower.stepT, Tower.pt]
  rw [e] at h
  exact h

/-- Membership respects equality of the element. -/
theorem mem_congr {n a a' : PTm k} (h : Γ ⊢[PRAAx] a ≐ a') (hm : Γ ⊢[PRAAx] W.mem n a) :
    Γ ⊢[PRAAx] W.mem n a' :=
  .andI (lt_congr h (.eqRefl _) (.andE₁ hm))
    (.impI (.impE (Prf.andE₂ hm).wk ((congrInst2 W.V h.wk (.eqRefl _)).eqTrans Prf.hyp0)))

variable {W}

/-- The selected lift of `a ∈ A_n` lies in `A_{n+1}` and is mapped to `a`. -/
theorem sel_spec (L : W.Lifting) {n a : PTm k} (hm : Γ ⊢[PRAAx] W.mem n a) :
    Γ ⊢[PRAAx] W.mem (succ n) (W.sel n a) ⋏ (inst2 W.p (W.sel n a) n ≐ a) := by
  have c := bounded_choice W.T (L.lift hm)
  exact .andI (.andI (.andE₁ c) (T_ne_V W (.andE₂ c))) (T_ne_p W (.andE₂ c))

/-- One step: from `pt(n, a₀) ∈ A_n`, the next point is in `A_{n+1}` and is mapped back. -/
theorem pt_step (L : W.Lifting) {n a₀ : PTm k} (ih : Γ ⊢[PRAAx] W.mem n (W.pt n a₀)) :
    Γ ⊢[PRAAx] W.mem (succ n) (W.pt (succ n) a₀) ⋏
      (inst2 W.p (W.pt (succ n) a₀) n ≐ W.pt n a₀) := by
  have s := sel_spec L ih
  have e := pt_succ (Γ := Γ) W n a₀
  exact .andI (mem_congr W e.eqSymm (.andE₁ s))
    ((congrInst2 W.p e (.eqRefl _)).eqTrans (.andE₂ s))

/-- Variables: `0 = n`, `1 = a₀`. -/
private def towerF (W : Tower) : Fm PTm 2 :=
  W.mem zero (var 1) ⟶ W.mem (var 0) (W.pt (var 0) (var 1))

private theorem tower₀ (L : W.Lifting) : ([] : List (Fm PTm 2)) ⊢[PRAAx] towerF W := by
  ipra_ind (⟨⟨trivial, trivial, trivial⟩, trivial, trivial, trivial⟩) [towerF, subst_mem, subst_pt]
  · exact .impI (mem_congr W (pt_zero W _).eqSymm Prf.hyp0)
  · have ih : [towerF W] ⊢[PRAAx] W.mem zero (var 1) ⟶ W.mem (var 0) (W.pt (var 0) (var 1)) :=
      Prf.hyp0
    exact .impI (.andE₁ (pt_step L (.impE ih.wk Prf.hyp0)))

/-- `thm:tower`, membership: `pt(n, a₀) ∈ A_n` for every `n`. -/
theorem pt_mem (L : W.Lifting) {a₀ : PTm k} (h₀ : Γ ⊢[PRAAx] W.mem zero a₀) (n : PTm k) :
    Γ ⊢[PRAAx] W.mem n (W.pt n a₀) := by
  have h := inst (Γ := Γ) (tower₀ L) (![n, a₀] : Fin 2 → PTm k)
  simp [towerF] at h
  exact .impE h h₀

/-- `thm:tower`, coherence: `p(pt(n + 1, a₀), n) = pt(n, a₀)` for every `n`. -/
theorem pt_coherent (L : W.Lifting) {a₀ : PTm k} (h₀ : Γ ⊢[PRAAx] W.mem zero a₀) (n : PTm k) :
    Γ ⊢[PRAAx] inst2 W.p (W.pt (succ n) a₀) n ≐ W.pt n a₀ :=
  .andE₂ (pt_step L (pt_mem L h₀ n))

/-- `thm:tower` as one closed sentence of iPRA. Variables: `0 = n`, `1 = a₀`. -/
theorem tower_closed (L : W.Lifting) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (W.mem zero (var 1) ⟶
      (W.mem (var 0) (W.pt (var 0) (var 1)) ⋏
        (inst2 W.p (W.pt (succ (var 0)) (var 1)) (var 0) ≐ W.pt (var 0) (var 1)))) :=
  closeUniv 2 (.impI (.andI (pt_mem L Prf.hyp0 _) (pt_coherent L Prf.hyp0 _)))

end Laws

/-! ## An instance: the full binary tree -/

/-- `A_n = [2^n]`, all words valid, bonding by truncation `c ↦ c mod 2^n`. -/
def binary : Tower where
  b := pw two (var 0)
  V := one
  p := rem (var 0) (pw two (var 1))

section Binary

theorem binary_bd (n : PTm k) : binary.bd n = pw two n := by simp [Tower.bd, binary]

theorem binary_V (a n : PTm k) : inst2 binary.V a n = one := by simp [inst2, binary]

theorem binary_p (c n : PTm k) : inst2 binary.p c n = rem c (pw two n) := by simp [inst2, binary]

theorem two_pos : Γ ⊢[PRAAx] (two : PTm k) ≐ succ (pred two) :=
  pos_of_eq_succ (c := one) (.eqRefl _)

/-- `a < 2^n` gives `a < 2^{n+1}`. -/
theorem lt_pw_succ {a n : PTm k} (h : Γ ⊢[PRAAx] lt a (pw two n)) :
    Γ ⊢[PRAAx] lt a (pw two (succ n)) := by
  refine le_of_eq_add (d := pw two n + monus (pw two n) (succ a)) ?_
  ipra_lc natEq (pw_succ (Γ := Γ) two n) + natEq (eq_add_of_le h)

/-- The lifting contract of the binary tree: a word of length `n` is its own lift. -/
theorem binary_lifting : binary.Lifting := by
  refine Lifting.of_conj binary (fun {k Γ n a} hm => ?_)
  have ha : Γ ⊢[PRAAx] lt a (pw two n) := by
    have h := Prf.andE₁ hm
    rw [binary_bd] at h
    exact h
  refine .exI a ?_
  simp only [Fm.subst_and, subst_lt, subst_neg, Fm.subst_eq, subst_inst2, Syn.subst_var,
    Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
  rw [binary_bd, binary_V, binary_p]
  exact .andI (lt_pw_succ ha) (.andI (.impI (one_ne_zero _ Prf.hyp0))
    (rem_of_lt (pw_pos' two_pos n) ha))

/-- The coherent point of the binary tree through any `a₀ < 1`, as a closed sentence. -/
theorem binary_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (binary.mem zero (var 1) ⟶
      (binary.mem (var 0) (binary.pt (var 0) (var 1)) ⋏
        (inst2 binary.p (binary.pt (succ (var 0)) (var 1)) (var 0) ≐
          binary.pt (var 0) (var 1)))) :=
  tower_closed binary_lifting

end Binary

end LeanProofs.IPRA.Foundations.CoherentTower
