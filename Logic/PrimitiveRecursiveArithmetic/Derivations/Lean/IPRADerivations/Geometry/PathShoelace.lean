import IPRADerivations.Core.SumReflect
import IPRADerivations.Core.Tactic
import IPRADerivations.Core.LinearCombination

/-!
# The open-path shoelace functional (`conway_criterion_ipra`, `lem:Jlaws`)

Packet: `geometry/conway_criterion_ipra_2026-11-16`, Section "The open-path shoelace
functional", Lemma `lem:Jlaws`, for paths of arbitrary length.

A path `p_0, …, p_k` in the first quadrant is given by two coordinate terms `x(i, p)`,
`y(i, p)` (variables `0 = i`, `1 = p`). The functional `J(P) = ∑_{i<k} det(p_i, p_{i+1})` is
kept as the pair of natural sums

`J⁺ = ∑_{i<k} x_i y_{i+1}` (`jp`), `J⁻ = ∑_{i<k} x_{i+1} y_i` (`jm`), `J = J⁺ − J⁻`,

and every law is an equation between natural numbers.

* `J_translate` (`eq:Jtranslate`): for the path translated by `w = (u, v)`,
  `J(P + w) = J(P) + det(w, p_k − p_0)`, i.e.
  `J⁺' + J⁻ + u y_0 + v x_k = J⁻' + J⁺ + u y_k + v x_0`; closed form `J_translate_closed`.
  The proof is the packet's: each edge contributes `det(w, p_{i+1} − p_i)` and these
  telescope; here it is one induction on `k` with a polynomial step.
* `J_reverse` (`eq:Jreverse`): for the reversed path `i ↦ p_{k−i}`, `J⁺` and `J⁻` are
  exchanged: `J(rev P) = −J(P)` (`J_reverse_plus`, `J_reverse_minus`).

Not derived: the half-turn law `eq:Jhalf` (it needs signed coordinates), concatenation as an
operation on two separately given paths, and `lem:Jcentral`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Geometry.PathShoelace

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {k : ℕ} {Γ : List (Fm PTm k)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The two sums -/

section Sums

variable (x y : PTm 2)

/-- `x_i · y_{i+1}`. -/
def pB : PTm 2 := x * shiftBody y
/-- `x_{i+1} · y_i`. -/
def mB : PTm 2 := shiftBody x * y

theorem inst2_pB (i p : PTm k) : inst2 (pB x y) i p = inst2 x i p * inst2 y (succ i) p := by
  have h : inst2 (pB x y) i p = inst2 x i p * inst2 (shiftBody y) i p := by simp [inst2, pB]
  rw [h, inst2_shiftBody]

theorem inst2_mB (i p : PTm k) : inst2 (mB x y) i p = inst2 x (succ i) p * inst2 y i p := by
  have h : inst2 (mB x y) i p = inst2 (shiftBody x) i p * inst2 y i p := by simp [inst2, mB]
  rw [h, inst2_shiftBody]

/-- `J⁺ = ∑_{i<n} x_i y_{i+1}`. -/
abbrev jp (n p : PTm k) : PTm k := ap2 (sumF (pB x y)) n p
/-- `J⁻ = ∑_{i<n} x_{i+1} y_i`. -/
abbrev jm (n p : PTm k) : PTm k := ap2 (sumF (mB x y)) n p

end Sums

/-! ## Translation -/

section Translate

variable (x y : PTm 2)

/-- `x_i + u`; variables `0 = i`, `1 = ⟨u, ⟨v, p⟩⟩`. -/
def trX : PTm 2 := inst2 x (var 0) (sndT (sndT (var 1))) + fstT (var 1)
/-- `y_i + v`; variables `0 = i`, `1 = ⟨u, ⟨v, p⟩⟩`. -/
def trY : PTm 2 := inst2 y (var 0) (sndT (sndT (var 1))) + fstT (sndT (var 1))

theorem trX_at (i u v p : PTm k) :
    Γ ⊢[PRAAx] inst2 (trX x) i (pairT u (pairT v p)) ≐ inst2 x i p + u := by
  have e : inst2 (trX x) i (pairT u (pairT v p)) =
      inst2 x i (sndT (sndT (pairT u (pairT v p)))) + fstT (pairT u (pairT v p)) := by
    show Syn.subst ![i, pairT u (pairT v p)] (trX x) = _
    simp [trX]
  rw [e]
  exact congrAdd (congrInst2 x (.eqRefl _) ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)))
    (fst_pair _ _)

theorem trY_at (i u v p : PTm k) :
    Γ ⊢[PRAAx] inst2 (trY y) i (pairT u (pairT v p)) ≐ inst2 y i p + v := by
  have e : inst2 (trY y) i (pairT u (pairT v p)) =
      inst2 y i (sndT (sndT (pairT u (pairT v p)))) + fstT (sndT (pairT u (pairT v p))) := by
    show Syn.subst ![i, pairT u (pairT v p)] (trY y) = _
    simp [trY]
  rw [e]
  exact congrAdd (congrInst2 y (.eqRefl _) ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)))
    ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))

/-- One more edge: the step of the translation law. -/
theorem translate_step {n u v p : PTm k}
    (ih : Γ ⊢[PRAAx] jp (trX x) (trY y) n (pairT u (pairT v p)) + jm x y n p +
        u * inst2 y zero p + v * inst2 x n p ≐
      jm (trX x) (trY y) n (pairT u (pairT v p)) + jp x y n p +
        u * inst2 y n p + v * inst2 x zero p) :
    Γ ⊢[PRAAx] jp (trX x) (trY y) (succ n) (pairT u (pairT v p)) + jm x y (succ n) p +
        u * inst2 y zero p + v * inst2 x (succ n) p ≐
      jm (trX x) (trY y) (succ n) (pairT u (pairT v p)) + jp x y (succ n) p +
        u * inst2 y (succ n) p + v * inst2 x zero p := by
  have s₁ := sum_succ' (Γ := Γ) (pB (trX x) (trY y)) n (pairT u (pairT v p))
  rw [inst2_pB] at s₁
  have s₂ := sum_succ' (Γ := Γ) (mB x y) n p
  rw [inst2_mB] at s₂
  have s₃ := sum_succ' (Γ := Γ) (mB (trX x) (trY y)) n (pairT u (pairT v p))
  rw [inst2_mB] at s₃
  have s₄ := sum_succ' (Γ := Γ) (pB x y) n p
  rw [inst2_pB] at s₄
  ipra_lc natEq ih + natEq s₁ + natEq s₂ - natEq s₃ - natEq s₄ +
    𝔞 (inst2 (trY y) (succ n) (pairT u (pairT v p))) * natEq (trX_at (Γ := Γ) x n u v p) +
    (𝔞 (inst2 x n p) + 𝔞 u) * natEq (trY_at (Γ := Γ) y (succ n) u v p) -
    𝔞 (inst2 (trY y) n (pairT u (pairT v p))) * natEq (trX_at (Γ := Γ) x (succ n) u v p) -
    (𝔞 (inst2 x (succ n) p) + 𝔞 u) * natEq (trY_at (Γ := Γ) y n u v p)

/-- Variables: `0 = n`, `1 = u`, `2 = v`, `3 = p`. -/
private def trF (x y : PTm 2) : Fm PTm 4 :=
  jp (trX x) (trY y) (var 0) (pairT (var 1) (pairT (var 2) (var 3))) + jm x y (var 0) (var 3) +
      var 1 * inst2 y zero (var 3) + var 2 * inst2 x (var 0) (var 3) ≐
    jm (trX x) (trY y) (var 0) (pairT (var 1) (pairT (var 2) (var 3))) + jp x y (var 0) (var 3) +
      var 1 * inst2 y (var 0) (var 3) + var 2 * inst2 x zero (var 3)

private theorem tr₀ : ([] : List (Fm PTm 4)) ⊢[PRAAx] trF x y := by
  refine ind _ trivial ?_ ?_
  · ipra_lc [trF, Fm.subst_eq, PTm.subst_add, PTm.subst_mul, subst_ap2, subst_pairT, subst_inst2, Syn.subst_var, Syn.inst_zero, Syn.inst_one, inst_two, inst_three, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] natEq (sum_zero (Γ := ([] : List (Fm PTm 3))) (pB (trX x) (trY y)) (pairT (var 0) (pairT (var 1) (var 2)))) +
      natEq (sum_zero (Γ := ([] : List (Fm PTm 3))) (mB x y) (var 2)) -
      natEq (sum_zero (Γ := ([] : List (Fm PTm 3))) (mB (trX x) (trY y)) (pairT (var 0) (pairT (var 1) (var 2)))) -
      natEq (sum_zero (Γ := ([] : List (Fm PTm 3))) (pB x y) (var 2))
  · simp only [trF, Fm.subst_eq, PTm.subst_add, PTm.subst_mul, subst_ap2, subst_pairT,
      subst_inst2, Syn.subst_var, Syn.repl_zero, repl_one, repl_two, repl_three,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    have ih : [trF x y] ⊢[PRAAx]
        jp (trX x) (trY y) (var 0) (pairT (var 1) (pairT (var 2) (var 3))) +
            jm x y (var 0) (var 3) + var 1 * inst2 y zero (var 3) +
            var 2 * inst2 x (var 0) (var 3) ≐
          jm (trX x) (trY y) (var 0) (pairT (var 1) (pairT (var 2) (var 3))) +
            jp x y (var 0) (var 3) + var 1 * inst2 y (var 0) (var 3) +
            var 2 * inst2 x zero (var 3) := Prf.hyp0
    exact translate_step x y ih

/-- `eq:Jtranslate`: `J(P + w) = J(P) + det(w, p_n − p_0)` for `w = (u, v)`, as an equation of
natural numbers. -/
theorem J_translate (n u v p : PTm k) :
    Γ ⊢[PRAAx] jp (trX x) (trY y) n (pairT u (pairT v p)) + jm x y n p +
        u * inst2 y zero p + v * inst2 x n p ≐
      jm (trX x) (trY y) n (pairT u (pairT v p)) + jp x y n p +
        u * inst2 y n p + v * inst2 x zero p := by
  have i := inst (Γ := Γ) (tr₀ x y) (![n, u, v, p] : Fin 4 → PTm k)
  simpa [trF] using i

/-- `eq:Jtranslate` as a closed sentence, for all coordinate terms. Variables: `0 = n`,
`1 = u`, `2 = v`, `3 = p`. -/
theorem J_translate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (jp (trX x) (trY y) (var 0) (pairT (var 1) (pairT (var 2) (var 3))) + jm x y (var 0) (var 3) +
        var 1 * inst2 y zero (var 3) + var 2 * inst2 x (var 0) (var 3) ≐
      jm (trX x) (trY y) (var 0) (pairT (var 1) (pairT (var 2) (var 3))) + jp x y (var 0) (var 3) +
        var 1 * inst2 y (var 0) (var 3) + var 2 * inst2 x zero (var 3)) :=
  closeUniv 4 (J_translate x y _ _ _ _)

end Translate

/-! ## Reversal -/

section Reverse

variable (x y : PTm 2)

/-- `(n ∸ (i + 1)) + 1 = n ∸ i` for `i < n`. -/
theorem succ_monus_lt {i n : PTm k} (h : Γ ⊢[PRAAx] lt i n) :
    Γ ⊢[PRAAx] succ (monus n (succ i)) ≐ monus n i := by
  ipra_lc natEq (eq_add_of_le (le_trans (le_succ_self i) h)) - natEq (eq_add_of_le h)

/-- The reversed coordinate `i ↦ x_{n ∸ i}`; variables `0 = i`, `1 = ⟨n, p⟩`. -/
def rvB : PTm 2 := inst2 x (monus (fstT (var 1)) (var 0)) (sndT (var 1))

theorem rvB_at (i n p : PTm k) :
    Γ ⊢[PRAAx] inst2 (rvB x) i (pairT n p) ≐ inst2 x (monus n i) p := by
  have e : inst2 (rvB x) i (pairT n p) =
      inst2 x (monus (fstT (pairT n p)) i) (sndT (pairT n p)) := by
    show Syn.subst ![i, pairT n p] (rvB x) = _
    simp [rvB]
  rw [e]
  exact congrInst2 x (congrMonus (fst_pair _ _) (.eqRefl _)) (snd_pair _ _)

/-- The reflected summand of `J⁻` is the summand of `J⁺` of the reversed path. -/
theorem rev_pt {i n p : PTm k} (h : Γ ⊢[PRAAx] lt i n) :
    Γ ⊢[PRAAx] inst2 (rflBody (mB x y)) i (pairT n p) ≐
      inst2 (pB (rvB x) (rvB y)) i (pairT n p) := by
  rw [inst2_rflBody, inst2_pB]
  have i₁ : Γ ⊢[PRAAx] monus (fstT (pairT n p)) (succ i) ≐ monus n (succ i) :=
    congrMonus (fst_pair _ _) (.eqRefl _)
  refine (congrInst2 (mB x y) i₁ (snd_pair n p)).eqTrans ?_
  rw [inst2_mB]
  refine .eqTrans ?_ (congrMul (rvB_at x i n p) (rvB_at y (succ i) n p)).eqSymm
  exact congrMul (congrInst2 x (succ_monus_lt h) (.eqRefl _)) (.eqRefl _)

/-- The reflected summand of `J⁺` is the summand of `J⁻` of the reversed path. -/
theorem rev_pt' {i n p : PTm k} (h : Γ ⊢[PRAAx] lt i n) :
    Γ ⊢[PRAAx] inst2 (rflBody (pB x y)) i (pairT n p) ≐
      inst2 (mB (rvB x) (rvB y)) i (pairT n p) := by
  rw [inst2_rflBody, inst2_mB]
  have i₁ : Γ ⊢[PRAAx] monus (fstT (pairT n p)) (succ i) ≐ monus n (succ i) :=
    congrMonus (fst_pair _ _) (.eqRefl _)
  refine (congrInst2 (pB x y) i₁ (snd_pair n p)).eqTrans ?_
  rw [inst2_pB]
  refine .eqTrans ?_ (congrMul (rvB_at x (succ i) n p) (rvB_at y i n p)).eqSymm
  exact congrMul (.eqRefl _) (congrInst2 y (succ_monus_lt h) (.eqRefl _))

/-- `eq:Jreverse`, first half: `J⁺(rev P) = J⁻(P)`. -/
theorem J_reverse_plus (n p : PTm k) :
    Γ ⊢[PRAAx] jp (rvB x) (rvB y) n (pairT n p) ≐ jm x y n p := by
  refine .eqSymm ((sum_reflect (mB x y) n p).eqTrans ?_)
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  rw [shift_pairT]
  exact rev_pt x y Prf.hyp0

/-- `eq:Jreverse`, second half: `J⁻(rev P) = J⁺(P)`. Together: `J(rev P) = −J(P)`. -/
theorem J_reverse_minus (n p : PTm k) :
    Γ ⊢[PRAAx] jm (rvB x) (rvB y) n (pairT n p) ≐ jp x y n p := by
  refine .eqSymm ((sum_reflect (pB x y) n p).eqTrans ?_)
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  rw [shift_pairT]
  exact rev_pt' x y Prf.hyp0

end Reverse

end LeanProofs.IPRA.Geometry.PathShoelace
