import IPRADerivations.DiophantineNumberTheory.HurwitzExtraction
import IPRADerivations.Core.LinearCombination

/-!
# The extraction loop of the continued-fraction prefix (`hurwitz_khinchin_ipra`)

Packet: `diophantine-number-theory/hurwitz_khinchin_ipra`, `hurwitz.tex`, §"Why the continued-fraction prefix
can be obtained primitively recursively": "Iterating this finite procedure through `a_{B+3}` supplies the
prefix … The loop invariants consist of determinant, positivity, and rational enclosure certificates; they are
decidable finite conditions. This is the promised path to a quantifier-free induction proof."

For an approximation `y = Y/W` the state `s = ⟨P, ⟨Q, ⟨P', Q'⟩⟩⟩` (the convergents `P/Q`, `P'/Q'`) is iterated by
`rec2` (`state`, `state_zero`, `state_succ`): with `Dn = |QY − PW|`, `A = |P'W − Q'Y|` and the digit
`a = ⌊A/Dn⌋`, the next state is `⟨aP + P', ⟨aQ + Q', ⟨P, Q⟩⟩⟩` (`nxt`).

The invariant `Inv` is: the approximation lies in one of the two sign regions (`R1`: `PW ≤ QY`, `Q'Y ≤ P'W`;
`R2`: the reverse), and the determinant is `±1`. `inv_step`: `Inv` and `Dn ≥ 1` give `Inv` of the next state
(`HurwitzExtraction.region_flip`, `region_flip'`, `det_step`, `det_step'`; the digit satisfies `a Dn ≤ A` by
division). `loop_inv`: if `Dn ≥ 1` at every state `n < N` — the positivity certificate, supplied by the
irrationality modulus — then `Inv` holds at every state `n ≤ N`, by one quantifier-free induction.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.HurwitzLoop

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.DiophantineNumberTheory.HurwitzExtraction (adist adist_of_le det_step det_step' region_flip
  region_flip')
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The state and its step -/

abbrev sP (s : PTm n) : PTm n := fstT s
abbrev sQ (s : PTm n) : PTm n := fstT (sndT s)
abbrev sP' (s : PTm n) : PTm n := fstT (sndT (sndT s))
abbrev sQ' (s : PTm n) : PTm n := sndT (sndT (sndT s))

/-- `⟨P, ⟨Q, ⟨P', Q'⟩⟩⟩`. -/
abbrev st (P Q P' Q' : PTm n) : PTm n := pairT P (pairT Q (pairT P' Q'))

/-- `Dn = |QY − PW|`. -/
abbrev Dn (s Y W : PTm n) : PTm n := adist (sQ s * Y) (sP s * W)
/-- `A = |P'W − Q'Y|`. -/
abbrev An (s Y W : PTm n) : PTm n := adist (sP' s * W) (sQ' s * Y)
/-- The digit `⌊A/Dn⌋`. -/
abbrev dig (s Y W : PTm n) : PTm n := quo (An s Y W) (Dn s Y W)
/-- The next state `⟨aP + P', ⟨aQ + Q', ⟨P, Q⟩⟩⟩`. -/
abbrev nxt (s Y W : PTm n) : PTm n :=
  st (dig s Y W * sP s + sP' s) (dig s Y W * sQ s + sQ' s) (sP s) (sQ s)

/-- The step body over `0 = n`, `1 = s`, `2 = ⟨s₀, ⟨Y, W⟩⟩`. -/
abbrev stepB : PTm 3 := nxt (var 1) (fstT (sndT (var 2))) (sndT (sndT (var 2)))

/-- The state after `n` steps from `s₀`. -/
def state (k s0 Y W : PTm n) : PTm n := ap2 (rec2 (fstT (var 0)) stepB) k (pairT s0 (pairT Y W))

@[simp] theorem subst_state {m : ℕ} (σ : Fin n → PTm m) (k s0 Y W : PTm n) :
    Syn.subst σ (state k s0 Y W) = state (Syn.subst σ k) (Syn.subst σ s0) (Syn.subst σ Y) (Syn.subst σ W) := by
  simp [state]

theorem congrNxt {s s' Y Y' W W' : PTm n} (hs : Γ ⊢[PRAAx] s ≐ s') (hY : Γ ⊢[PRAAx] Y ≐ Y')
    (hW : Γ ⊢[PRAAx] W ≐ W') : Γ ⊢[PRAAx] nxt s Y W ≐ nxt s' Y' W' := by
  have e := Prf.eqCongr (Γ := Γ) (nxt (var 0) (var 1) (var 2) : PTm 3) (σ := ![s, Y, W]) (σ' := ![s', Y', W'])
    (fun j => by fin_cases j <;> assumption)
  simpa [subst_ap2] using e

theorem state_zero (s0 Y W : PTm n) : Γ ⊢[PRAAx] state zero s0 Y W ≐ s0 := by
  unfold state
  have h := rec2_zero (Γ := Γ) (fstT (var 0)) stepB (pairT s0 (pairT Y W))
  exact h.eqTrans (by simpa using fst_pair (Γ := Γ) s0 (pairT Y W))

theorem state_succ (k s0 Y W : PTm n) :
    Γ ⊢[PRAAx] state (succ k) s0 Y W ≐ nxt (state k s0 Y W) Y W := by
  unfold state
  have h := rec2_succ (Γ := Γ) (fstT (var 0)) stepB k (pairT s0 (pairT Y W))
  have e : Syn.subst ![k, ap2 (rec2 (fstT (var 0)) stepB) k (pairT s0 (pairT Y W)), pairT s0 (pairT Y W)] stepB =
      nxt (ap2 (rec2 (fstT (var 0)) stepB) k (pairT s0 (pairT Y W))) (fstT (sndT (pairT s0 (pairT Y W))))
        (sndT (sndT (pairT s0 (pairT Y W)))) := by
    simp [subst_ap2]
  rw [e] at h
  refine h.eqTrans (congrNxt (.eqRefl _) ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))
    ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)))

/-! ## The invariant -/

abbrev R1 (s Y W : PTm n) : Fm PTm n := le (sP s * W) (sQ s * Y) ⋏ le (sQ' s * Y) (sP' s * W)
abbrev R2 (s Y W : PTm n) : Fm PTm n := le (sQ s * Y) (sP s * W) ⋏ le (sP' s * W) (sQ' s * Y)
abbrev detP (s : PTm n) : Fm PTm n := sP' s * sQ s ≐ sP s * sQ' s + one
abbrev detM (s : PTm n) : Fm PTm n := sP s * sQ' s ≐ sP' s * sQ s + one

/-- The loop invariant: a sign region and a unit determinant. -/
def Inv (s Y W : PTm n) : Fm PTm n := (R1 s Y W ⋎ R2 s Y W) ⋏ (detP s ⋎ detM s)

@[simp] theorem subst_Inv {k : ℕ} (σ : Fin n → PTm k) (s Y W : PTm n) :
    (Inv s Y W).subst σ = Inv (Syn.subst σ s) (Syn.subst σ Y) (Syn.subst σ W) := by
  simp [Inv]

theorem inv_QF (s Y W : PTm n) : (Inv s Y W).QF := by
  simp [Inv, Fm.QF, le_QF]

/-- The projections of an explicit state. -/
theorem proj_st (P Q P' Q' : PTm n) :
    (Γ ⊢[PRAAx] sP (st P Q P' Q') ≐ P) ∧ (Γ ⊢[PRAAx] sQ (st P Q P' Q') ≐ Q) ∧
      (Γ ⊢[PRAAx] sP' (st P Q P' Q') ≐ P') ∧ (Γ ⊢[PRAAx] sQ' (st P Q P' Q') ≐ Q') := by
  have s1 : Γ ⊢[PRAAx] sndT (st P Q P' Q') ≐ pairT Q (pairT P' Q') := snd_pair _ _
  have s2 : Γ ⊢[PRAAx] sndT (sndT (st P Q P' Q')) ≐ pairT P' Q' := (congrSnd s1).eqTrans (snd_pair _ _)
  exact ⟨fst_pair _ _, (congrFst s1).eqTrans (fst_pair _ _), (congrFst s2).eqTrans (fst_pair _ _),
    (congrSnd s2).eqTrans (snd_pair _ _)⟩

/-- The invariant at an explicit state from facts about its components. -/
theorem inv_of {P Q P' Q' Y W : PTm n}
    (hR : Γ ⊢[PRAAx] (le (P * W) (Q * Y) ⋏ le (Q' * Y) (P' * W)) ⋎ (le (Q * Y) (P * W) ⋏ le (P' * W) (Q' * Y)))
    (hd : Γ ⊢[PRAAx] (P' * Q ≐ P * Q' + one) ⋎ (P * Q' ≐ P' * Q + one)) :
    Γ ⊢[PRAAx] Inv (st P Q P' Q') Y W := by
  obtain ⟨p1, p2, p3, p4⟩ := proj_st (Γ := Γ) P Q P' Q'
  have m : ∀ {a b : PTm n}, (Γ ⊢[PRAAx] a ≐ b) → (Γ ⊢[PRAAx] a * W ≐ b * W) := fun h => congrMul h (.eqRefl _)
  have m' : ∀ {a b : PTm n}, (Γ ⊢[PRAAx] a ≐ b) → (Γ ⊢[PRAAx] a * Y ≐ b * Y) := fun h => congrMul h (.eqRefl _)
  refine .andI ?_ ?_
  · refine .orE hR ?_ ?_
    · exact .orI₁ (.andI (le_congr (m p1).wk.eqSymm (m' p2).wk.eqSymm (Prf.andE₁ Prf.hyp0))
        (le_congr (m' p4).wk.eqSymm (m p3).wk.eqSymm (Prf.andE₂ Prf.hyp0)))
    · exact .orI₂ (.andI (le_congr (m' p2).wk.eqSymm (m p1).wk.eqSymm (Prf.andE₁ Prf.hyp0))
        (le_congr (m p3).wk.eqSymm (m' p4).wk.eqSymm (Prf.andE₂ Prf.hyp0)))
  · refine .orE hd ?_ ?_
    · exact .orI₁ ((congrMul p3.wk p2.wk).eqTrans (Prf.hyp0.eqTrans (congrAdd (congrMul p1.wk p4.wk).eqSymm (.eqRefl _))))
    · exact .orI₂ ((congrMul p1.wk p4.wk).eqTrans (Prf.hyp0.eqTrans (congrAdd (congrMul p3.wk p2.wk).eqSymm (.eqRefl _))))

/-- The invariant is a congruence in the state. -/
theorem inv_congr {s s' Y W : PTm n} (h : Γ ⊢[PRAAx] s ≐ s') (hi : Γ ⊢[PRAAx] Inv s Y W) :
    Γ ⊢[PRAAx] Inv s' Y W := by
  have eP : Γ ⊢[PRAAx] sP s ≐ sP s' := congrFst h
  have eQ : Γ ⊢[PRAAx] sQ s ≐ sQ s' := congrFst (congrSnd h)
  have eP' : Γ ⊢[PRAAx] sP' s ≐ sP' s' := congrFst (congrSnd (congrSnd h))
  have eQ' : Γ ⊢[PRAAx] sQ' s ≐ sQ' s' := congrSnd (congrSnd (congrSnd h))
  have hR : Γ ⊢[PRAAx] (le (sP s' * W) (sQ s' * Y) ⋏ le (sQ' s' * Y) (sP' s' * W)) ⋎
      (le (sQ s' * Y) (sP s' * W) ⋏ le (sP' s' * W) (sQ' s' * Y)) := by
    refine .orE (Prf.andE₁ hi) ?_ ?_
    · exact .orI₁ (.andI (le_congr (congrMul eP.wk (.eqRefl _)) (congrMul eQ.wk (.eqRefl _)) (Prf.andE₁ Prf.hyp0))
        (le_congr (congrMul eQ'.wk (.eqRefl _)) (congrMul eP'.wk (.eqRefl _)) (Prf.andE₂ Prf.hyp0)))
    · exact .orI₂ (.andI (le_congr (congrMul eQ.wk (.eqRefl _)) (congrMul eP.wk (.eqRefl _)) (Prf.andE₁ Prf.hyp0))
        (le_congr (congrMul eP'.wk (.eqRefl _)) (congrMul eQ'.wk (.eqRefl _)) (Prf.andE₂ Prf.hyp0)))
  have hd : Γ ⊢[PRAAx] (sP' s' * sQ s' ≐ sP s' * sQ' s' + one) ⋎ (sP s' * sQ' s' ≐ sP' s' * sQ s' + one) := by
    refine .orE (Prf.andE₂ hi) ?_ ?_
    · exact .orI₁ ((congrMul eP'.wk eQ.wk).eqSymm.eqTrans (Prf.hyp0.eqTrans (congrAdd (congrMul eP.wk eQ'.wk) (.eqRefl _))))
    · exact .orI₂ ((congrMul eP.wk eQ'.wk).eqSymm.eqTrans (Prf.hyp0.eqTrans (congrAdd (congrMul eP'.wk eQ.wk) (.eqRefl _))))
  exact .andI hR hd

/-- `x ≤ y` gives `y = x + |y − x|`. -/
theorem add_adist {x y : PTm n} (h : Γ ⊢[PRAAx] le x y) : Γ ⊢[PRAAx] y ≐ x + adist y x := by
  ipra_lc natEq (eq_add_of_le h) - natEq h

/-- `x ≤ y` gives `y = x + |x − y|`. -/
theorem add_adist' {x y : PTm n} (h : Γ ⊢[PRAAx] le x y) : Γ ⊢[PRAAx] y ≐ x + adist x y := by
  ipra_lc natEq (eq_add_of_le h) - natEq h

/-- `⌊x/y⌋ y ≤ x` for `y ≥ 1`. -/
theorem quo_mul_le {x y : PTm n} (hy : Γ ⊢[PRAAx] y ≐ succ (pred y)) : Γ ⊢[PRAAx] le (quo x y * y) x := by
  have d := div_mod_at (Γ := Γ) (x := x) hy
  have e := natEq (Prf.andE₁ d)
  exact le_of_eq_add (d := rem x y) (by apply deriveNat; ipra_simps; linear_combination e)

/-- One step of the loop: `Inv` and `Dn ≥ 1` give `Inv` of the next state; the sign region flips and the
determinant changes sign. -/
theorem inv_step {s Y W : PTm n} (hi : Γ ⊢[PRAAx] Inv s Y W) (hD : Γ ⊢[PRAAx] Dn s Y W ≐ succ (pred (Dn s Y W))) :
    Γ ⊢[PRAAx] Inv (nxt s Y W) Y W := by
  have ha : Γ ⊢[PRAAx] le (dig s Y W * Dn s Y W) (An s Y W) := quo_mul_le hD
  refine inv_of ?_ ?_
  · refine .orE (Prf.andE₁ hi) ?_ ?_
    · have hD1 : (R1 s Y W :: Γ) ⊢[PRAAx] sQ s * Y ≐ sP s * W + Dn s Y W := add_adist (Prf.andE₁ Prf.hyp0)
      have hA1 : (R1 s Y W :: Γ) ⊢[PRAAx] sP' s * W ≐ sQ' s * Y + An s Y W := add_adist (Prf.andE₂ Prf.hyp0)
      exact .orI₂ (.andI (le_of_eq_add (region_flip hA1 hD1 ha.wk)) (Prf.andE₁ Prf.hyp0))
    · have hD2 : (R2 s Y W :: Γ) ⊢[PRAAx] sP s * W ≐ sQ s * Y + Dn s Y W := add_adist' (Prf.andE₁ Prf.hyp0)
      have hA2 : (R2 s Y W :: Γ) ⊢[PRAAx] sQ' s * Y ≐ sP' s * W + An s Y W := add_adist' (Prf.andE₂ Prf.hyp0)
      exact .orI₁ (.andI (le_of_eq_add (region_flip' hA2 hD2 ha.wk)) (Prf.andE₁ Prf.hyp0))
  · refine .orE (Prf.andE₂ hi) ?_ ?_
    · exact .orI₂ (det_step Prf.hyp0)
    · exact .orI₁ (det_step' Prf.hyp0)

/-- The loop invariant: if `Dn ≥ 1` at every state `j < N` (the positivity certificate), then every state `k ≤ N`
satisfies `Inv`. -/
theorem loop_inv_all (s0 Y W N : PTm n) (h0 : Γ ⊢[PRAAx] Inv s0 Y W)
    (hpos : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      Dn (state (var 0) (Syn.shift s0) (Syn.shift Y) (Syn.shift W)) (Syn.shift Y) (Syn.shift W) ≐
        succ (pred (Dn (state (var 0) (Syn.shift s0) (Syn.shift Y) (Syn.shift W)) (Syn.shift Y) (Syn.shift W))))) :
    Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift N) ⟶
      Inv (state (var 0) (Syn.shift s0) (Syn.shift Y) (Syn.shift W)) (Syn.shift Y) (Syn.shift W)) := by
  refine PRA.qfInd _ ⟨le_QF _ _, inv_QF _ _ _⟩ ?_ ?_
  · simp only [Fm.subst_imp, subst_le, subst_Inv, subst_state, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
    exact .impI (inv_congr (state_zero _ _ _).eqSymm h0.wk)
  · simp only [Fm.subst_imp, subst_le, subst_Inv, subst_state, Syn.subst_var, Syn.repl_zero, subst_repl_shift]
    refine .impI ?_
    let Θ : List (Fm PTm (n + 1)) := le (succ (var 0)) (Syn.shift N) ::
      (le (var 0) (Syn.shift N) ⟶
        Inv (state (var 0) (Syn.shift s0) (Syn.shift Y) (Syn.shift W)) (Syn.shift Y) (Syn.shift W)) ::
      Γ.map Fm.shift
    have hle : Θ ⊢[PRAAx] le (var 0) (Syn.shift N) := le_trans (le_succ_self _) Prf.hyp0
    have ih : Θ ⊢[PRAAx] Inv (state (var 0) (Syn.shift s0) (Syn.shift Y) (Syn.shift W)) (Syn.shift Y) (Syn.shift W) :=
      Prf.impE Prf.hyp1 hle
    have hD : Θ ⊢[PRAAx] Dn (state (var 0) (Syn.shift s0) (Syn.shift Y) (Syn.shift W)) (Syn.shift Y) (Syn.shift W) ≐
        succ (pred (Dn (state (var 0) (Syn.shift s0) (Syn.shift Y) (Syn.shift W)) (Syn.shift Y) (Syn.shift W))) :=
      Prf.impE hpos.allOpen.wk.wk Prf.hyp0
    exact inv_congr (state_succ _ _ _ _).eqSymm (inv_step ih hD)

/-- The loop invariant at the final state `N`. -/
theorem loop_inv (s0 Y W N : PTm n) (h0 : Γ ⊢[PRAAx] Inv s0 Y W)
    (hpos : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      Dn (state (var 0) (Syn.shift s0) (Syn.shift Y) (Syn.shift W)) (Syn.shift Y) (Syn.shift W) ≐
        succ (pred (Dn (state (var 0) (Syn.shift s0) (Syn.shift Y) (Syn.shift W)) (Syn.shift Y) (Syn.shift W))))) :
    Γ ⊢[PRAAx] Inv (state N s0 Y W) Y W := by
  have h2 := Prf.allE N (loop_inv_all s0 Y W N h0 hpos)
  simp only [Fm.subst_imp, subst_le, subst_Inv, subst_state, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at h2
  exact .impE h2 (le_refl N)

end LeanProofs.IPRA.DiophantineNumberTheory.HurwitzLoop
