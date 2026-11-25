import IPRADerivations.Foundations.AbelianCodes
import IPRADerivations.AnalyticNumberTheory.Totatives
import IPRADerivations.Core.LinearCombination

/-!
# Finite generation from a computable reducing step

Packet: `diophantine-number-theory/diophantine_geometry_ipra`, Theorem `thm:generation`: "Suppose ... primitive
recursive functions `D(P)` and `i(P)` such that, for every valid `P` with `h(P) > T`, ... `P = m D(P) + r_{i(P)}`,
`h(D(P)) < h(P)`. Then `R ∪ S` generates the group ... Keep a current point, an active-step count `k`, and ...
When the current point `Q` has height at most `T`, keep the whole state unchanged. Otherwise ... replace `Q` by
`D(Q)`, add `m^k` ... and increase `k` by one ... Throughout the iteration the following group identity is
maintained: `P = m^k Q + ∑ a_i r_i`."

The group is `Foundations/AbelianCodes` (operation `G`, neutral `num e`, laws as iPRA-provable schemas). The data
`h`, `D`, `i`, `r` are unary bodies (`ap1`), and the reduction hypotheses are iPRA-provable schemas, as in the
theorem. The state `⟨Q, ⟨k, A⟩⟩` is iterated by primitive recursion (`st`); `A` accumulates the generator
multiples `m^k r_{i(Q)}`.

* `st_zero`, `st_succ`: the iteration;
* `inv_step`, `invariant`: `P = m^k Q + A` at every stage;
* `height_step`, `height_bound`: `h(Q_j) ≤ T` or `h(Q_j) + j ≤ h(P)`, so after `h(P)` stages `h(Q) ≤ T`;
* `generation`: `P = m^k Q + A` with `h(Q) ≤ T` and `A` the accumulated generator multiples.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.GenerationDescent

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.AbelianCodes (op Assoc Comm IdL congrOp smul smulF congrSmul smul_op smul_mul)
open LeanProofs.IPRA.Signum (sg)
open LeanProofs.IPRA.AnalyticNumberTheory.Totatives (sg_lt sg_le)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

/-- A unary body `F(a)`. -/
abbrev ap1 (F : PTm 1) {n : ℕ} (a : PTm n) : PTm n := Syn.subst ![a] F

@[simp] theorem subst_ap1 {n m : ℕ} (σ : Fin n → PTm m) (F : PTm 1) (a : PTm n) :
    Syn.subst σ (ap1 F a) = ap1 F (Syn.subst σ a) := by
  simp only [ap1, Syn.subst_subst]
  congr 1; funext j; fin_cases j; rfl

theorem congrAp1 (F : PTm 1) {n : ℕ} {Δ : List (Fm PTm n)} {a a' : PTm n} (h : Δ ⊢[PRAAx] a ≐ a') :
    Δ ⊢[PRAAx] ap1 F a ≐ ap1 F a' :=
  Prf.eqCongr F fun j => by fin_cases j; exact h

section Iter

variable (G : PTm 2) (e T m : ℕ) (H D I R : PTm 1)

/-- The activity bit `[h(Q) > T]`. -/
abbrev act {n : ℕ} (Q : PTm n) : PTm n := sg (monus (ap1 H Q) (num T))

/-- One step on the state `⟨Q, ⟨k, A⟩⟩` (variable `1`). -/
abbrev stepB : PTm 3 :=
  pairT (act T H (fstT (var 1)) * ap1 D (fstT (var 1)) + monus one (act T H (fstT (var 1))) * fstT (var 1))
    (pairT (fstT (sndT (var 1)) + act T H (fstT (var 1)))
      (act T H (fstT (var 1)) * op G (sndT (sndT (var 1)))
          (smul G e (pw (num m) (fstT (sndT (var 1)))) (ap1 R (ap1 I (fstT (var 1))))) +
        monus one (act T H (fstT (var 1))) * sndT (sndT (var 1))))

/-- The initial state `⟨P, ⟨0, e⟩⟩`. -/
abbrev initB : PTm 1 := pairT (var 0) (pairT zero (num e))

/-- The state after `j` stages. -/
abbrev st {n : ℕ} (j P : PTm n) : PTm n := ap2 (rec2 (initB e) (stepB G e T m H D I R)) j P

abbrev Qs {n : ℕ} (s : PTm n) : PTm n := fstT s
abbrev ks {n : ℕ} (s : PTm n) : PTm n := fstT (sndT s)
abbrev As {n : ℕ} (s : PTm n) : PTm n := sndT (sndT s)

variable {G e T m H D I R}
variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem st_zero (P : PTm n) : Γ ⊢[PRAAx] st G e T m H D I R zero P ≐ pairT P (pairT zero (num e)) := by
  simpa using rec2_zero (Γ := Γ) (initB e) (stepB G e T m H D I R) P

theorem st_succ (j P : PTm n) :
    Γ ⊢[PRAAx] st G e T m H D I R (succ j) P ≐
      pairT (act T H (Qs (st G e T m H D I R j P)) * ap1 D (Qs (st G e T m H D I R j P)) +
          monus one (act T H (Qs (st G e T m H D I R j P))) * Qs (st G e T m H D I R j P))
        (pairT (ks (st G e T m H D I R j P) + act T H (Qs (st G e T m H D I R j P)))
          (act T H (Qs (st G e T m H D I R j P)) * op G (As (st G e T m H D I R j P))
              (smul G e (pw (num m) (ks (st G e T m H D I R j P))) (ap1 R (ap1 I (Qs (st G e T m H D I R j P))))) +
            monus one (act T H (Qs (st G e T m H D I R j P))) * As (st G e T m H D I R j P))) := by
  have h := rec2_succ (Γ := Γ) (initB e) (stepB G e T m H D I R) j P
  simpa [stepB, act, op] using h

end Iter

section Main

variable {G : PTm 2} {e T m : ℕ} {H D I R : PTm 1}
variable (hA : Assoc G) (hC : Comm G) (hI : IdL G e)
  (hDesc : ∀ {n : ℕ} {Δ : List (Fm PTm n)} (Q : PTm n), Prf PRAAx Δ (lt (num T) (ap1 H Q)) →
    Prf PRAAx Δ (Q ≐ op G (smul G e (num m) (ap1 D Q)) (ap1 R (ap1 I Q))))
  (hDec : ∀ {n : ℕ} {Δ : List (Fm PTm n)} (Q : PTm n), Prf PRAAx Δ (lt (num T) (ap1 H Q)) →
    Prf PRAAx Δ (lt (ap1 H (ap1 D Q)) (ap1 H Q)))

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The invariant `P = m^k Q + A` of a state. -/
abbrev invF {n : ℕ} (G : PTm 2) (e T m : ℕ) (H D I R : PTm 1) (j P : PTm n) : Fm PTm n :=
  P ≐ op G (smul G e (pw (num m) (ks (st G e T m H D I R j P))) (Qs (st G e T m H D I R j P)))
    (As (st G e T m H D I R j P))

theorem subst_invF {n n' : ℕ} (σ : Fin n → PTm n') (j P : PTm n) :
    (invF G e T m H D I R j P).subst σ = invF G e T m H D I R (Syn.subst σ j) (Syn.subst σ P) := by
  simp [invF]

/-- The height alternative `h(Q_j) ≤ T ∨ h(Q_j) + j ≤ h(P)`. -/
abbrev hgtF {n : ℕ} (G : PTm 2) (e T m : ℕ) (H D I R : PTm 1) (j P : PTm n) : Fm PTm n :=
  le (ap1 H (Qs (st G e T m H D I R j P))) (num T) ⋎ le (ap1 H (Qs (st G e T m H D I R j P)) + j) (ap1 H P)

theorem subst_hgtF {n n' : ℕ} (σ : Fin n → PTm n') (j P : PTm n) :
    (hgtF G e T m H D I R j P).subst σ = hgtF G e T m H D I R (Syn.subst σ j) (Syn.subst σ P) := by
  simp [hgtF]

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- An active step: `Q' = D(Q)`, `k' = k + 1`, `A' = A + m^k r_{i(Q)}`. -/
theorem step_active {j P : PTm n} (h : Γ ⊢[PRAAx] lt (num T) (ap1 H (Qs (st G e T m H D I R j P)))) :
    Γ ⊢[PRAAx] (Qs (st G e T m H D I R (succ j) P) ≐ ap1 D (Qs (st G e T m H D I R j P))) ⋏
      ((ks (st G e T m H D I R (succ j) P) ≐ succ (ks (st G e T m H D I R j P))) ⋏
        (As (st G e T m H D I R (succ j) P) ≐ op G (As (st G e T m H D I R j P))
          (smul G e (pw (num m) (ks (st G e T m H D I R j P))) (ap1 R (ap1 I (Qs (st G e T m H D I R j P))))))) := by
  have s := st_succ (Γ := Γ) (G := G) (e := e) (T := T) (m := m) (H := H) (D := D) (I := I) (R := R) j P
  have a1 : Γ ⊢[PRAAx] act T H (Qs (st G e T m H D I R j P)) ≐ one := sg_lt h
  have u0 : Γ ⊢[PRAAx] monus one (act T H (Qs (st G e T m H D I R j P))) ≐ zero :=
    (congrMonus (.eqRefl _) a1).eqTrans (monus_self _)
  have ea := natEq a1; have eu := natEq u0
  refine .andI ?_ (.andI ?_ ?_)
  · ipra_lc natEq ((congrFst s).eqTrans (fst_pair _ _)) + 𝔞 (ap1 D (Qs (st G e T m H D I R j P))) * ea +
      𝔞 (Qs (st G e T m H D I R j P)) * eu
  · ipra_lc natEq ((congrFst (congrSnd s)).eqTrans ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))) + ea
  · ipra_lc natEq ((congrSnd (congrSnd s)).eqTrans ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))) +
      𝔞 (op G (As (st G e T m H D I R j P)) (smul G e (pw (num m) (ks (st G e T m H D I R j P))) (ap1 R (ap1 I (Qs (st G e T m H D I R j P)))))) * ea +
      𝔞 (As (st G e T m H D I R j P)) * eu

/-- A stopped step leaves the state unchanged. -/
theorem step_stopped {j P : PTm n} (h : Γ ⊢[PRAAx] le (ap1 H (Qs (st G e T m H D I R j P))) (num T)) :
    Γ ⊢[PRAAx] (Qs (st G e T m H D I R (succ j) P) ≐ Qs (st G e T m H D I R j P)) ⋏
      ((ks (st G e T m H D I R (succ j) P) ≐ ks (st G e T m H D I R j P)) ⋏
        (As (st G e T m H D I R (succ j) P) ≐ As (st G e T m H D I R j P))) := by
  have s := st_succ (Γ := Γ) (G := G) (e := e) (T := T) (m := m) (H := H) (D := D) (I := I) (R := R) j P
  have a0 : Γ ⊢[PRAAx] act T H (Qs (st G e T m H D I R j P)) ≐ zero := sg_le h
  have u1 : Γ ⊢[PRAAx] monus one (act T H (Qs (st G e T m H D I R j P))) ≐ one :=
    (congrMonus (.eqRefl _) a0).eqTrans (monus_zero _)
  have ea := natEq a0; have eu := natEq u1
  refine .andI ?_ (.andI ?_ ?_)
  · ipra_lc natEq ((congrFst s).eqTrans (fst_pair _ _)) + 𝔞 (ap1 D (Qs (st G e T m H D I R j P))) * ea +
      𝔞 (Qs (st G e T m H D I R j P)) * eu
  · ipra_lc natEq ((congrFst (congrSnd s)).eqTrans ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))) + ea
  · ipra_lc natEq ((congrSnd (congrSnd s)).eqTrans ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))) +
      𝔞 (op G (As (st G e T m H D I R j P)) (smul G e (pw (num m) (ks (st G e T m H D I R j P))) (ap1 R (ap1 I (Qs (st G e T m H D I R j P)))))) * ea +
      𝔞 (As (st G e T m H D I R j P)) * eu

include hA hC hI hDesc in
/-- The invariant is preserved by a step. -/
theorem inv_step {j P : PTm n} (ih : Γ ⊢[PRAAx] invF G e T m H D I R j P) :
    Γ ⊢[PRAAx] invF G e T m H D I R (succ j) P := by
  refine .orE (lt_or_le (num T) (ap1 H (Qs (st G e T m H D I R j P)))) ?_ ?_
  · have hl : (lt (num T) (ap1 H (Qs (st G e T m H D I R j P))) :: Γ) ⊢[PRAAx]
        lt (num T) (ap1 H (Qs (st G e T m H D I R j P))) := Prf.hyp0
    have sa := step_active hl
    have dq := hDesc _ hl
    -- `m^k Q = m^{k+1} D(Q) + m^k r`
    have t1 : (lt (num T) (ap1 H (Qs (st G e T m H D I R j P))) :: Γ) ⊢[PRAAx]
        smul G e (pw (num m) (ks (st G e T m H D I R j P))) (Qs (st G e T m H D I R j P)) ≐
          op G (smul G e (pw (num m) (succ (ks (st G e T m H D I R j P)))) (ap1 D (Qs (st G e T m H D I R j P))))
            (smul G e (pw (num m) (ks (st G e T m H D I R j P))) (ap1 R (ap1 I (Qs (st G e T m H D I R j P))))) := by
      refine (congrSmul (.eqRefl _) dq).eqTrans ((smul_op hA hC hI _ _ _).eqTrans (congrOp G ?_ (.eqRefl _)))
      refine (smul_mul hA hC hI _ _ _).eqSymm.eqTrans (congrSmul ?_ (.eqRefl _))
      exact (mul_comm _ _).eqTrans (pw_succ _ _).eqSymm
    have i2 := ih.wk.eqTrans ((congrOp G t1 (.eqRefl _)).eqTrans ((hA _ _ _).eqTrans
      (congrOp G (.eqRefl _) (hC _ _))))
    exact i2.eqTrans (congrOp G (congrSmul (congrPw (.eqRefl _) (Prf.andE₁ (Prf.andE₂ sa)).eqSymm)
      (Prf.andE₁ sa).eqSymm) (Prf.andE₂ (Prf.andE₂ sa)).eqSymm)
  · have ss := step_stopped (Prf.hyp0 : (le (ap1 H (Qs (st G e T m H D I R j P))) (num T) :: Γ) ⊢[PRAAx] _)
    exact ih.wk.eqTrans (congrOp G (congrSmul (congrPw (.eqRefl _) (Prf.andE₁ (Prf.andE₂ ss)).eqSymm)
      (Prf.andE₁ ss).eqSymm) (Prf.andE₂ (Prf.andE₂ ss)).eqSymm)

include hDec in
/-- The height alternative is preserved by a step. -/
theorem hgt_step {j P : PTm n} (ih : Γ ⊢[PRAAx] hgtF G e T m H D I R j P) :
    Γ ⊢[PRAAx] hgtF G e T m H D I R (succ j) P := by
  refine .orE (lt_or_le (num T) (ap1 H (Qs (st G e T m H D I R j P)))) ?_ ?_
  · have hl : (lt (num T) (ap1 H (Qs (st G e T m H D I R j P))) :: Γ) ⊢[PRAAx]
        lt (num T) (ap1 H (Qs (st G e T m H D I R j P))) := Prf.hyp0
    have sa := step_active hl
    have dd := hDec _ hl
    have eq1 := congrAp1 H (Prf.andE₁ sa)
    refine .orE ih.wk ?_ ?_
    · exact not_succ_le_self (num T) _ (le_trans Prf.hyp1 Prf.hyp0)
    · refine .orI₂ ?_
      have b := (Prf.hyp0 : (le (ap1 H (Qs (st G e T m H D I R j P)) + j) (ap1 H P) ::
        lt (num T) (ap1 H (Qs (st G e T m H D I R j P))) :: Γ) ⊢[PRAAx] _)
      have dd' := dd.wk (ψ := le (ap1 H (Qs (st G e T m H D I R j P)) + j) (ap1 H P))
      have e1 := natEq (eq1.wk (ψ := le (ap1 H (Qs (st G e T m H D I R j P)) + j) (ap1 H P)))
      ipra_le sl b + sl dd' using linear_combination -e1
  · have ss := step_stopped (Prf.hyp0 : (le (ap1 H (Qs (st G e T m H D I R j P))) (num T) :: Γ) ⊢[PRAAx] _)
    exact .orI₁ (le_congr (congrAp1 H (Prf.andE₁ ss)).eqSymm (.eqRefl _) Prf.hyp0)

include hA hC hI hDesc hDec in
/-- `thm:generation`: after `h(P)` stages, `P = m^k Q + A` with `h(Q) ≤ T`, where `A` is the accumulated sum of
the generator multiples `m^{k_j} r_{i(Q_j)}` of the active stages. -/
theorem generation (P : PTm n) :
    Γ ⊢[PRAAx] invF G e T m H D I R (ap1 H P) P ⋏
      le (ap1 H (Qs (st G e T m H D I R (ap1 H P) P))) (num T) := by
  have hinv : Γ ⊢[PRAAx] Fm.all (invF G e T m H D I R (var 0) (Syn.shift P)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · rw [subst_invF]; simp only [Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      have s0 := st_zero (Γ := Γ) (G := G) (e := e) (T := T) (m := m) (H := H) (D := D) (I := I) (R := R) P
      have q0 := (congrFst s0).eqTrans (fst_pair _ _)
      have k0 := (congrFst (congrSnd s0)).eqTrans ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))
      have a0 := (congrSnd (congrSnd s0)).eqTrans ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))
      have one1 : Γ ⊢[PRAAx] smul G e (pw (num m) zero) P ≐ P :=
        (congrSmul (pw_zero _) (.eqRefl _)).eqTrans ((LeanProofs.IPRA.Foundations.AbelianCodes.smul_succ _ _).eqTrans
          ((congrOp G (LeanProofs.IPRA.Foundations.AbelianCodes.smul_zero _) (.eqRefl _)).eqTrans (hI _)))
      refine .eqSymm ?_
      refine (congrOp G (congrSmul (congrPw (.eqRefl _) k0) q0) a0).eqTrans ?_
      exact (congrOp G one1 (.eqRefl _)).eqTrans ((hC _ _).eqTrans (hI _))
    · rw [subst_invF]
      simp only [Syn.subst_var, Syn.repl_zero, subst_repl_shift, ConciseIPRA.PTm.subst_succ]
      exact inv_step hA hC hI hDesc Prf.hyp0
  have hhgt : Γ ⊢[PRAAx] Fm.all (hgtF G e T m H D I R (var 0) (Syn.shift P)) := by
    refine PRA.qfInd _ ⟨le_QF _ _, le_QF _ _⟩ ?_ ?_
    · rw [subst_hgtF]; simp only [Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      have s0 := st_zero (Γ := Γ) (G := G) (e := e) (T := T) (m := m) (H := H) (D := D) (I := I) (R := R) P
      have q0 := (congrFst s0).eqTrans (fst_pair _ _)
      exact .orI₂ (le_congr (congrAdd (congrAp1 H q0).eqSymm (.eqRefl _)) (.eqRefl _)
        (le_congr (add_zero _).eqSymm (.eqRefl _) (le_refl _)))
    · rw [subst_hgtF]
      simp only [Syn.subst_var, Syn.repl_zero, subst_repl_shift, ConciseIPRA.PTm.subst_succ]
      exact hgt_step hDec Prf.hyp0
  have i2 := Prf.allE (ap1 H P) hinv
  rw [subst_invF] at i2; simp only [Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at i2
  have h2 := Prf.allE (ap1 H P) hhgt
  rw [subst_hgtF] at h2; simp only [Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at h2
  refine .andI i2 (.orE h2 Prf.hyp0 ?_)
  have b := (Prf.hyp0 : (le (ap1 H (Qs (st G e T m H D I R (ap1 H P) P)) + ap1 H P) (ap1 H P) :: Γ) ⊢[PRAAx] _)
  exact le_trans (by ipra_le sl b) (zero_le _)

end Main

end LeanProofs.IPRA.Foundations.GenerationDescent
