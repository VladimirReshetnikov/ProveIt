import IPRADerivations.AnalyticNumberTheory.StageAdvance
import IPRADerivations.AnalyticNumberTheory.PNTThresholds
import IPRADerivations.Foundations.BoundedSyntaxInduction

/-!
# The finite induction over stages (`pnt_ipra_constructive_2026-11-14`, §"The induction predicate is a bounded
finite check")

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `contraction.tex`: "Induction on the assertion
'for every `x ≥ P_j`' would not be an instance of quantifier-free induction. Instead, fix a final integer ceiling
`X` … The stage predicate is the Boolean conjunction, over the finite set of integers `P_j ≤ n ≤ X` …". Here the
stage predicate is the bounded formula `ContractionSplit.Stage X (2^{s_j}) D A_j K L` (all `m ≤ X` with
`m ≥ 2^{s_j}`), and the induction on `j` is `Foundations.BoundedSyntaxInduction.induction`, i.e. the
quantifier-free induction on its compiled bit.

With `q = p + 1`, `D = 2^{20} q³` (`PNTThresholds.Dq`):

* levels `A_j = 4D − 3j` (`Aj`), down to `A_J ≥ A_min = 2^{20} q²` at `J = ⌊(4D − A_min)/3⌋` (`Jst`); at every
  level `A ≥ A_min` the block condition `576 D P ≤ A²` holds (`ap_bound`, `A³ ≥ 2^{60}q⁶ ≥ 78336 D²`);
* exponents `s_0 = D + 1600`, `s_{j+1} = 2(s_j + P_j(c_j + 1)) + 2` (`sT`, `StageAdvance.sN`), with
  `1600 D ≤ 2^{s_j}` (`z_bound`, `s_ge`);
* the base stage `A_0 = 4D` from `con:global` (`HarmonicChebyshev.psi_le`: `ψ(m) ≤ 4Fm`), `stage_base`;
* `stages`: the stage bound with `A_J` from `2^{s_J}` to `X`, for every ceiling `X` and mesh/denominator sizes.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.StageInduction

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicChebyshev (wt psi_le)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicMertens (le_scale)
open LeanProofs.IPRA.AnalyticNumberTheory.BlockChain (one_le_pw')
open LeanProofs.IPRA.AnalyticNumberTheory.ContractionSplit (Stage)
open LeanProofs.IPRA.AnalyticNumberTheory.StepCondition (mul_le2)
open LeanProofs.IPRA.AnalyticNumberTheory.StepAt (Pq stage_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.StageAdvance (sN stage_advance p4_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTThresholds (Dq Q3)
open LeanProofs.IPRA.AnalyticNumberTheory.ZetaFiniteContract (le_pow_self)
open LeanProofs.IPRA.AnalyticNumberTheory.FourthRootSum (Q4)
open LeanProofs.IPRA.AnalyticNumberTheory.AbsDiff (absd absd_le)
open LeanProofs.IPRA.AnalyticNumberTheory.LcmUpto (Psi)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le cancel_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerCleared (pw_le_exp)
open LeanProofs.IPRA.Foundations.BoundedSyntax (BFm formula)
open LeanProofs.IPRA.Analysis.Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Levels -/

/-- `A_j = 4D − 3j`. -/
def Aj (j D : PTm n) : PTm n := monus (num 4 * D) (num 3 * j)

@[simp] theorem subst_Aj {k : ℕ} (σ : Fin n → PTm k) (j D : PTm n) :
    Syn.subst σ (Aj j D) = Aj (Syn.subst σ j) (Syn.subst σ D) := by simp [Aj]

/-- `A_min = 2^{20} q²`. -/
abbrev Amin (p : PTm n) : PTm n := num 1048576 * (succ p * succ p)

/-- `J = ⌊(4D − A_min)/3⌋`. -/
abbrev Jst (p : PTm n) : PTm n := quo (monus (num 4 * Dq p) (Amin p)) (num 3)

/-- At every level `A ≥ A_min`: `576 D P ≤ A²`. -/
theorem ap_bound {p A : PTm n} (hA : Γ ⊢[PRAAx] le (Amin p) A) (hA4 : Γ ⊢[PRAAx] le A (two * (two * Dq p))) :
    Γ ⊢[PRAAx] le (num 576 * Dq p * Pq (Dq p) A) (A * A) := by
  have hA1 : Γ ⊢[PRAAx] le one A := le_trans (by ipra_le 1048576 * 𝔞 p * 𝔞 p + 2097152 * 𝔞 p + 1048575) hA
  have dm := div_mod_at (Γ := Γ) (x := num 24 * Dq p) (y := A) (c := pred A) (pos_of_one_le hA1)
  have e := natEq (Prf.andE₁ dm)
  refine cancel_pos hA1 ?_
  ipra_le (𝔞 A * 𝔞 A + 𝔞 A * (1048576 * (𝔞 p + 1) ^ 2) + (1048576 * (𝔞 p + 1) ^ 2) ^ 2) * sl hA +
    2415919104 * (𝔞 p + 1) ^ 3 * 𝔞 (rem (num 24 * Dq p) A) + 6039797760 * (𝔞 p + 1) ^ 3 * sl hA4 +
    1066790161733386240 * (𝔞 p + 1) ^ 6 with 2415919104 * (𝔞 p + 1) ^ 3 * e

/-- For `j < J`: `A_j ≥ A_min + 3`, `A_j ≤ 4D` and `A_j − 3 ≤ A_{j+1}`. -/
theorem level_facts {p j : PTm n} (hj : Γ ⊢[PRAAx] le (succ j) (Jst p)) :
    Γ ⊢[PRAAx] le (num 3 + Amin p) (Aj j (Dq p)) ⋏
      (le (Aj j (Dq p)) (two * (two * Dq p)) ⋏ le (monus (Aj j (Dq p)) (num 3)) (Aj (succ j) (Dq p))) := by
  have hm : Γ ⊢[PRAAx] le (Amin p) (num 4 * Dq p) := by
    ipra_le 4194304 * 𝔞 p ^ 3 + 11534336 * 𝔞 p ^ 2 + 10485760 * 𝔞 p + 3145728
  have f0 := natEq (eq_add_of_le hm)
  have dm := div_mod_at (Γ := Γ) (x := monus (num 4 * Dq p) (Amin p)) (y := num 3) (c := two) (.eqRefl _)
  have e0 := natEq (Prf.andE₁ dm)
  have h3 : Γ ⊢[PRAAx] le (num 3 * succ j) (num 4 * Dq p) := by
    have q := le_scale (num 3) hj
    ipra_le sl q + 𝔞 (rem (monus (num 4 * Dq p) (Amin p)) (num 3)) + 1048576 * (𝔞 p + 1) ^ 2 with f0 + e0
  have h3' : Γ ⊢[PRAAx] le (num 3 * j) (num 4 * Dq p) := le_trans (by ipra_le 3) h3
  have f1 := natEq (eq_add_of_le h3')
  have f2 := natEq (eq_add_of_le h3)
  have hlo : Γ ⊢[PRAAx] le (num 3 + Amin p) (Aj j (Dq p)) := by
    have q := le_scale (num 3) hj
    unfold Aj
    ipra_le sl q + 𝔞 (rem (monus (num 4 * Dq p) (Amin p)) (num 3)) with f0 + e0 - f1
  have f3 := natEq (eq_add_of_le (le_trans (le_add_right (num 3) (Amin p)) hlo))
  refine .andI hlo (.andI ?_ ?_)
  · unfold Aj; ipra_le 3 * 𝔞 j with f1
  · unfold Aj at f3 ⊢; ipra_le 0 with f1 - f2 + f3

/-! ## Exponents -/

/-- The step body over `0 = j`, `1 = s_j`, `2 = D`. -/
def stepS : PTm 3 := sN (var 2) (Aj (var 0) (var 2)) (var 1)

/-- `s_j`: `s_0 = D + 1600`, `s_{j+1} = sN(D, A_j, s_j)`. -/
def sT (j D : PTm n) : PTm n := ap2 (rec2 (var 0 + num 1600) stepS) j D

@[simp] theorem subst_sT {k : ℕ} (σ : Fin n → PTm k) (j D : PTm n) :
    Syn.subst σ (sT j D) = sT (Syn.subst σ j) (Syn.subst σ D) := by simp [sT]

theorem s_zero (D : PTm n) : Γ ⊢[PRAAx] sT zero D ≐ D + num 1600 := by
  have h := rec2_zero (Γ := Γ) (var 0 + num 1600) stepS D
  simp at h
  exact h

theorem s_succ (j D : PTm n) : Γ ⊢[PRAAx] sT (succ j) D ≐ sN D (Aj j D) (sT j D) := by
  have h := rec2_succ (Γ := Γ) (var 0 + num 1600) stepS j D
  simp [stepS] at h
  exact h

theorem le_two_mul (a : PTm n) : Γ ⊢[PRAAx] le a (two * a) := by ipra_le 𝔞 a

/-- `s_j ≥ D + 1600`. -/
theorem s_ge (j D : PTm n) : Γ ⊢[PRAAx] le (D + num 1600) (sT j D) := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (Syn.shift D + num 1600) (sT (var 0) (Syn.shift D))) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [subst_le, PTm.subst_add, PTm.subst_num, subst_sT, Syn.subst_var, Syn.inst_zero,
        Syn.subst_inst_shift]
      exact le_congr (.eqRefl _) (s_zero D).eqSymm (le_refl _)
    · simp only [subst_le, PTm.subst_add, PTm.subst_num, subst_sT, Syn.subst_var, Syn.repl_zero,
        subst_repl_shift]
      let Δ : List (Fm PTm (n + 1)) := le (Syn.shift D + num 1600) (sT (var 0) (Syn.shift D)) :: Γ.map Fm.shift
      have ih : Δ ⊢[PRAAx] le (Syn.shift D + num 1600) (sT (var 0) (Syn.shift D)) := Prf.hyp0
      have e := natEq (s_succ (Γ := Δ) (var 0) (Syn.shift D))
      have g : Δ ⊢[PRAAx] le (sT (var 0) (Syn.shift D)) (sN (Syn.shift D) (Aj (var 0) (Syn.shift D))
          (sT (var 0) (Syn.shift D))) := le_trans (le_add_right _ _) (le_trans (le_two_mul _) (le_add_right _ _))
      exact le_trans ih (le_congr (.eqRefl _) (s_succ _ _).eqSymm g)
  have h := Prf.allE j hall
  simp only [subst_le, PTm.subst_add, PTm.subst_num, subst_sT, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift] at h
  exact h

/-- `1600 D ≤ 2^{D + 1600}`. -/
theorem z_bound (D : PTm n) : Γ ⊢[PRAAx] le (num 1600 * D) (pw two (D + num 1600)) := by
  have a := mul_le2 (le_pow_self (Γ := Γ) (num 1600)) (le_pow_self (Γ := Γ) D)
  have e := natEq (pw_add (Γ := Γ) two D (num 1600))
  ipra_le sl a with e

/-! ## The stage formula as a bounded formula -/

/-- The source syntax of `Stage x Y D A K L`. -/
def stageSyntax (x Y D A K L : PTm n) : BFm n :=
  .all (succ x) (.imp (.le (Syn.shift Y) (var 0))
    (.le (Syn.shift D * absd (Psi wt (var 0) (Syn.shift (pairT K (fact L)))) (Syn.shift (fact L) * var 0))
      (Syn.shift A * (Syn.shift (fact L) * var 0))))

theorem stage_formula (x Y D A K L : PTm n) : formula (stageSyntax x Y D A K L) = Stage x Y D A K L := rfl

/-- The induction law: `j ≤ J → Stage X (2^{s_j}) D A_j K L`. -/
def lawS (X D K L J j : PTm n) : Fm PTm n := le j J ⟶ Stage X (pw two (sT j D)) D (Aj j D) K L

def lawSyn (X D K L J j : PTm n) : BFm n := .imp (.le j J) (stageSyntax X (pw two (sT j D)) D (Aj j D) K L)

theorem law_formula (X D K L J j : PTm n) : formula (lawSyn X D K L J j) = lawS X D K L J j := rfl

@[simp] theorem subst_lawS {k : ℕ} (σ : Fin n → PTm k) (X D K L J j : PTm n) :
    (lawS X D K L J j).subst σ = lawS (Syn.subst σ X) (Syn.subst σ D) (Syn.subst σ K) (Syn.subst σ L)
      (Syn.subst σ J) (Syn.subst σ j) := by
  simp [lawS, Stage, LeanProofs.IPRA.Foundations.BoundedFormulas.subst_up_shift', Fm.subst_all, Fm.subst_imp]

/-! ## Monotonicity in the level and the base stage -/

theorem stage_monoA {x Y D A A' K L : PTm n} (hA : Γ ⊢[PRAAx] le A A') (h : Γ ⊢[PRAAx] Stage x Y D A K L) :
    Γ ⊢[PRAAx] Stage x Y D A' K L := by
  have hA' : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift A) (Syn.shift A') := by simpa [Fm.shift, Syn.shift] using hA.shift
  refine .allI (.impI (.impI ?_))
  exact le_trans (Prf.impE (Prf.impE h.allOpen.wk.wk Prf.hyp1) Prf.hyp0) (mul_le_mul_right _ hA'.wk.wk)

/-- The base stage: `D|ψ(m) − Fm| ≤ 4D Fm` for all `m ≤ X` (`ψ(m) ≤ 4Fm`, con:global). -/
theorem stage_base {X Y D K L : PTm n} (hK : Γ ⊢[PRAAx] le one K)
    (hP : Γ ⊢[PRAAx] le (K * pw two (two * (two * X))) L) : Γ ⊢[PRAAx] Stage X Y D (num 4 * D) K L := by
  have hK' : (Γ.map Fm.shift) ⊢[PRAAx] le one (Syn.shift K) := by simpa [Fm.shift, Syn.shift] using hK.shift
  have hP' : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift K * pw two (two * (two * Syn.shift X))) (Syn.shift L) := by
    simpa [Fm.shift, Syn.shift] using hP.shift
  refine .allI (.impI (.impI ?_))
  let Θ : List (Fm PTm (n + 1)) := le (Syn.shift Y) (var 0) :: lt (var 0) (Syn.shift (succ X)) :: Γ.map Fm.shift
  have hmX : Θ ⊢[PRAAx] le (var 0) (Syn.shift X) := by
    have a : Θ ⊢[PRAAx] lt (var 0) (succ (Syn.shift X)) := by
      have a0 : Θ ⊢[PRAAx] lt (var 0) (Syn.shift (succ X)) := Prf.hyp1
      rw [show Syn.shift (succ X) = succ (Syn.shift X) by simp [Syn.shift]] at a0
      exact a0
    exact (succ_monus_succ _ _).eqSymm.eqTrans a
  have hPm : Θ ⊢[PRAAx] le (Syn.shift K * pw two (two * (two * var 0))) (Syn.shift L) :=
    le_trans (le_scale _ (p4_mono hmX)) hP'.wk.wk
  have ps := psi_le (Γ := Θ) (N := var 0) hK'.wk.wk hPm
  have ab : Θ ⊢[PRAAx] le (absd (Psi wt (var 0) (pairT (Syn.shift K) (fact (Syn.shift L))))
      (fact (Syn.shift L) * var 0)) (num 4 * (fact (Syn.shift L) * var 0)) := by
    refine absd_le ?_ ?_
    · ipra_le sl ps + 𝔞 (fact (Syn.shift L)) * 𝔞 (var 0)
    · ipra_le 3 * 𝔞 (fact (Syn.shift L)) * 𝔞 (var 0) + 𝔞 (Psi wt (var 0) (pairT (Syn.shift K) (fact (Syn.shift L))))
  rw [show Syn.shift (pairT K (fact L)) = pairT (Syn.shift K) (fact (Syn.shift L)) by simp [Syn.shift],
    show Syn.shift (fact L) = fact (Syn.shift L) by simp [Syn.shift],
    show Syn.shift (num 4 * D) = num 4 * Syn.shift D by simp [Syn.shift]]
  have q := le_scale (Syn.shift D) ab
  ipra_le sl q

/-! ## The induction -/

theorem stages {p X K L : PTm n}
    (hK : Γ ⊢[PRAAx] le one K) (hX1 : Γ ⊢[PRAAx] le one X) (hX4 : Γ ⊢[PRAAx] le (Q4 X) K)
    (hL4 : Γ ⊢[PRAAx] le (K * Q4 X) L) (hP : Γ ⊢[PRAAx] le (K * pw two (two * (two * X))) L)
    (hKx : Γ ⊢[PRAAx] le (K * X) L) (hxL : Γ ⊢[PRAAx] le X L) (hxK : Γ ⊢[PRAAx] le X K)
    (hNN : Γ ⊢[PRAAx] le (K * pw X X) L) (hF : Γ ⊢[PRAAx] le (two * X) (fact L))
    (h2K : Γ ⊢[PRAAx] le (two * (K * X)) (fact L)) (hF4 : Γ ⊢[PRAAx] le (num 4 * K + two) (fact L)) :
    Γ ⊢[PRAAx] Stage X (pw two (sT (Jst p) (Dq p))) (Dq p) (Aj (Jst p) (Dq p)) K L := by
  have t7 : (Γ.map Fm.shift) ⊢[PRAAx] le one (Syn.shift K) := by simpa [Fm.shift, Syn.shift] using hK.shift
  have t8 : (Γ.map Fm.shift) ⊢[PRAAx] le one (Syn.shift X) := by simpa [Fm.shift, Syn.shift] using hX1.shift
  have t9 : (Γ.map Fm.shift) ⊢[PRAAx] le (Q4 (Syn.shift X)) (Syn.shift K) := by
    simpa [Fm.shift, Syn.shift] using hX4.shift
  have t10 : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift K * Q4 (Syn.shift X)) (Syn.shift L) := by
    simpa [Fm.shift, Syn.shift] using hL4.shift
  have t11 : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift K * pw two (two * (two * Syn.shift X))) (Syn.shift L) := by
    simpa [Fm.shift, Syn.shift] using hP.shift
  have t12 : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift K * Syn.shift X) (Syn.shift L) := by
    simpa [Fm.shift, Syn.shift] using hKx.shift
  have t13 : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift X) (Syn.shift L) := by simpa [Fm.shift, Syn.shift] using hxL.shift
  have t14 : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift X) (Syn.shift K) := by simpa [Fm.shift, Syn.shift] using hxK.shift
  have t15 : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift K * pw (Syn.shift X) (Syn.shift X)) (Syn.shift L) := by
    simpa [Fm.shift, Syn.shift] using hNN.shift
  have t16 : (Γ.map Fm.shift) ⊢[PRAAx] le (two * Syn.shift X) (fact (Syn.shift L)) := by
    simpa [Fm.shift, Syn.shift] using hF.shift
  have t17 : (Γ.map Fm.shift) ⊢[PRAAx] le (two * (Syn.shift K * Syn.shift X)) (fact (Syn.shift L)) := by
    simpa [Fm.shift, Syn.shift] using h2K.shift
  have t18 : (Γ.map Fm.shift) ⊢[PRAAx] le (num 4 * Syn.shift K + two) (fact (Syn.shift L)) := by
    simpa [Fm.shift, Syn.shift] using hF4.shift
  have e30 : Γ ⊢[PRAAx] Aj zero (Dq p) ≐ num 4 * Dq p :=
    (congrMonus (.eqRefl _) (by apply deriveNat; ipra_simps; ring)).eqTrans (monus_zero _)
  have hD : Syn.shift (Dq p) = Dq (Syn.shift p) := by simp [Syn.shift, PTm.subst_num]
  have hJ : Syn.shift (Jst p) = Jst (Syn.shift p) := by simp [Syn.shift, PTm.subst_num]
  have all : Γ ⊢[PRAAx] .all (lawS (Syn.shift X) (Syn.shift (Dq p)) (Syn.shift K) (Syn.shift L)
      (Syn.shift (Jst p)) (var 0)) := by
    simpa only [law_formula] using (Foundations.BoundedSyntaxInduction.induction
      (lawSyn (Syn.shift X) (Syn.shift (Dq p)) (Syn.shift K) (Syn.shift L) (Syn.shift (Jst p)) (var 0)) (Γ := Γ)
      (by
        simp only [law_formula, subst_lawS, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
        exact .impI (stage_monoA (le_congr (.eqRefl _) e30.eqSymm (le_refl _)).wk (stage_base hK.wk hP.wk)))
      (by
        simp only [law_formula, subst_lawS, Syn.subst_var, Syn.repl_zero, subst_repl_shift]
        refine .impI ?_
        let Δ : List (Fm PTm (n + 1)) := le (succ (var 0)) (Syn.shift (Jst p)) ::
          lawS (Syn.shift X) (Syn.shift (Dq p)) (Syn.shift K) (Syn.shift L) (Syn.shift (Jst p)) (var 0) ::
          Γ.map Fm.shift
        have hj : Δ ⊢[PRAAx] le (succ (var 0)) (Jst (Syn.shift p)) := by
          have h0 : Δ ⊢[PRAAx] le (succ (var 0)) (Syn.shift (Jst p)) := Prf.hyp0
          rw [hJ] at h0; exact h0
        have prev : Δ ⊢[PRAAx] Stage (Syn.shift X) (pw two (sT (var 0) (Dq (Syn.shift p)))) (Dq (Syn.shift p))
            (Aj (var 0) (Dq (Syn.shift p))) (Syn.shift K) (Syn.shift L) := by
          have h1 : Δ ⊢[PRAAx] lawS (Syn.shift X) (Syn.shift (Dq p)) (Syn.shift K) (Syn.shift L)
              (Syn.shift (Jst p)) (var 0) := Prf.hyp1
          rw [hD, hJ] at h1
          exact Prf.impE h1 (le_trans (le_succ_self _) hj)
        have lf := level_facts hj
        have p2 : Δ ⊢[PRAAx] (two : PTm (n + 1)) ≐ succ (pred two) := pos_of_one_le (le_succ_self one)
        have hsg := s_ge (Γ := Δ) (var 0) (Dq (Syn.shift p))
        have hs0 : Δ ⊢[PRAAx] le one (sT (var 0) (Dq (Syn.shift p))) := le_trans (by ipra_le
          1048576 * (𝔞 (Syn.shift p) + 1) ^ 3 + 1599) hsg
        have hD1 : Δ ⊢[PRAAx] le one (Dq (Syn.shift p)) := by
          ipra_le 1048576 * 𝔞 (Syn.shift p) ^ 3 + 3145728 * 𝔞 (Syn.shift p) ^ 2 + 3145728 * 𝔞 (Syn.shift p) + 1048575
        have adv := stage_advance hs0 (le_trans (le_add_right _ _) (Prf.andE₁ lf)) (Prf.andE₁ (Prf.andE₂ lf)) hD1
          (ap_bound (le_trans (le_add_left _ _) (Prf.andE₁ lf)) (Prf.andE₁ (Prf.andE₂ lf)))
          (le_trans (z_bound _) (pw_le_exp p2 hsg)) t7.wk.wk t8.wk.wk t9.wk.wk t10.wk.wk t11.wk.wk t12.wk.wk
          t13.wk.wk t14.wk.wk t15.wk.wk t16.wk.wk t17.wk.wk t18.wk.wk prev
        have r : Δ ⊢[PRAAx] Stage (Syn.shift X) (pw two (sT (succ (var 0)) (Syn.shift (Dq p)))) (Syn.shift (Dq p))
            (Aj (succ (var 0)) (Syn.shift (Dq p))) (Syn.shift K) (Syn.shift L) := by
          rw [hD]
          exact stage_monoA (Prf.andE₂ (Prf.andE₂ lf)) (stage_mono
            (le_congr (.eqRefl _) (congrAp2 powF (s_succ _ _).eqSymm (.eqRefl two)) (le_refl _)) adv)
        exact r))
  have rule := all.allE (Jst p)
  simp only [subst_lawS, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at rule
  exact .impE rule (le_refl _)

end LeanProofs.IPRA.AnalyticNumberTheory.StageInduction
