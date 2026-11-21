import IPRADerivations.AnalyticNumberTheory.StepAt

/-!
# One stage of the contraction (`pnt_ipra_constructive_2026-11-14`, §"Integer thresholds and the modulus")

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `contraction.tex`: "The hypotheses of
Lemma con:one-step are therefore met at every rational `x ≥ P_{j+1}` … We retain only a decrement `δ` at each
step." Here the stage bound `D|ψ(m) − Fm| ≤ AFm` on `[2^s, X]` (a single iPRA formula `Stage`, all `m ≤ X`
at once, with one mesh `K` and one denominator `F = L!` fixed by `X`) improves to the stage bound with `A − 3`
on `[2^{s'}, X]`, where (`sN`)

  `s' = 2(s + P(c + 1)) + 2`,  `c = Lin + Cst` (`StepCondition`), `P = Pq D A` (`StepAt`).

Every `m ≥ 2^{s'}` has `ℓ(m) ≥ s' − 1`, hence `2s + 1 ≤ ℓ` and at least `c` blocks (`B_lower`), so
`StepAt.step_at` applies at `m`; the size conditions at `m` follow from those at `X` (`sizes_at`).

* `stage_restrict`: a stage bound up to `X` holds up to every `x ≤ X`;
* `clog_ge`: `2^s ≤ m` gives `s ≤ λ(m)`;
* `B_lower`: `2(σ₀ + P(c + 1)) ≤ ℓ` gives `c ≤ B`;
* `stage_advance`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.StageAdvance

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicChebyshev (wt)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicMertens (le_scale)
open LeanProofs.IPRA.AnalyticNumberTheory.BlockChain (one_le_pw')
open LeanProofs.IPRA.AnalyticNumberTheory.BlockTests (one_le_mul)
open LeanProofs.IPRA.AnalyticNumberTheory.ContractionSplit (Stage)
open LeanProofs.IPRA.AnalyticNumberTheory.StepCondition (DecLin DecCst mul_le2)
open LeanProofs.IPRA.AnalyticNumberTheory.StepParams (ell muP BP clog_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.StepAt (Pq step_at)
open LeanProofs.IPRA.AnalyticNumberTheory.ZetaFiniteContract (clog clog_spec)
open LeanProofs.IPRA.AnalyticNumberTheory.FourthRootSum (Q4)
open LeanProofs.IPRA.AnalyticNumberTheory.AbsDiff (absd)
open LeanProofs.IPRA.AnalyticNumberTheory.LcmUpto (Psi)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le cancel_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerCleared (pw_le_exp)
open LeanProofs.IPRA.Analysis.Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Restriction and logarithm facts -/

theorem stage_restrict {x X Y D A K L : PTm n} (hxX : Γ ⊢[PRAAx] le x X) (h : Γ ⊢[PRAAx] Stage X Y D A K L) :
    Γ ⊢[PRAAx] Stage x Y D A K L := by
  have hxX0 : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift x) (Syn.shift X) := by simpa [Fm.shift, Syn.shift] using hxX.shift
  have hxX' : (Γ.map Fm.shift) ⊢[PRAAx] le (succ (Syn.shift x)) (succ (Syn.shift X)) :=
    (succ_monus_succ _ _).eqTrans hxX0
  refine .allI (.impI (.impI ?_))
  have hv : (le (Syn.shift Y) (var 0) :: lt (var 0) (Syn.shift (succ x)) :: Γ.map Fm.shift) ⊢[PRAAx]
      lt (var 0) (Syn.shift (succ X)) := by
    have a : (le (Syn.shift Y) (var 0) :: lt (var 0) (Syn.shift (succ x)) :: Γ.map Fm.shift) ⊢[PRAAx]
        lt (var 0) (succ (Syn.shift x)) := by simpa [Syn.shift] using (Prf.hyp1 :
          (le (Syn.shift Y) (var 0) :: lt (var 0) (Syn.shift (succ x)) :: Γ.map Fm.shift) ⊢[PRAAx] _)
    simpa [Syn.shift] using lt_of_lt_of_le a hxX'.wk.wk
  exact Prf.impE (Prf.impE h.allOpen.wk.wk hv) Prf.hyp0

/-- `2^s ≤ m` gives `s ≤ λ(m)`. -/
theorem clog_ge {s m : PTm n} (h : Γ ⊢[PRAAx] le (pw two s) m) : Γ ⊢[PRAAx] le s (clog m) := by
  refine .orE (lt_or_le (clog m) s) ?_ Prf.hyp0
  have p2 : (lt (clog m) s :: Γ) ⊢[PRAAx] (two : PTm n) ≐ succ (pred two) := pos_of_one_le (le_succ_self one)
  have a := pw_le_exp p2 (Prf.hyp0 : (lt (clog m) s :: Γ) ⊢[PRAAx] le (succ (clog m)) s)
  have e := natEq (pw_succ (Γ := lt (clog m) s :: Γ) two (clog m))
  have b := Prf.andE₁ (clog_spec (Γ := lt (clog m) s :: Γ) m)
  have c := one_le_pw' (Γ := lt (clog m) s :: Γ) (le_succ_self one) (clog m)
  have d : (lt (clog m) s :: Γ) ⊢[PRAAx] lt (pw two (clog m)) (pw two (clog m)) := by
    ipra_le sl a + sl h.wk + sl b + sl c with e
  exact lt_irrefl _ _ d

/-- At least `c` blocks: `2(σ₀ + P(c + 1)) ≤ ℓ` gives `c ≤ ⌊(ℓ − μ − σ₀)/P⌋`. -/
theorem B_lower {x s0 P c : PTm n} (hP : Γ ⊢[PRAAx] le one P)
    (hl : Γ ⊢[PRAAx] le (two * (s0 + P * succ c)) (ell x)) : Γ ⊢[PRAAx] le c (BP x s0 P) := by
  have d1 := div_mod_at (Γ := Γ) (x := ell x) (y := two) (c := one) (.eqRefl _)
  have e1 := natEq (Prf.andE₁ d1)
  have r1 := Prf.andE₂ d1
  have hμl : Γ ⊢[PRAAx] le (muP x) (ell x) := by ipra_le 𝔞 (muP x) + 𝔞 (rem (ell x) two) with e1
  have f1 := natEq (eq_add_of_le hμl)
  have hP1 : Γ ⊢[PRAAx] le one (P * succ c) := le_trans hP (by ipra_le 𝔞 P * 𝔞 c)
  have hm2 : Γ ⊢[PRAAx] le (two * s0) (two * muP x) := by ipra_le sl hl + sl r1 + 2 * sl hP1 + 1 with e1
  have hms : Γ ⊢[PRAAx] le s0 (muP x) := mul_le_cancel (d' := one) hm2
  have hs : Γ ⊢[PRAAx] le s0 (monus (ell x) (muP x)) := by ipra_le sl hms + 𝔞 (rem (ell x) two) with f1 - e1
  have f2 := natEq (eq_add_of_le hs)
  have d2 := div_mod_at (Γ := Γ) (x := monus (monus (ell x) (muP x)) s0) (y := P) (c := pred P) (pos_of_one_le hP)
  have e2 := natEq (Prf.andE₁ d2)
  have r2 := Prf.andE₂ d2
  have hrr2 : Γ ⊢[PRAAx] le (two * (P * succ c)) (two * monus (monus (ell x) (muP x)) s0) := by
    ipra_le sl hl + 𝔞 (rem (ell x) two) with 2 * f2 + 2 * f1 - e1
  have hrr := mul_le_cancel (d' := one) hrr2
  have hPB : Γ ⊢[PRAAx] le (P * succ c) (P * succ (BP x s0 P)) := by ipra_le sl hrr + sl r2 + 1 with e2
  exact (succ_monus_succ _ _).eqSymm.eqTrans (cancel_pos hP hPB)

/-! ## Sizes at `m ≤ X` -/

theorem q4_mono {m X : PTm n} (h : Γ ⊢[PRAAx] le m X) : Γ ⊢[PRAAx] le (Q4 m) (Q4 X) := by
  have s : Γ ⊢[PRAAx] le (succ m) (succ X) := (succ_monus_succ _ _).eqTrans h
  exact mul_le2 (mul_le2 s s) (mul_le2 s s)

theorem pp_mono {m X : PTm n} (hX : Γ ⊢[PRAAx] le one X) (h : Γ ⊢[PRAAx] le m X) :
    Γ ⊢[PRAAx] le (pw m m) (pw X X) :=
  le_trans (pw_le_pw m h) (pw_le_exp (pos_of_one_le hX) h)

theorem p4_mono {m X : PTm n} (h : Γ ⊢[PRAAx] le m X) :
    Γ ⊢[PRAAx] le (pw two (two * (two * m))) (pw two (two * (two * X))) :=
  pw_le_exp (pos_of_one_le (le_succ_self one)) (le_scale two (le_scale two h))

/-! ## The stage advance -/

/-- The block-count constant `c = Lin + Cst`. -/
abbrev Cc (D A s : PTm n) : PTm n := DecLin D A (Pq D A) s + DecCst D A (Pq D A) s

/-- The next stage exponent `s' = 2(s + P(c + 1)) + 2`. -/
abbrev sN (D A s : PTm n) : PTm n := two * (s + Pq D A * succ (Cc D A s)) + two

theorem le_sum5 {a b c d e : PTm n} : Γ ⊢[PRAAx] le a ((((a + b) + c) + d) + e) := by
  ipra_le 𝔞 b + 𝔞 c + 𝔞 d + 𝔞 e

theorem one_le_Cc {D A s : PTm n} (hA1 : Γ ⊢[PRAAx] le one A) : Γ ⊢[PRAAx] le one (Cc D A s) := by
  have a := one_le_mul hA1 hA1
  have b : Γ ⊢[PRAAx] le (num 3 * (A * A)) (Cc D A s) := le_sum5
  exact le_trans (by ipra_le 3 * sl a + 2) b

/-- The step at one point `m ∈ [2^{s'}, X]`. -/
theorem stage_point {m X s D A K L : PTm n} (hs0 : Γ ⊢[PRAAx] le one s) (hA1 : Γ ⊢[PRAAx] le one A)
    (hA4 : Γ ⊢[PRAAx] le A (two * (two * D))) (hD1 : Γ ⊢[PRAAx] le one D)
    (hAP : Γ ⊢[PRAAx] le (num 576 * D * Pq D A) (A * A)) (hZ : Γ ⊢[PRAAx] le (num 1600 * D) (pw two s))
    (hK : Γ ⊢[PRAAx] le one K) (hX1 : Γ ⊢[PRAAx] le one X) (hX4 : Γ ⊢[PRAAx] le (Q4 X) K)
    (hL4 : Γ ⊢[PRAAx] le (K * Q4 X) L) (hP : Γ ⊢[PRAAx] le (K * pw two (two * (two * X))) L)
    (hKx : Γ ⊢[PRAAx] le (K * X) L) (hxL : Γ ⊢[PRAAx] le X L) (hxK : Γ ⊢[PRAAx] le X K)
    (hNN : Γ ⊢[PRAAx] le (K * pw X X) L) (hF : Γ ⊢[PRAAx] le (two * X) (fact L))
    (h2K : Γ ⊢[PRAAx] le (two * (K * X)) (fact L)) (hF4 : Γ ⊢[PRAAx] le (num 4 * K + two) (fact L))
    (hst : Γ ⊢[PRAAx] Stage X (pw two s) D A K L)
    (hm : Γ ⊢[PRAAx] le (pw two (sN D A s)) m) (hmX : Γ ⊢[PRAAx] le m X) :
    Γ ⊢[PRAAx] le (D * absd (Psi wt m (pairT K (fact L))) (fact L * m) + num 3 * (fact L * m)) (A * (fact L * m)) := by
  have hc1 := one_le_Cc (D := D) (s := s) hA1
  have hPq := LeanProofs.IPRA.AnalyticNumberTheory.StepAt.one_le_Pq (Γ := Γ) D A
  have p2 : Γ ⊢[PRAAx] (two : PTm n) ≐ succ (pred two) := pos_of_one_le (le_succ_self one)
  have hsN1 : Γ ⊢[PRAAx] le one (sN D A s) := le_trans (by ipra_le 1) (le_add_left two _)
  have h2m : Γ ⊢[PRAAx] le two m := le_trans (le_congr (pw_one two) (.eqRefl _) (pw_le_exp p2 hsN1)) hm
  have hcg := clog_ge hm
  have hcl : Γ ⊢[PRAAx] clog m ≐ succ (ell m) := pos_of_one_le (clog_pos h2m)
  have ec := natEq hcl
  have hP1 : Γ ⊢[PRAAx] le one (Pq D A * succ (Cc D A s)) := one_le_mul hPq (le_trans hc1 (le_succ_self _))
  have hl : Γ ⊢[PRAAx] le (two * s + one) (ell m) := by
    ipra_le sl hcg + 2 * sl hP1 + 2 with ec
  have hlB : Γ ⊢[PRAAx] le (two * (s + Pq D A * succ (Cc D A s))) (ell m) := by ipra_le sl hcg + 1 with ec
  have hcB := B_lower hPq hlB
  have hAAP : Γ ⊢[PRAAx] le one (A * A * Pq D A) := one_le_mul (one_le_mul hA1 hA1) hPq
  have hBB : Γ ⊢[PRAAx] le (BP m s (Pq D A)) (A * A * Pq D A * BP m s (Pq D A)) := by
    have q := le_scale (BP m s (Pq D A)) hAAP
    ipra_le sl q
  have hq4 := q4_mono hmX
  have hp4 := p4_mono hmX
  have hpp := pp_mono hX1 hmX
  exact step_at h2m hs0 hl hK (le_trans hq4 hX4) (le_trans (le_scale _ hq4) hL4)
    (le_trans (le_scale _ hp4) hP) (le_trans (le_scale _ hmX) hKx) (le_trans hmX hxL)
    (le_trans hmX hxK) (le_trans (le_scale _ hpp) hNN) (le_trans (le_scale _ hmX) hF)
    (le_trans (le_scale _ (le_scale _ hmX)) h2K) hF4 hA1 hA4 hD1 hAP hZ
    (le_trans hcB hBB) (le_trans hc1 hcB) (stage_restrict hmX hst)

/-- The stage bound on `[2^s, X]` with `A ≥ 3` improves to `A − 3` on `[2^{s'}, X]`. -/
theorem stage_advance {X s D A K L : PTm n} (hs0 : Γ ⊢[PRAAx] le one s) (hA3 : Γ ⊢[PRAAx] le (num 3) A)
    (hA4 : Γ ⊢[PRAAx] le A (two * (two * D))) (hD1 : Γ ⊢[PRAAx] le one D)
    (hAP : Γ ⊢[PRAAx] le (num 576 * D * Pq D A) (A * A)) (hZ : Γ ⊢[PRAAx] le (num 1600 * D) (pw two s))
    (hK : Γ ⊢[PRAAx] le one K) (hX1 : Γ ⊢[PRAAx] le one X) (hX4 : Γ ⊢[PRAAx] le (Q4 X) K)
    (hL4 : Γ ⊢[PRAAx] le (K * Q4 X) L) (hP : Γ ⊢[PRAAx] le (K * pw two (two * (two * X))) L)
    (hKx : Γ ⊢[PRAAx] le (K * X) L) (hxL : Γ ⊢[PRAAx] le X L) (hxK : Γ ⊢[PRAAx] le X K)
    (hNN : Γ ⊢[PRAAx] le (K * pw X X) L) (hF : Γ ⊢[PRAAx] le (two * X) (fact L))
    (h2K : Γ ⊢[PRAAx] le (two * (K * X)) (fact L)) (hF4 : Γ ⊢[PRAAx] le (num 4 * K + two) (fact L))
    (hst : Γ ⊢[PRAAx] Stage X (pw two s) D A K L) :
    Γ ⊢[PRAAx] Stage X (pw two (sN D A s)) D (monus A (num 3)) K L := by
  have hA1 : Γ ⊢[PRAAx] le one A := le_trans (by ipra_le 2) hA3
  have t1 : (Γ.map Fm.shift) ⊢[PRAAx] le one (Syn.shift s) := by simpa [Fm.shift, Syn.shift] using hs0.shift
  have t2 : (Γ.map Fm.shift) ⊢[PRAAx] le one (Syn.shift A) := by simpa [Fm.shift, Syn.shift] using hA1.shift
  have t3 : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift A) (two * (two * Syn.shift D)) := by
    simpa [Fm.shift, Syn.shift] using hA4.shift
  have t4 : (Γ.map Fm.shift) ⊢[PRAAx] le one (Syn.shift D) := by simpa [Fm.shift, Syn.shift] using hD1.shift
  have t5 : (Γ.map Fm.shift) ⊢[PRAAx] le (num 576 * Syn.shift D * Pq (Syn.shift D) (Syn.shift A))
      (Syn.shift A * Syn.shift A) := by simpa [Fm.shift, Syn.shift] using hAP.shift
  have t6 : (Γ.map Fm.shift) ⊢[PRAAx] le (num 1600 * Syn.shift D) (pw two (Syn.shift s)) := by
    simpa [Fm.shift, Syn.shift] using hZ.shift
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
  have t19 : (Γ.map Fm.shift) ⊢[PRAAx] Stage (Syn.shift X) (pw two (Syn.shift s)) (Syn.shift D) (Syn.shift A)
      (Syn.shift K) (Syn.shift L) := by
    have a := hst.shift
    simp only [Stage, Fm.shift, Fm.subst_all, Fm.subst_imp, subst_le, subst_lt, subst_ap2, PTm.subst_mul,
      PTm.subst_add, PTm.subst_monus, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.subst_var,
      Syn.up_zero, subst_up_shift_pal, subst_pairT] at a
    exact a
  have t20 : (Γ.map Fm.shift) ⊢[PRAAx] le (num 3) (Syn.shift A) := by
    simpa [Fm.shift, Syn.shift, PTm.subst_num] using hA3.shift
  refine .allI (.impI (.impI ?_))
  let Θ : List (Fm PTm (n + 1)) := le (Syn.shift (pw two (sN D A s))) (var 0) ::
    lt (var 0) (Syn.shift (succ X)) :: Γ.map Fm.shift
  have hmX : Θ ⊢[PRAAx] le (var 0) (Syn.shift X) := by
    have a : Θ ⊢[PRAAx] lt (var 0) (succ (Syn.shift X)) := by
      have a0 : Θ ⊢[PRAAx] lt (var 0) (Syn.shift (succ X)) := Prf.hyp1
      rw [show Syn.shift (succ X) = succ (Syn.shift X) by simp [Syn.shift]] at a0
      exact a0
    exact (succ_monus_succ _ _).eqSymm.eqTrans a
  have hm : Θ ⊢[PRAAx] le (pw two (sN (Syn.shift D) (Syn.shift A) (Syn.shift s))) (var 0) := by
    have h0 : Θ ⊢[PRAAx] le (Syn.shift (pw two (sN D A s))) (var 0) := Prf.hyp0
    rw [show Syn.shift (pw two (sN D A s)) = pw two (sN (Syn.shift D) (Syn.shift A) (Syn.shift s)) by
      simp [Syn.shift, PTm.subst_num]] at h0
    exact h0
  have r := stage_point t1.wk.wk t2.wk.wk t3.wk.wk t4.wk.wk t5.wk.wk t6.wk.wk t7.wk.wk t8.wk.wk t9.wk.wk t10.wk.wk
    t11.wk.wk t12.wk.wk t13.wk.wk t14.wk.wk t15.wk.wk t16.wk.wk t17.wk.wk t18.wk.wk t19.wk.wk hm hmX
  have e := natEq (eq_add_of_le (t20.wk.wk : Θ ⊢[PRAAx] _))
  rw [show Syn.shift (pairT K (fact L)) = pairT (Syn.shift K) (fact (Syn.shift L)) by simp [Syn.shift],
    show Syn.shift (fact L) = fact (Syn.shift L) by simp [Syn.shift],
    show Syn.shift (monus A (num 3)) = monus (Syn.shift A) (num 3) by simp [Syn.shift, PTm.subst_num]]
  ipra_le sl r with 𝔞 (fact (Syn.shift L)) * 𝔞 (var 0) * e

end LeanProofs.IPRA.AnalyticNumberTheory.StageAdvance
