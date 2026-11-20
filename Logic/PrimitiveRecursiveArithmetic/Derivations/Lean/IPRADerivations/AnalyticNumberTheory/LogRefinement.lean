import IPRADerivations.AnalyticNumberTheory.Harmonic
import IPRADerivations.AnalyticNumberTheory.Primes
import IPRADerivations.AnalyticNumberTheory.SumReindex
import IPRADerivations.AnalyticNumberTheory.SumPhi
import IPRADerivations.Foundations.AuxiliaryEnvelope
import IPRADerivations.Probability.Independence
import IPRADerivations.Core.SumSplit
import IPRADerivations.Core.OrderCertificates

/-!
# Refinement of the rational logarithm intervals (`pnt_ipra_constructive_2026-11-14`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `pnt_ipra.tex`, §"Rational
logarithm intervals": "For positive integers `a ≥ b` and `M ≥ 1`, define `λ_M(a/b) = H_{Ma} − H_{Mb}`.
… `λ_M(a/b)` is the right rectangle sum for `1/t` on `[b, a]` with mesh `1/M`; its upper rectangle sum
is `λ_M(a/b) + 1/(Mb) − 1/(Ma)`. Refinement nests these intervals. … Thus their consistency and width
are bounded rational inequalities, proved without presupposing a real logarithm."

This module derives the nesting under refinement of the mesh `1/M` to `1/(MK)`:

  `λ_M(a/b) ≤ λ_{MK}(a/b) ≤ λ_M(a/b) + 1/(Mb) − 1/(Ma)`.

With `c₀ = Mb = c₁ + 1`, `T = Ma − Mb` and the common denominator `F = L!` for `L ≥ MKa`, every harmonic
number `H_m` with `m ≤ L` is `S(m, F)/F` exactly (`S(m, F) = Σ_{i<m} ⌊F/(i+1)⌋`, `Harmonic.S`), and the
two inequalities are (`log_refine`, `refine_closed`)

  `S(c₀ + T) + S(Kc₀) ≤ S(K(c₀ + T)) + S(c₀)`        (`λ_M ≤ λ_{MK}`),
  `S(K(c₀ + T)) + S(c₁) ≤ S(Kc₀) + S(c₁ + T)`        (`λ_{MK} ≤ H_{Ma−1} − H_{Mb−1}`).

The proof splits the fine sum into the blocks `Σ_{i<K} 1/(Kc + i + 1)` (`blk`) and bounds each block by
its endpoint values, `1/(c+1) ≤ blk ≤ 1/c` (`block_lower`, `block_upper`), then sums the blocks by two
quantifier-free inductions over the number `t` of blocks (`lo_step`, `up_step`). The lower block
bound uses that `K(c+1)` divides `F` (`Primes.dvd_fact`); the upper one holds for every `F`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.LogRefinement

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB inst2_h quo_anti)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (dvd_fact)
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.SumReindex (le_quo_of_mul_le)
open LeanProofs.IPRA.AnalyticNumberTheory.SumPhi (sum_ones)
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (quo_eq)
open LeanProofs.IPRA.Foundations.AuxiliaryEnvelope (sum_le_const)
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Small tools -/

theorem pos_of_eq {t e : PTm n} (h : Γ ⊢[PRAAx] t ≐ succ e) : Γ ⊢[PRAAx] t ≐ succ (pred t) :=
  h.eqTrans (congrSucc ((pred_succ e).eqSymm.eqTrans (congrPred h.eqSymm)))

/-- `⌊x / B⌋ = u` when `x = B u`, `B ≥ 1`. -/
theorem quo_mul {x B u : PTm n} (hB : Γ ⊢[PRAAx] B ≐ succ (pred B)) (h : Γ ⊢[PRAAx] x ≐ B * u) :
    Γ ⊢[PRAAx] quo x B ≐ u := by
  have e := natEq hB
  exact quo_eq hB (h.eqTrans (add_zero _).eqSymm) (by ipra_le 𝔞 (pred B) with e)

/-- The constant body `fst y` in `(i, y)`. -/
abbrev cstB : PTm 2 := fstT (var 1)

/-- `N L ≤ Σ_{i<N} f(i, x)` when every term is at least `L`. -/
theorem const_le_sum (f : PTm 2) {N L x : PTm n}
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ le (Syn.shift L) (inst2 f (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] le (N * L) (ap2 (sumF f) N x) := by
  have e : Γ ⊢[PRAAx] ap2 (sumF cstB) N (pairT L x) ≐ L * ap2 (sumF (one : PTm 2)) N x := by
    refine sum_scale cstB one N L x (pairT L x) (.allI (.impI ?_))
    rw [show inst2 cstB (var 0 : PTm (n + 1)) (Syn.shift (pairT L x)) = fstT (pairT (Syn.shift L) (Syn.shift x)) by
        simp [inst2, Syn.shift],
      show inst2 (one : PTm 2) (var 0 : PTm (n + 1)) (Syn.shift x) = one by simp [inst2]]
    exact (fst_pair _ _).eqTrans ((mul_comm _ _).eqTrans (one_mul _)).eqSymm
  have e' : Γ ⊢[PRAAx] ap2 (sumF cstB) N (pairT L x) ≐ N * L :=
    e.eqTrans ((congrMul (.eqRefl _) (sum_ones N x)).eqTrans (mul_comm _ _))
  refine le_congr e' (.eqRefl _) (sum_le_params cstB f (pairT L x) x N (.allI (.impI ?_)))
  rw [show inst2 cstB (var 0 : PTm (n + 1)) (Syn.shift (pairT L x)) = fstT (pairT (Syn.shift L) (Syn.shift x)) by
      simp [inst2, Syn.shift]]
  exact le_congr (fst_pair _ _).eqSymm (.eqRefl _) (Prf.impE h.allOpen.wk Prf.hyp0)

theorem shift_eq {a b N : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) :
    (lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) ⊢[PRAAx] Syn.shift a ≐ Syn.shift b := by
  have s := h.shift
  simp only [Fm.shift, Fm.subst_eq] at s
  exact s.wk

/-! ## Blocks -/

/-- The block `Σ_{i<K} ⌊F/(Kc + i + 1)⌋`, i.e. `F Σ_{i<K} 1/(Kc + i + 1)`. -/
abbrev blk (K c F : PTm n) : PTm n := ap2 (sumF (offB hB)) K (pairT (K * c) F)

theorem inst2_blk (i K c F : PTm n) :
    Γ ⊢[PRAAx] inst2 (offB hB) i (pairT (K * c) F) ≐ quo F (succ (K * c + i)) := by
  rw [inst2_offB, inst2_h]
  exact congrAp2 quoF (snd_pair _ _) (congrSucc (congrAdd (fst_pair _ _) (.eqRefl _)))

/-- `S(K(c + 1)) = S(Kc) + blk(c)`. -/
theorem S_block (K c F : PTm n) : Γ ⊢[PRAAx] S (K * succ c) F ≐ S (K * c) F + blk K c F := by
  have eK : Γ ⊢[PRAAx] K * succ c ≐ K * c + K := by apply deriveNat; ipra_simps; ring
  exact (congrAp2 (sumF hB) eK (.eqRefl _)).eqTrans (sum_split hB (K * c) K F)

/-- A term of the block is at most `⌊F/(Kc + 1)⌋`. -/
theorem blk_point_upper (i K c F : PTm n) :
    Γ ⊢[PRAAx] le (inst2 (offB hB) i (pairT (K * c) F)) (quo F (succ (K * c))) :=
  le_congr (inst2_blk i K c F).eqSymm (.eqRefl _)
    (quo_anti (congrSucc (pred_succ _).eqSymm) (by ipra_le 𝔞 i))

/-- `blk(c) ≤ ⌊F/c⌋` for `c ≥ 1`. -/
theorem block_upper {K c F : PTm n} (hc : Γ ⊢[PRAAx] c ≐ succ (pred c)) :
    Γ ⊢[PRAAx] le (blk K c F) (quo F c) := by
  have h1 : Γ ⊢[PRAAx] le (blk K c F) (K * quo F (succ (K * c))) := by
    refine sum_le_const (offB hB) (.allI (.impI ?_))
    rw [show Syn.shift (pairT (K * c) F) = pairT (Syn.shift K * Syn.shift c) (Syn.shift F) by simp [Syn.shift],
      show Syn.shift (quo F (succ (K * c))) = quo (Syn.shift F) (succ (Syn.shift K * Syn.shift c)) by
        simp [Syn.shift]]
    exact blk_point_upper _ _ _ _
  have dm := div_mod_at (Γ := Γ) (x := F) (y := succ (K * c)) (c := K * c) (.eqRefl _)
  have e := natEq (Prf.andE₁ dm)
  have h2 : Γ ⊢[PRAAx] le (K * quo F (succ (K * c))) (quo F c) := by
    refine le_quo_of_mul_le hc ?_
    ipra_le 𝔞 (quo F (succ (K * c))) + 𝔞 (rem F (succ (K * c))) with e
  exact le_trans h1 h2

/-- A term of the block is at least `⌊F/(K(c + 1))⌋`. -/
theorem blk_point_lower {i K c F u : PTm n} (hi : Γ ⊢[PRAAx] lt i K) (hu : Γ ⊢[PRAAx] quo F (K * succ c) ≐ u) :
    Γ ⊢[PRAAx] le u (inst2 (offB hB) i (pairT (K * c) F)) := by
  refine le_congr hu (inst2_blk i K c F).eqSymm (quo_anti (congrSucc (pred_succ _).eqSymm) ?_)
  ipra_le sl hi

/-- `⌊F/(c + 1)⌋ ≤ blk(c)` when `F = K(c + 1) u`, `K ≥ 1`. -/
theorem block_lower {K c F u : PTm n} (hK : Γ ⊢[PRAAx] K ≐ succ (pred K)) (hF : Γ ⊢[PRAAx] F ≐ K * succ c * u) :
    Γ ⊢[PRAAx] le (quo F (succ c)) (blk K c F) := by
  have hd : Γ ⊢[PRAAx] K * succ c ≐ succ (pred (K * succ c)) := by
    refine pos_of_eq (e := pred K * succ c + c) ((congrMul hK (.eqRefl _)).eqTrans ?_)
    apply deriveNat; ipra_simps; ring
  have hu : Γ ⊢[PRAAx] quo F (K * succ c) ≐ u := quo_mul hd hF
  have hq : Γ ⊢[PRAAx] quo F (succ c) ≐ K * u := by
    refine quo_mul (congrSucc (pred_succ _).eqSymm) (hF.eqTrans ?_)
    apply deriveNat; ipra_simps; ring
  refine le_congr hq.eqSymm (.eqRefl _) (const_le_sum (offB hB) (.allI (.impI ?_)))
  rw [show Syn.shift (pairT (K * c) F) = pairT (Syn.shift K * Syn.shift c) (Syn.shift F) by simp [Syn.shift]]
  refine blk_point_lower Prf.hyp0 ?_
  have s := shift_eq (N := K) hu
  rw [show Syn.shift (quo F (K * succ c)) = quo (Syn.shift F) (Syn.shift K * succ (Syn.shift c)) by
    simp [Syn.shift]] at s
  exact s

/-! ## The upper inequality -/

/-- `S(K(c₁ + 1 + t)) + S(c₁) ≤ S(K(c₁ + 1)) + S(c₁ + t)`. -/
def upInv (t c₁ K F : PTm n) : Fm PTm n :=
  le (S (K * (succ c₁ + t)) F + S c₁ F) (S (K * succ c₁) F + S (c₁ + t) F)

@[simp] theorem subst_upInv {k : ℕ} (σ : Fin n → PTm k) (t c₁ K F : PTm n) :
    (upInv t c₁ K F).subst σ = upInv (Syn.subst σ t) (Syn.subst σ c₁) (Syn.subst σ K) (Syn.subst σ F) := by
  simp [upInv, subst_ap2]

theorem up_base (c₁ K F : PTm n) : Γ ⊢[PRAAx] upInv zero c₁ K F :=
  le_congr (congrAdd (congrAp2 (sumF hB) (congrMul (.eqRefl _) (add_zero _)).eqSymm (.eqRefl _)) (.eqRefl _))
    (congrAdd (.eqRefl _) (congrAp2 (sumF hB) (add_zero _).eqSymm (.eqRefl _))) (le_refl _)

theorem up_step {t c₁ K F : PTm n} (ih : Γ ⊢[PRAAx] upInv t c₁ K F) : Γ ⊢[PRAAx] upInv (succ t) c₁ K F := by
  have eK : Γ ⊢[PRAAx] K * (succ c₁ + succ t) ≐ K * succ (succ c₁ + t) := by apply deriveNat; ipra_simps; ring
  have eA := natEq ((congrAp2 (sumF hB) eK (.eqRefl _)).eqTrans (S_block K (succ c₁ + t) F))
  have eB := natEq ((congrAp2 (sumF hB) (add_succ c₁ t) (.eqRefl F)).eqTrans
    ((sum_succ' hB (c₁ + t) F).eqTrans (by rw [inst2_h]; exact .eqRefl _)) : Γ ⊢[PRAAx] _ ≐ _)
  have hc : Γ ⊢[PRAAx] succ c₁ + t ≐ succ (pred (succ c₁ + t)) :=
    pos_of_eq (e := c₁ + t) (by apply deriveNat; ipra_simps; ring)
  have hb : Γ ⊢[PRAAx] le (blk K (succ c₁ + t) F) (quo F (succ (c₁ + t))) :=
    le_congr (.eqRefl _) (congrAp2 quoF (.eqRefl _) (by apply deriveNat; ipra_simps; ring)) (block_upper hc)
  have ih' : Γ ⊢[PRAAx] le (S (K * (succ c₁ + t)) F + S c₁ F) (S (K * succ c₁) F + S (c₁ + t) F) := ih
  show Γ ⊢[PRAAx] le (S (K * (succ c₁ + succ t)) F + S c₁ F) (S (K * succ c₁) F + S (c₁ + succ t) F)
  ipra_le sl ih' + sl hb with eB - eA

theorem up_all (t c₁ K F : PTm n) : Γ ⊢[PRAAx] upInv t c₁ K F := by
  have hall : Γ ⊢[PRAAx] Fm.all (upInv (var 0) (Syn.shift c₁) (Syn.shift K) (Syn.shift F)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · rw [subst_upInv]
      simp only [Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      exact up_base _ _ _
    · rw [subst_upInv]
      simp only [Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      exact up_step Prf.hyp0
  have a := Prf.allE t hall
  rw [subst_upInv] at a
  simpa [Syn.subst_inst_shift] using a

/-! ## The lower inequality -/

/-- `t ≤ T → S(c₀ + t) + S(Kc₀) ≤ S(K(c₀ + t)) + S(c₀)`, with `F = L!`. -/
def loInv (t T c₀ K L : PTm n) : Fm PTm n :=
  le t T ⟶ le (S (c₀ + t) (fact L) + S (K * c₀) (fact L)) (S (K * (c₀ + t)) (fact L) + S c₀ (fact L))

@[simp] theorem subst_loInv {k : ℕ} (σ : Fin n → PTm k) (t T c₀ K L : PTm n) :
    (loInv t T c₀ K L).subst σ =
      loInv (Syn.subst σ t) (Syn.subst σ T) (Syn.subst σ c₀) (Syn.subst σ K) (Syn.subst σ L) := by
  simp [loInv, subst_ap2]

theorem loInv_QF (t T c₀ K L : PTm n) : (loInv t T c₀ K L).QF := by
  unfold loInv; exact ⟨le_QF _ _, le_QF _ _⟩

theorem lo_base (T c₀ K L : PTm n) : Γ ⊢[PRAAx] loInv zero T c₀ K L :=
  .impI (le_congr (congrAdd (congrAp2 (sumF hB) (add_zero _).eqSymm (.eqRefl _)) (.eqRefl _))
    ((add_comm _ _).eqTrans
      (congrAdd (congrAp2 (sumF hB) (congrMul (.eqRefl _) (add_zero _)).eqSymm (.eqRefl _)) (.eqRefl _))) (le_refl _))

theorem lo_step {t T c₀ K L : PTm n} (hK : Γ ⊢[PRAAx] K ≐ succ (pred K)) (hL : Γ ⊢[PRAAx] le (K * (c₀ + T)) L)
    (ih : Γ ⊢[PRAAx] loInv t T c₀ K L) : Γ ⊢[PRAAx] loInv (succ t) T c₀ K L := by
  refine .impI ?_
  let Δ : List (Fm PTm n) := le (succ t) T :: Γ
  have ht : Δ ⊢[PRAAx] le (succ t) T := Prf.hyp0
  have ih' : Δ ⊢[PRAAx] le (S (c₀ + t) (fact L) + S (K * c₀) (fact L)) (S (K * (c₀ + t)) (fact L) + S c₀ (fact L)) :=
    Prf.impE ih.wk (le_trans (le_succ_self t) ht)
  -- `K(c₀ + t + 1)` divides `L!`
  have hd : Δ ⊢[PRAAx] K * succ (c₀ + t) ≐ succ (pred (K * succ (c₀ + t))) := by
    refine pos_of_eq (e := pred K * succ (c₀ + t) + (c₀ + t)) ((congrMul hK.wk (.eqRefl _)).eqTrans ?_)
    apply deriveNat; ipra_simps; ring
  have hdL : Δ ⊢[PRAAx] le (succ (pred (K * succ (c₀ + t)))) L := by
    have hL' : Δ ⊢[PRAAx] le (K * (c₀ + T)) L := hL.wk
    have e := natEq hd
    ipra_le sl hL' + 𝔞 K * sl ht with e
  have dv := dvd_fact hdL
  have dm := div_mod_at (Γ := Δ) (x := fact L) hd
  have hF : Δ ⊢[PRAAx] fact L ≐ K * succ (c₀ + t) * quo (fact L) (K * succ (c₀ + t)) := by
    refine (Prf.andE₁ dm).eqTrans ((congrAdd (.eqRefl _) ?_).eqTrans (add_zero _))
    exact (congrAp2 remF (.eqRefl _) hd).eqTrans dv
  have hb := block_lower hK.wk hF
  have eA := natEq ((congrAp2 (sumF hB) (add_succ c₀ t) (.eqRefl (fact L))).eqTrans
    ((sum_succ' hB (c₀ + t) (fact L)).eqTrans (by rw [inst2_h]; exact .eqRefl _)) : Δ ⊢[PRAAx] _ ≐ _)
  have eK : Δ ⊢[PRAAx] K * (c₀ + succ t) ≐ K * succ (c₀ + t) := by apply deriveNat; ipra_simps; ring
  have eB := natEq ((congrAp2 (sumF hB) eK (.eqRefl _)).eqTrans (S_block K (c₀ + t) (fact L)))
  show Δ ⊢[PRAAx] le (S (c₀ + succ t) (fact L) + S (K * c₀) (fact L)) (S (K * (c₀ + succ t)) (fact L) + S c₀ (fact L))
  ipra_le sl ih' + sl hb with eB - eA

theorem lo_all {T c₀ K L : PTm n} (hK : Γ ⊢[PRAAx] K ≐ succ (pred K)) (hL : Γ ⊢[PRAAx] le (K * (c₀ + T)) L)
    (t : PTm n) : Γ ⊢[PRAAx] loInv t T c₀ K L := by
  have hall : Γ ⊢[PRAAx] Fm.all (loInv (var 0) (Syn.shift T) (Syn.shift c₀) (Syn.shift K) (Syn.shift L)) := by
    refine PRA.qfInd _ (loInv_QF _ _ _ _ _) ?_ ?_
    · rw [subst_loInv]
      simp only [Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      exact lo_base _ _ _ _
    · rw [subst_loInv]
      simp only [Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      have sK := hK.shift
      simp only [Fm.shift, Fm.subst_eq, ConciseIPRA.PTm.subst_succ, PTm.subst_pred] at sK
      have sL := hL.shift
      simp only [Fm.shift, subst_le, PTm.subst_mul, PTm.subst_add] at sL
      exact lo_step sK.wk sL.wk Prf.hyp0
  have a := Prf.allE t hall
  rw [subst_loInv] at a
  simpa [Syn.subst_inst_shift] using a

/-! ## The nesting -/

/-- `λ_M(a/b) ≤ λ_{MK}(a/b) ≤ λ_M(a/b) + 1/(Mb) − 1/(Ma)` with `Mb = c₁ + 1`, `Ma = c₁ + 1 + T`,
`K ≥ 1`, cleared by the common denominator `L!`, `L ≥ MKa`. -/
theorem log_refine {c₁ T K L : PTm n} (hK : Γ ⊢[PRAAx] K ≐ succ (pred K))
    (hL : Γ ⊢[PRAAx] le (K * (succ c₁ + T)) L) :
    Γ ⊢[PRAAx] le (S (succ c₁ + T) (fact L) + S (K * succ c₁) (fact L))
        (S (K * (succ c₁ + T)) (fact L) + S (succ c₁) (fact L)) ⋏
      le (S (K * (succ c₁ + T)) (fact L) + S c₁ (fact L)) (S (K * succ c₁) (fact L) + S (c₁ + T) (fact L)) :=
  .andI (Prf.impE (lo_all hK hL T) (le_refl T)) (up_all T c₁ K (fact L))

/-- Variables `0 = c₁`, `1 = T`, `2 = K − 1`, `3 = L`. -/
def refineFormula : Fm PTm 4 :=
  le (succ (var 2) * (succ (var 0) + var 1)) (var 3) ⟶
    (le (S (succ (var 0) + var 1) (fact (var 3)) + S (succ (var 2) * succ (var 0)) (fact (var 3)))
        (S (succ (var 2) * (succ (var 0) + var 1)) (fact (var 3)) + S (succ (var 0)) (fact (var 3))) ⋏
      le (S (succ (var 2) * (succ (var 0) + var 1)) (fact (var 3)) + S (var 0) (fact (var 3)))
        (S (succ (var 2) * succ (var 0)) (fact (var 3)) + S (var 0 + var 1) (fact (var 3))))

/-- The nesting of the rational logarithm intervals, as a closed sentence of iPRA. -/
theorem refine_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 refineFormula :=
  closeUniv 4 (.impI (log_refine (congrSucc (pred_succ _).eqSymm) Prf.hyp0))

end LeanProofs.IPRA.AnalyticNumberTheory.LogRefinement
