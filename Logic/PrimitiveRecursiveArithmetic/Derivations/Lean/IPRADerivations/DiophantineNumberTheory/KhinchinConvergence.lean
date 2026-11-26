import IPRADerivations.Foundations.IntervalCover
import IPRADerivations.Foundations.AuxiliaryEnvelope
import IPRADerivations.Probability.Independence
import IPRADerivations.AnalyticNumberTheory.Totient
import IPRADerivations.DiophantineNumberTheory.HurwitzMargin
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.InductionTactic
import IPRADerivations.Core.Header

/-!
# The convergent half of the finite Khinchin theorem (`hurwitz_khinchin_ipra`, (K1))

Packet: `diophantine-number-theory/hurwitz_khinchin_ipra`, `khinchin.tex`, "Convergent version":
"Suppose a function `C` satisfies `C(s) ≥ 1` and `Σ_{q=C(s)}^R ψ(q) ≤ 2^{−s}` for every `s` and every
`R ≥ C(s)` (K-C). Then, for every `m` and `R ≥ C(m+1)`, `|⋃_{q=C(m+1)}^R A_q| ≤ 2^{−m}` (K1)", where
`A_q ⊆ [0, 1]` is the set of `x` with `|x − p/q| < ψ(q)/q` for some `0 ≤ p ≤ q`. The packet's remark
"If one insists on intervals open in all of `ℝ` and counts their unclipped lengths, the simpler bound
`4ψ(q)` applies; replace `C(m+1)` by `C(m+2)`" is the version proved here.

Coding. `ψ(q) = Ψ(q)/G` over a common denominator `G ≥ 1` (`Ψ`, `C` arbitrary PR terms). Lengths
are exact lengths of finite unions on the grid `{0, …, T}`, `T = G · R!` (`Foundations/IntervalCover`):
the interval around `p/q` is the cells `[(pG ∸ Ψ(q)) · R!/q, (pG + Ψ(q)) · R!/q)`, so its endpoints
are exactly `T (p/q ∓ ψ(q)/q)` (clipped at `0`), because `q ∣ R!` (`fact_dvd`). The intervals with
`q < C(m+2)` are made empty by the gate `[C(m+2) ≤ q]`.

* `union_measure`: the number of grid cells covered by `⋃_{q ≤ R} A_q` (gated);
* `khinchin_convergent` (closed sentence): for all `m, R, G` with `C(m+2) ≥ 1` and
  `2^{m+2} Σ_{q ≤ R} [C(m+2) ≤ q] Ψ(q) ≤ G` (the instance of (K-C), cleared),
  `2^m · union_measure ≤ T`, that is `|⋃_{q=C(m+2)}^R A_q| ≤ 2^{−m}`.

Proof: the union bound over `q` (`IntervalCover.union_le`), finite subadditivity inside each `A_q`
(`IntervalCover.subadditive`), each interval of length `≤ 2Ψ(q) R!/q`, `q + 1 ≤ 2q`, and (K-C).
The constructive null-cover reading ("every finite initial portion of the tail cover") is this
bound for every `R`.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.KhinchinConvergence

open_ipra
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open LeanProofs.IPRA.Foundations.IntervalCover
open LeanProofs.IPRA.Foundations.AuxiliaryEnvelope (sum_le_const)
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (quo_eq)

set_option autoImplicit false

variable {n : ℕ}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## `q ∣ R!` -/

/-- `R!`. -/
abbrev fact (R : PTm n) : PTm n := ap2 factF R zero

/-- Variables `0 = R`, `1 = q`. -/
private abbrev dvdF : Fm PTm 2 :=
  le one (var 1) ⟶ (le (var 1) (var 0) ⟶ (fact (var 0) ≐ var 1 * quo (fact (var 0)) (var 1)))

private theorem fact_dvd₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] dvdF := by
  ipra_ind (⟨le_QF _ _, le_QF _ _, trivial⟩) [dvdF, subst_le, subst_ap2]
  · refine .impI (.impI (.botE _ ?_))
    -- `1 ≤ q ≤ 0`
    exact not_succ_le_self zero _ (le_trans Prf.hyp1 Prf.hyp0)
  · refine .impI (.impI ?_)
    let Δ : List (Fm PTm 2) := le (var 1) (succ (var 0)) :: le one (var 1) :: [dvdF]
    have hq : Δ ⊢[PRAAx] var 1 ≐ succ (pred (var 1)) := by
      refine .orE (zero_or_succ (var 1)) ?_ Prf.hyp0
      exact .botE _ (not_succ_le_self zero _ (le_congr (.eqRefl _) Prf.hyp0 hyp2))
    have hf : Δ ⊢[PRAAx] fact (succ (var 0)) ≐ fact (var 0) * succ (var 0) := fact_succ _ _
    refine .orE (lt_or_le (var 0) (var 1)) ?_ ?_
    · -- `q = R + 1`
      have hq1 : (lt (var 0) (var 1) :: Δ) ⊢[PRAAx] var 1 ≐ succ (var 0) :=
        le_antisymm Prf.hyp1 Prf.hyp0
      have e : (lt (var 0) (var 1) :: Δ) ⊢[PRAAx] fact (succ (var 0)) ≐ var 1 * fact (var 0) :=
        hf.wk.eqTrans ((mul_comm _ _).eqTrans (congrMul hq1.eqSymm (.eqRefl _)))
      refine e.eqTrans (congrMul (.eqRefl _) ?_)
      refine (quo_eq hq.wk (r := zero) (e.eqTrans (add_zero _).eqSymm) ?_).eqSymm
      exact le_congr (.eqRefl _) hq.wk.eqSymm ((succ_monus_succ _ _).eqTrans (zero_monus _))
    · -- `q ≤ R`: the induction hypothesis
      have ih : (le (var 1) (var 0) :: Δ) ⊢[PRAAx] fact (var 0) ≐ var 1 * quo (fact (var 0)) (var 1) :=
        Prf.impE (Prf.impE (show (le (var 1) (var 0) :: Δ) ⊢[PRAAx] dvdF from .hyp (by simp [Δ])) hyp2) Prf.hyp0
      have e : (le (var 1) (var 0) :: Δ) ⊢[PRAAx] fact (succ (var 0)) ≐
          var 1 * (quo (fact (var 0)) (var 1) * succ (var 0)) :=
        hf.wk.eqTrans ((congrMul ih (.eqRefl _)).eqTrans (mul_assoc _ _ _))
      refine e.eqTrans (congrMul (.eqRefl _) ?_)
      refine (quo_eq hq.wk (r := zero) (e.eqTrans (add_zero _).eqSymm) ?_).eqSymm
      exact le_congr (.eqRefl _) hq.wk.eqSymm ((succ_monus_succ _ _).eqTrans (zero_monus _))

/-- `q ∣ R!` for `1 ≤ q ≤ R`. -/
theorem fact_dvd {Γ : List (Fm PTm n)} {q R : PTm n} (h1 : Γ ⊢[PRAAx] le one q) (h2 : Γ ⊢[PRAAx] le q R) :
    Γ ⊢[PRAAx] fact R ≐ q * quo (fact R) q := by
  have h := inst (Γ := Γ) fact_dvd₀ ![R, q]
  simp [dvdF] at h
  exact .impE (.impE h h1) h2

/-! ## The intervals -/

section Intervals

variable (Ψ C : PTm 1)

/-- `[C(s) ≤ q]`. -/
def gate (s q : PTm n) : PTm n := monus one (monus (Syn.subst ![s] C) q)

/-- The parameters `x = ⟨R, ⟨G, m⟩⟩`; `s = m + 2`. -/
abbrev pR (x : PTm n) : PTm n := fstT x
abbrev pG (x : PTm n) : PTm n := fstT (sndT x)
abbrev pS (x : PTm n) : PTm n := succ (succ (sndT (sndT x)))

/-- `R!/q`. -/
abbrev cof (q x : PTm n) : PTm n := quo (fact (pR x)) q

def loT (p q x : PTm n) : PTm n :=
  gate C (pS x) q * monus (p * pG x * cof q x) (Syn.subst ![q] Ψ * cof q x)
def hiT (p q x : PTm n) : PTm n :=
  gate C (pS x) q * ((p * pG x + Syn.subst ![q] Ψ) * cof q x)

theorem subst_one_vec {k : ℕ} (σ : Fin n → PTm k) (s : PTm n) (t : PTm 1) :
    Syn.subst σ (Syn.subst ![s] t) = Syn.subst ![Syn.subst σ s] t := by
  simp only [Syn.subst_subst]; congr 1; funext i; fin_cases i; rfl

@[simp] theorem subst_gate {k : ℕ} (σ : Fin n → PTm k) (s q : PTm n) :
    Syn.subst σ (gate C s q) = gate C (Syn.subst σ s) (Syn.subst σ q) := by
  simp [gate, subst_one_vec]

@[simp] theorem subst_loT {k : ℕ} (σ : Fin n → PTm k) (p q x : PTm n) :
    Syn.subst σ (loT Ψ C p q x) = loT Ψ C (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ x) := by
  simp [loT, subst_one_vec, subst_ap2]

@[simp] theorem subst_hiT {k : ℕ} (σ : Fin n → PTm k) (p q x : PTm n) :
    Syn.subst σ (hiT Ψ C p q x) = hiT Ψ C (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ x) := by
  simp [hiT, subst_one_vec, subst_ap2]

/-- The interval bodies in `(p, ⟨q, x⟩)`. -/
def loB : PTm 2 := loT Ψ C (var 0) (fstT (var 1)) (sndT (var 1))
def hiB : PTm 2 := hiT Ψ C (var 0) (fstT (var 1)) (sndT (var 1))

theorem inst2_loB (p y : PTm n) : inst2 (loB Ψ C) p y = loT Ψ C p (fstT y) (sndT y) := by
  simp [loB, inst2]
theorem inst2_hiB (p y : PTm n) : inst2 (hiB Ψ C) p y = hiT Ψ C p (fstT y) (sndT y) := by
  simp [hiB, inst2]

/-- `A_q` as a cell set: `aB(c, q, x) = [c ∈ ⋃_{p ≤ q} I_{p,q}]`. -/
def aB : PTm 3 := Syn.subst ![var 0, pairT (succ (var 1)) (pairT (var 1) (var 2))] (covB (loB Ψ C) (hiB Ψ C))

/-- The grid size `T = G · R!`. -/
abbrev gridT (x : PTm n) : PTm n := pG x * fact (pR x)

/-- The number of cells of `⋃_{q ≤ R} A_q`. -/
def unionMeasure (x : PTm n) : PTm n := ap2 (sumF (sg (oB (aB Ψ C)))) (gridT x) (pairT (succ (pR x)) x)

/-- The (K-C) body `[C(s) ≤ q] Ψ(q)` in `(q, x)`. -/
def gpB : PTm 2 := gate C (pS (var 1)) (var 0) * Syn.subst ![var 0] Ψ

/-- The bound `4 R! [C(s) ≤ q] Ψ(q)` in `(q, x)`. -/
def bndB : PTm 2 := num 4 * fact (pR (var 1)) * gpB Ψ C

end Intervals

/-! ## Arithmetic -/

section Arith

variable {Γ : List (Fm PTm n)}

theorem gate_cases (C : PTm 1) (s q : PTm n) :
    Γ ⊢[PRAAx] (gate C s q ≐ zero) ⋎ ((gate C s q ≐ one) ⋏ le (Syn.subst ![s] C) q) := by
  refine .orE (zero_or_succ (monus (Syn.subst ![s] C) q)) ?_ ?_
  · exact .orI₂ (.andI ((congrMonus (.eqRefl _) Prf.hyp0).eqTrans (monus_zero _)) Prf.hyp0)
  · exact .orI₁ ((congrMonus (.eqRefl _) Prf.hyp0).eqTrans ((succ_monus_succ _ _).eqTrans (zero_monus _)))

/-- `(A + B) ∸ (A ∸ B) ≤ 2B`. -/
theorem width_le (A B : PTm n) : Γ ⊢[PRAAx] le (monus (A + B) (monus A B)) (two * B) := by
  refine .orE (le_total B A) ?_ ?_
  · have e := natEq (eq_add_of_le (Γ := le B A :: Γ) Prf.hyp0)
    have h : (le B A :: Γ) ⊢[PRAAx] A + B ≐ monus A B + two * B := by
      ipra_lc e
    exact le_congr ((congrMonus h (.eqRefl _)).eqTrans (add_monus' _ _)).eqSymm (.eqRefl _) (le_refl _)
  · have h0 : (le A B :: Γ) ⊢[PRAAx] monus A B ≐ zero := Prf.hyp0
    have e := natEq (eq_add_of_le (Γ := le A B :: Γ) Prf.hyp0)
    refine le_congr ((congrMonus (.eqRefl _) h0).eqTrans (monus_zero _)).eqSymm (.eqRefl _) ?_
    refine le_of_eq_add (d := monus B A) ?_
    ipra_lc e

end Arith

/-! ## The estimate -/

section Estimate

variable (Ψ C : PTm 1) {Γ : List (Fm PTm n)}

/-- Each interval has length at most `[C(s) ≤ q] · 2Ψ(q) · R!/q`. -/
theorem len_le (p q x : PTm n) :
    Γ ⊢[PRAAx] le (monus (hiT Ψ C p q x) (loT Ψ C p q x))
      (gate C (pS x) q * (two * (Syn.subst ![q] Ψ * cof q x))) := by
  refine .orE (gate_cases (Γ := Γ) C (pS x) q) ?_ ?_
  · have h0 : ((gate C (pS x) q ≐ zero) :: Γ) ⊢[PRAAx] hiT Ψ C p q x ≐ zero :=
      (congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _)
    exact le_congr ((congrMonus h0 (.eqRefl _)).eqTrans (zero_monus _)).eqSymm (.eqRefl _) (zero_le _)
  · let Δ : List (Fm PTm n) := (gate C (pS x) q ≐ one ⋏ le (Syn.subst ![pS x] C) q) :: Γ
    have h1 : Δ ⊢[PRAAx] gate C (pS x) q ≐ one := Prf.andE₁ Prf.hyp0
    have eX : Δ ⊢[PRAAx] hiT Ψ C p q x ≐ p * pG x * cof q x + Syn.subst ![q] Ψ * cof q x :=
      (congrMul h1 (.eqRefl _)).eqTrans ((one_mul _).eqTrans (by ipra_ring))
    have eY : Δ ⊢[PRAAx] loT Ψ C p q x ≐ monus (p * pG x * cof q x) (Syn.subst ![q] Ψ * cof q x) :=
      (congrMul h1 (.eqRefl _)).eqTrans (one_mul _)
    have eG : Δ ⊢[PRAAx] gate C (pS x) q * (two * (Syn.subst ![q] Ψ * cof q x)) ≐
        two * (Syn.subst ![q] Ψ * cof q x) := (congrMul h1 (.eqRefl _)).eqTrans (one_mul _)
    exact le_congr (congrMonus eX eY).eqSymm eG.eqSymm (width_le _ _)

/-- The bound for one `q` as a template in `(q, x)`. -/
def Lt : PTm 2 := gate C (pS (var 1)) (var 0) * (two * (Syn.subst ![var 0] Ψ * cof (var 0) (var 1)))

theorem inst2_Lt (q x : PTm n) :
    inst2 (Lt Ψ C) q x = gate C (pS x) q * (two * (Syn.subst ![q] Ψ * cof q x)) := by
  simp [Lt, inst2, subst_one_vec, subst_ap2]

theorem inst3_aB (c j x : PTm n) :
    inst3 (aB Ψ C) c j x = inst2 (covB (loB Ψ C) (hiB Ψ C)) c (pairT (succ j) (pairT j x)) := by
  simp only [inst3, inst2, aB, Syn.subst_subst]
  congr 1; funext i; fin_cases i <;> simp

/-- The cells of `A_q` are at most `4 R! [C(s) ≤ q] Ψ(q)`. -/
theorem point_bound {q x : PTm n} (hC : Γ ⊢[PRAAx] le one (Syn.subst ![pS x] C))
    (hq : Γ ⊢[PRAAx] lt q (succ (pR x))) :
    Γ ⊢[PRAAx] le (inst2 (pB (aB Ψ C)) q (pairT (gridT x) x)) (inst2 (bndB Ψ C) q x) := by
  rw [inst2_pB]
  -- the cells of `A_q` are those of the union of its intervals
  have e1 : Γ ⊢[PRAAx] ap2 (sumF (colB (aB Ψ C))) (fstT (pairT (gridT x) x)) (pairT q (sndT (pairT (gridT x) x))) ≐
      ap2 (sumF (colB (aB Ψ C))) (gridT x) (pairT q x) :=
    congrAp2 _ (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))
  have s1 : Γ ⊢[PRAAx] le (ap2 (sumF (colB (aB Ψ C))) (gridT x) (pairT q x))
      (measure (loB Ψ C) (hiB Ψ C) (gridT x) (succ q) (pairT q x)) := by
    refine sum_le_params _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_colB, inst3_aB]
    refine le_congr (.eqRefl _) ?_ (le_refl _)
    refine congrInst2 _ (.eqRefl _) ?_
    have hz : (lt (var 0) (Syn.shift (gridT x)) :: Γ.map Fm.shift) ⊢[PRAAx]
        fstT (Syn.shift (pairT q x)) ≐ Syn.shift q := by rw [shift_pairT]; exact fst_pair _ _
    have hz' : (lt (var 0) (Syn.shift (gridT x)) :: Γ.map Fm.shift) ⊢[PRAAx]
        sndT (Syn.shift (pairT q x)) ≐ Syn.shift x := by rw [shift_pairT]; exact snd_pair _ _
    rw [shift_pairT, shift_pairT, shift_pairT]
    rw [shift_pairT] at hz hz'
    exact congrPairT (congrSucc hz) (congrPairT hz hz')
  -- finite subadditivity inside `A_q`
  have s2 := subadditive (Γ := Γ) (loB Ψ C) (hiB Ψ C) (gridT x) (succ q) (pairT q x)
  -- each interval
  have s3 : Γ ⊢[PRAAx] le (ap2 (sumF (lenB (loB Ψ C) (hiB Ψ C))) (succ q) (pairT q x))
      (succ q * inst2 (Lt Ψ C) q x) := by
    refine sum_le_const _ (.allI (.impI ?_))
    have e : inst2 (lenB (loB Ψ C) (hiB Ψ C)) (var 0) (Syn.shift (pairT q x)) =
        monus (hiT Ψ C (var 0) (fstT (Syn.shift (pairT q x))) (sndT (Syn.shift (pairT q x))))
          (loT Ψ C (var 0) (fstT (Syn.shift (pairT q x))) (sndT (Syn.shift (pairT q x)))) := by
      simp [lenB, loB, hiB, inst2]
    rw [e]
    refine le_congr (.eqRefl _) ?_ (len_le Ψ C _ _ _)
    rw [← inst2_Lt, show Syn.shift (inst2 (Lt Ψ C) q x) = inst2 (Lt Ψ C) (Syn.shift q) (Syn.shift x) by
      simp [inst2, Syn.shift, Syn.subst_subst]; congr 1; funext i; fin_cases i <;> rfl]
    rw [shift_pairT]
    exact congrInst2 _ (fst_pair _ _) (snd_pair _ _)
  -- `(q + 1) · 2Ψ(q) R!/q ≤ 4 R! Ψ(q)` when the gate is open
  have s4 : Γ ⊢[PRAAx] le (succ q * inst2 (Lt Ψ C) q x) (inst2 (bndB Ψ C) q x) := by
    rw [inst2_Lt]
    have eb : inst2 (bndB Ψ C) q x = num 4 * fact (pR x) * (gate C (pS x) q * Syn.subst ![q] Ψ) := by
      simp [bndB, gpB, inst2, subst_one_vec, subst_ap2]
    rw [eb]
    refine .orE (gate_cases (Γ := Γ) C (pS x) q) ?_ ?_
    · have h0 : ((gate C (pS x) q ≐ zero) :: Γ) ⊢[PRAAx]
          succ q * (gate C (pS x) q * (two * (Syn.subst ![q] Ψ * cof q x))) ≐ zero :=
        (congrMul (.eqRefl _) ((congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _))).eqTrans (mul_zero _)
      exact le_congr h0.eqSymm (.eqRefl _) (zero_le _)
    · let Δ : List (Fm PTm n) := (gate C (pS x) q ≐ one ⋏ le (Syn.subst ![pS x] C) q) :: Γ
      have h1 : Δ ⊢[PRAAx] gate C (pS x) q ≐ one := Prf.andE₁ Prf.hyp0
      have hq1 : Δ ⊢[PRAAx] le one q := le_trans hC.wk (Prf.andE₂ Prf.hyp0)
      have hqR : Δ ⊢[PRAAx] le q (pR x) := (succ_monus_succ _ _).eqSymm.eqTrans hq.wk
      have hf := natEq (fact_dvd hq1 hqR)
      have eq1 := natEq (eq_add_of_le hq1)
      have eg := natEq h1
      refine le_of_eq_add (d := two * Syn.subst ![q] Ψ * cof q x * monus q one) ?_
      apply deriveNat; ipra_simps
      rw [eg, hf, eq1]
      ring
  exact le_congr e1.eqSymm (.eqRefl _) (le_trans s1 (le_trans s2 (le_trans s3 s4)))

/-- The estimate (K1) for given `m, R, G` (parameters `x = ⟨R, ⟨G, m⟩⟩`). -/
theorem khinchin_core {x : PTm n} (hC : Γ ⊢[PRAAx] le one (Syn.subst ![pS x] C))
    (hKC : Γ ⊢[PRAAx] le (pw two (pS x) * ap2 (sumF (gpB Ψ C)) (succ (pR x)) x) (pG x)) :
    Γ ⊢[PRAAx] le (pw two (sndT (sndT x)) * unionMeasure Ψ C x) (gridT x) := by
  have u1 := union_le (Γ := Γ) (aB Ψ C) (gridT x) (succ (pR x)) x
  have u2 : Γ ⊢[PRAAx] le (ap2 (sumF (pB (aB Ψ C))) (succ (pR x)) (pairT (gridT x) x))
      (ap2 (sumF (bndB Ψ C)) (succ (pR x)) x) := by
    refine sum_le_params _ _ _ _ _ (.allI (.impI ?_))
    have e : Syn.shift (pairT (gridT x) x) = pairT (gridT (Syn.shift x)) (Syn.shift x) := by simp [Syn.shift]
    rw [e]
    have hC' : (lt (var 0) (Syn.shift (succ (pR x))) :: Γ.map Fm.shift) ⊢[PRAAx]
        le one (Syn.subst ![pS (Syn.shift x)] C) := by
      have a := hC.shift
      simp only [Fm.shift, subst_le, subst_one_vec, subst_sndT, ConciseIPRA.PTm.subst_succ,
        ConciseIPRA.PTm.subst_zero] at a
      exact a.wk
    have hq : (lt (var 0) (Syn.shift (succ (pR x))) :: Γ.map Fm.shift) ⊢[PRAAx]
        lt (var 0) (succ (pR (Syn.shift x))) := by
      have e2 : Syn.shift (succ (pR x)) = succ (pR (Syn.shift x)) := by simp [Syn.shift]
      rw [← e2]; exact Prf.hyp0
    exact point_bound Ψ C hC' hq
  have u3 : Γ ⊢[PRAAx] ap2 (sumF (bndB Ψ C)) (succ (pR x)) x ≐
      (num 4 * fact (pR x)) * ap2 (sumF (gpB Ψ C)) (succ (pR x)) x := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    have e : inst2 (bndB Ψ C) (var 0) (Syn.shift x) =
        Syn.shift (num 4 * fact (pR x)) * inst2 (gpB Ψ C) (var 0) (Syn.shift x) := by
      simp [bndB, inst2, Syn.shift, subst_ap2]
    rw [e]; exact .eqRefl _
  have hU := le_congr (.eqRefl _) u3 (le_trans u1 u2)
  -- `2^m · 4 R! S = R! · 2^{m+2} S ≤ R! G`
  have h2 := natEq (pw_succ (Γ := Γ) two (succ (sndT (sndT x))))
  have h1 := natEq (pw_succ (Γ := Γ) two (sndT (sndT x)))
  have hm : Γ ⊢[PRAAx] le (pw two (sndT (sndT x)) * unionMeasure Ψ C x)
      (fact (pR x) * (pw two (pS x) * ap2 (sumF (gpB Ψ C)) (succ (pR x)) x)) := by
    refine le_congr (.eqRefl _) ?_ (HurwitzMargin.le_mul_mono (pw two (sndT (sndT x))) hU)
    apply deriveNat; ipra_simps; rw [h2, h1]; ring
  refine le_trans hm (le_congr (.eqRefl _) ?_ (HurwitzMargin.le_mul_mono (fact (pR x)) hKC))
  exact mul_comm _ _

end Estimate

/-! ## The closed sentence -/

section Closed

variable (Ψ C : PTm 1)

/-- Variables `0 = m`, `1 = R`, `2 = G`; `x = ⟨R, ⟨G, m⟩⟩`. -/
abbrev xK : PTm 3 := pairT (var 1) (pairT (var 2) (var 0))

/-- `C(m+2) ≥ 1 → (K-C) at s = m + 2 → 2^m |⋃_{q=C(m+2)}^R A_q| ≤ 1` (in cells of `[0, 1]`). -/
def khinchinFormula : Fm PTm 3 :=
  le one (Syn.subst ![pS xK] C) ⟶
    (le (pw two (pS xK) * ap2 (sumF (gpB Ψ C)) (succ (pR xK)) xK) (pG xK) ⟶
      le (pw two (sndT (sndT xK)) * unionMeasure Ψ C xK) (gridT xK))

/-- (K1), the convergent half of the finite Khinchin theorem, as a closed sentence of iPRA. -/
theorem khinchin_convergent : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (khinchinFormula Ψ C) :=
  closeUniv 3 (.impI (.impI (khinchin_core Ψ C Prf.hyp1 Prf.hyp0)))

end Closed

end LeanProofs.IPRA.DiophantineNumberTheory.KhinchinConvergence
