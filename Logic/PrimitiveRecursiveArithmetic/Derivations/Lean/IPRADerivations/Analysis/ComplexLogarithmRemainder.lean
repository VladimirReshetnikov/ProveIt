import IPRADerivations.Analysis.LogarithmRemainder
import IPRADerivations.Core.IntOrder

/-!
# The finite complex logarithm tail

Gaussian integers are coded as a pair of signed-coordinate pairs. The actual
alternating finite Taylor numerator uses the same factorial/power denominator
as `LogarithmRemainder`: `G₀ = 0` and
`G_(L+1) = (L+3) N G_L - (L+2)! (-z)^(L+3)`.
The exponent encodes exactly the Taylor sign `(-1)^L` in degree `L+3`.

The finite complex estimate is proved from the Gaussian product identity and
the squared-norm triangle inequality, with every degree internal to iPRA.
The finite canonical factor is `Q_L = N G_L / D_L`; thus the checked bound
`|3 N³ G_L|² ≤ (2R³D_L)²` says `|Q_L| ≤ 2R³/(3N²)` when `N ≥ 1`.
At `N = R = 0` only the denominator-cleared polynomial statement is intended.
The analytic identification with an infinite logarithm remains separate.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Probability.Variance (ad)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.Analysis.LogarithmRemainder
  (numerator denominator three numerator_zero numerator_succ denominator_positive finite_taylor_bound)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

def re (c : PTm n) : ZT n := ⟨fstT (fstT c), sndT (fstT c)⟩
def im (c : PTm n) : ZT n := ⟨fstT (sndT c), sndT (sndT c)⟩

def code (x y : ZT n) : PTm n := pairT (pairT x.pos x.neg) (pairT y.pos y.neg)
def add (a b : PTm n) : PTm n := code (re a + re b) (im a + im b)
def mul (a b : PTm n) : PTm n := code (re a * re b - im a * im b) (re a * im b + im a * re b)
def neg (a : PTm n) : PTm n := code (-re a) (-im a)
def scale (C a : PTm n) : PTm n := code (ZT.ofNat C * re a) (ZT.ofNat C * im a)
def zeroCode : PTm n := code (ZT.ofNat zero) (ZT.ofNat zero)
def oneCode : PTm n := code (ZT.ofNat one) (ZT.ofNat zero)

def normSq (c : PTm n) : PTm n :=
  ad (re c).pos (re c).neg * ad (re c).pos (re c).neg +
    ad (im c).pos (im c).neg * ad (im c).pos (im c).neg

def bounded (c R : PTm n) : Fm PTm n := le (normSq c) (R * R)

@[simp] theorem subst_re {m : ℕ} (σ : Fin n → PTm m) (c : PTm n) :
    (re c).subst σ = re (Syn.subst σ c) := by simp [re, ZT.subst]
@[simp] theorem subst_im {m : ℕ} (σ : Fin n → PTm m) (c : PTm n) :
    (im c).subst σ = im (Syn.subst σ c) := by simp [im, ZT.subst]
@[simp] theorem subst_code {m : ℕ} (σ : Fin n → PTm m) (x y : ZT n) :
    Syn.subst σ (code x y) = code (x.subst σ) (y.subst σ) := by simp [code, ZT.subst]
@[simp] theorem subst_add {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    Syn.subst σ (add a b) = add (Syn.subst σ a) (Syn.subst σ b) := by simp [add]
@[simp] theorem subst_mul {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    Syn.subst σ (mul a b) = mul (Syn.subst σ a) (Syn.subst σ b) := by simp [mul]
@[simp] theorem subst_neg {m : ℕ} (σ : Fin n → PTm m) (a : PTm n) :
    Syn.subst σ (neg a) = neg (Syn.subst σ a) := by simp [neg]
@[simp] theorem subst_scale {m : ℕ} (σ : Fin n → PTm m) (C a : PTm n) :
    Syn.subst σ (scale C a) = scale (Syn.subst σ C) (Syn.subst σ a) := by simp [scale]
@[simp] theorem subst_zeroCode {m : ℕ} (σ : Fin n → PTm m) :
    Syn.subst σ (zeroCode : PTm n) = (zeroCode : PTm m) := by simp [zeroCode]
@[simp] theorem subst_oneCode {m : ℕ} (σ : Fin n → PTm m) :
    Syn.subst σ (oneCode : PTm n) = (oneCode : PTm m) := by simp [oneCode]
@[simp] theorem subst_normSq {m : ℕ} (σ : Fin n → PTm m) (c : PTm n) :
    Syn.subst σ (normSq c) = normSq (Syn.subst σ c) := by
  simp [normSq, ad, re, im]
@[simp] theorem subst_bounded {m : ℕ} (σ : Fin n → PTm m) (c R : PTm n) :
    (bounded c R).subst σ = bounded (Syn.subst σ c) (Syn.subst σ R) := by simp [bounded]

theorem eval_re_code (x y : ZT n) : ZT.toZ Γ (re (code x y)) = ZT.toZ Γ x := by
  have a := natEq ((congrFst (fst_pair (pairT x.pos x.neg) (pairT y.pos y.neg))).eqTrans
    (fst_pair x.pos x.neg) : Γ ⊢[PRAAx] _)
  have b := natEq ((congrSnd (fst_pair (pairT x.pos x.neg) (pairT y.pos y.neg))).eqTrans
    (snd_pair x.pos x.neg) : Γ ⊢[PRAAx] _)
  simp only [re, code, ZT.toZ]
  linear_combination a - b

theorem eval_im_code (x y : ZT n) : ZT.toZ Γ (im (code x y)) = ZT.toZ Γ y := by
  have a := natEq ((congrFst (snd_pair (pairT x.pos x.neg) (pairT y.pos y.neg))).eqTrans
    (fst_pair y.pos y.neg) : Γ ⊢[PRAAx] _)
  have b := natEq ((congrSnd (snd_pair (pairT x.pos x.neg) (pairT y.pos y.neg))).eqTrans
    (snd_pair y.pos y.neg) : Γ ⊢[PRAAx] _)
  simp only [im, code, ZT.toZ]
  linear_combination a - b

theorem normSq_eval (c : PTm n) :
    𝔞(normSq c) = ZT.toZ Γ (re c) ^ 2 + ZT.toZ Γ (im c) ^ 2 := by
  have r := sq_nat (Γ := Γ) (re c)
  have i := sq_nat (Γ := Γ) (im c)
  simp only [ZT.toZ_sq] at r i
  simp only [normSq, Q.mk_add, map_add]
  linear_combination -r - i

theorem normSq_code (x y : ZT n) :
    𝔞(normSq (code x y)) = ZT.toZ Γ x ^ 2 + ZT.toZ Γ y ^ 2 := by
  rw [normSq_eval, eval_re_code, eval_im_code]

theorem normSq_mul (a b : PTm n) :
    Γ ⊢[PRAAx] normSq (mul a b) ≐ normSq a * normSq b := by
  apply deriveNat
  simp only [Q.mk_mul, map_mul]
  rw [mul, normSq_code, normSq_eval, normSq_eval]
  simp only [ZT.toZ_sub, ZT.toZ_add, ZT.toZ_mul]
  ring

theorem normSq_scale (C a : PTm n) :
    Γ ⊢[PRAAx] normSq (scale C a) ≐ C * C * normSq a := by
  apply deriveNat
  simp only [Q.mk_mul, map_mul]
  rw [scale, normSq_code, normSq_eval]
  simp only [ZT.toZ_mul, ZT.toZ_ofNat]
  ring

theorem normSq_neg (a : PTm n) : Γ ⊢[PRAAx] normSq (neg a) ≐ normSq a := by
  apply deriveNat
  rw [neg, normSq_code, normSq_eval]
  simp only [ZT.toZ_neg]
  ring

theorem normSq_zero : Γ ⊢[PRAAx] normSq (zeroCode : PTm n) ≐ zero := by
  apply deriveNat
  rw [zeroCode, normSq_code]
  simp

theorem normSq_one : Γ ⊢[PRAAx] normSq (oneCode : PTm n) ≐ one := by
  apply deriveNat
  rw [oneCode, normSq_code]
  simp

theorem congr_normSq {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) :
    Γ ⊢[PRAAx] normSq a ≐ normSq b := by
  have e := Prf.eqCongr (normSq (var 0 : PTm 1)) (fun _ => h)
  simpa only [subst_normSq, Syn.subst_var] using e

theorem bounded_mul {a b R S : PTm n} (ha : Γ ⊢[PRAAx] bounded a R)
    (hb : Γ ⊢[PRAAx] bounded b S) : Γ ⊢[PRAAx] bounded (mul a b) (R * S) :=
  le_congr (normSq_mul _ _).eqSymm (by ipra_ring) (le_mul_mono ha hb)

theorem bounded_scale {a R : PTm n} (C : PTm n) (ha : Γ ⊢[PRAAx] bounded a R) :
    Γ ⊢[PRAAx] bounded (scale C a) (C * R) := by
  have h := le_mul_mono (le_refl (Γ := Γ) (C * C)) ha
  exact le_congr (normSq_scale _ _).eqSymm (by ipra_ring) h

theorem bounded_neg {a R : PTm n} (ha : Γ ⊢[PRAAx] bounded a R) :
    Γ ⊢[PRAAx] bounded (neg a) R :=
  le_congr (normSq_neg _).eqSymm (.eqRefl _) ha

theorem bounded_to_zle {a R : PTm n} (ha : Γ ⊢[PRAAx] bounded a R) :
    Γ ⊢[PRAAx] zle (ZT.sq (re a) + ZT.sq (im a)) (ZT.ofNat (R * R)) := by
  have h := natEq (eq_add_of_le ha)
  refine zle_of_toZ (monus (R * R) (normSq a)) ?_
  simp only [ZT.toZ_add, ZT.toZ_sq, ZT.toZ_ofNat, Q.mk_add, map_add] at *
  rw [← normSq_eval]
  linear_combination -h

theorem bounded_add {a b R S : PTm n} (ha : Γ ⊢[PRAAx] bounded a R)
    (hb : Γ ⊢[PRAAx] bounded b S) : Γ ⊢[PRAAx] bounded (add a b) (R + S) := by
  have h := zle_toZ (triangle (bounded_to_zle ha) (bounded_to_zle hb))
  refine le_of_eq_add (d :=
    monus ((ZT.ofNat ((R + S) * (R + S))).pos +
      (ZT.sq (re a + re b) + ZT.sq (im a + im b)).neg)
      ((ZT.sq (re a + re b) + ZT.sq (im a + im b)).pos +
        (ZT.ofNat ((R + S) * (R + S))).neg)) ?_
  apply deriveNat
  simp only [Q.mk_add, map_add]
  rw [add, normSq_code]
  simp only [ZT.toZ_add, ZT.toZ_sq, ZT.toZ_ofNat] at h ⊢
  linear_combination -h

/-! ## Primitive-recursive Gaussian powers -/

def powerStep : PTm 3 := mul (var 1) (var 2)
def powerF : PR 2 := rec2 oneCode powerStep
def power (z k : PTm n) : PTm n := ap2 powerF k z

@[simp] theorem subst_power {m : ℕ} (σ : Fin n → PTm m) (z k : PTm n) :
    Syn.subst σ (power z k) = power (Syn.subst σ z) (Syn.subst σ k) := by simp [power]

theorem power_zero (z : PTm n) : Γ ⊢[PRAAx] power z zero ≐ oneCode := by
  simpa [power, powerF] using rec2_zero (Γ := Γ) oneCode powerStep z

theorem power_succ (z k : PTm n) :
    Γ ⊢[PRAAx] power z (succ k) ≐ mul (power z k) z := by
  simpa [power, powerF, powerStep] using rec2_succ (Γ := Γ) oneCode powerStep k z

/-- Every internally indexed Gaussian power has the expected norm bound. -/
theorem bounded_power (z R k : PTm n) (h : Γ ⊢[PRAAx] bounded z R) :
    Γ ⊢[PRAAx] bounded (power z k) (pw R k) := by
  have all : Γ ⊢[PRAAx] .all (bounded (power (Syn.shift z) (var 0)) (pw (Syn.shift R) (var 0))) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [subst_bounded, subst_power, subst_ap2, Syn.subst_var, Syn.inst_zero,
        Syn.subst_inst_shift]
      have l := (congr_normSq (power_zero (Γ := Γ) z)).eqTrans normSq_one
      have r := (congrMul (pw_zero (Γ := Γ) R) (pw_zero R)).eqTrans (one_mul one)
      exact le_congr l.eqSymm r.eqSymm (le_refl one)
    · simp only [subst_bounded, subst_power, subst_ap2, Syn.subst_var, Syn.repl_zero,
        subst_repl_shift]
      have shifted : Γ.map Fm.shift ⊢[PRAAx] bounded (Syn.shift z) (Syn.shift R) := by
        simpa [Fm.shift, Syn.shift] using h.shift
      have p : (bounded (power (Syn.shift z) (var 0)) (pw (Syn.shift R) (var 0))) ::
          Γ.map Fm.shift ⊢[PRAAx]
          bounded (mul (power (Syn.shift z) (var 0)) (Syn.shift z))
            (pw (Syn.shift R) (var 0) * Syn.shift R) := bounded_mul Prf.hyp0 shifted.wk
      exact le_congr (congr_normSq (power_succ _ _)).eqSymm
        (congrMul (pw_succ _ _) (pw_succ _ _)).eqSymm p
  simpa only [subst_bounded, subst_power, subst_ap2, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift] using Prf.allE k all

#print axioms bounded_power

/-! ## The actual alternating complex Taylor numerator -/

/-- Variables `0 = L`, `1 = G_L`, `2 = z`, `3 = N`. -/
def seriesStep : PTm 4 :=
  add (scale ((var 0 + three) * var 3) (var 1))
    (neg (scale (fact (var 0 + two)) (power (neg (var 2)) (var 0 + three))))

def seriesF : PR 3 := recDef zeroCode seriesStep
def series (z N L : PTm n) : PTm n := ap3 seriesF L z N

@[simp] theorem subst_series {m : ℕ} (σ : Fin n → PTm m) (z N L : PTm n) :
    Syn.subst σ (series z N L) = series (Syn.subst σ z) (Syn.subst σ N) (Syn.subst σ L) := by
  simp [series]

theorem series_zero (z N : PTm n) : Γ ⊢[PRAAx] series z N zero ≐ zeroCode := by
  have h := rec_zero (Γ := Γ) (zeroCode : PTm 2) seriesStep ![z, N]
  have e : (Fin.cases zero ![z, N] : Fin 3 → PTm n) = ![zero, z, N] := by
    funext i; fin_cases i <;> rfl
  rw [e] at h
  simpa only [series, seriesF, ap3, subst_zeroCode] using h

theorem series_succ (z N L : PTm n) :
    Γ ⊢[PRAAx] series z N (succ L) ≐
      add (scale ((L + three) * N) (series z N L))
        (neg (scale (fact (L + two)) (power (neg z) (L + three)))) := by
  have h := rec_succ (Γ := Γ) (zeroCode : PTm 2) seriesStep L ![z, N]
  have e₁ : (Fin.cases (succ L) ![z, N] : Fin 3 → PTm n) = ![succ L, z, N] := by
    funext i; fin_cases i <;> rfl
  have e₂ : (Fin.cases L
      (Fin.cases (ConciseIPRA.PTm.app (recDef (zeroCode : PTm 2) seriesStep) (Fin.cases L ![z, N])) ![z, N]) :
      Fin 4 → PTm n) = ![L, series z N L, z, N] := by
    funext i; fin_cases i <;> rfl
  rw [e₁, e₂] at h
  simpa [series, seriesF, ap3, seriesStep] using h

/-- Domination of the actual alternating Gaussian numerator by the positive
finite Taylor numerator. No sign or triangle estimate is assumed. -/
theorem bounded_series (z N R L : PTm n) (hz : Γ ⊢[PRAAx] bounded z R) :
    Γ ⊢[PRAAx] bounded (series z N L) (numerator R N L) := by
  have all : Γ ⊢[PRAAx] .all
      (bounded (series (Syn.shift z) (Syn.shift N) (var 0))
        (numerator (Syn.shift R) (Syn.shift N) (var 0))) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [subst_bounded, subst_series, LogarithmRemainder.subst_numerator,
        Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      have l := (congr_normSq (series_zero (Γ := Γ) z N)).eqTrans normSq_zero
      have r := (congrMul (numerator_zero (Γ := Γ) R N) (numerator_zero R N)).eqTrans (mul_zero zero)
      exact le_congr l.eqSymm r.eqSymm (le_refl zero)
    · simp only [subst_bounded, subst_series, LogarithmRemainder.subst_numerator,
        Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      have shifted : Γ.map Fm.shift ⊢[PRAAx] bounded (Syn.shift z) (Syn.shift R) := by
        simpa [Fm.shift, Syn.shift] using hz.shift
      have ih : (bounded (series (Syn.shift z) (Syn.shift N) (var 0))
          (numerator (Syn.shift R) (Syn.shift N) (var 0))) :: Γ.map Fm.shift ⊢[PRAAx]
          bounded (series (Syn.shift z) (Syn.shift N) (var 0))
            (numerator (Syn.shift R) (Syn.shift N) (var 0)) := Prf.hyp0
      have first := bounded_scale ((var 0 + three) * Syn.shift N) ih
      have second := bounded_neg (bounded_scale (fact (var 0 + two))
        (bounded_power (neg (Syn.shift z)) (Syn.shift R) (var 0 + three)
          (bounded_neg (shifted.wk (ψ := bounded (series (Syn.shift z) (Syn.shift N) (var 0))
            (numerator (Syn.shift R) (Syn.shift N) (var 0)))))))
      have combined := bounded_add first second
      exact le_congr (congr_normSq (series_succ _ _ _)).eqSymm
        (congrMul (numerator_succ _ _ _) (numerator_succ _ _ _)).eqSymm combined
  simpa only [subst_bounded, subst_series, LogarithmRemainder.subst_numerator,
    Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using Prf.allE L all

theorem bounded_mono {z R S : PTm n} (hz : Γ ⊢[PRAAx] bounded z R)
    (h : Γ ⊢[PRAAx] le R S) : Γ ⊢[PRAAx] bounded z S :=
  le_trans hz (le_mul_mono h h)

/-- A genuine finite complex canonical-factor estimate with all denominators
cleared: `|3 N³ G_L|² ≤ (2R³D_L)²`. -/
theorem canonical_bound (z N R L : PTm n) (hz : Γ ⊢[PRAAx] bounded z R)
    (hN : Γ ⊢[PRAAx] le (two * R) N) :
    Γ ⊢[PRAAx] bounded (scale (three * N * N * N) (series z N L))
      (two * R * R * R * denominator N L) :=
  bounded_mono (bounded_scale _ (bounded_series z N R L hz)) (finite_taylor_bound R N L hN)

/-- Variables `0 = L`, `1 = z` (a coded Gaussian integer), `2 = R`. -/
def powerFormula : Fm PTm 3 :=
  bounded (var 1) (var 2) ⟶ bounded (power (var 1) (var 0)) (pw (var 2) (var 0))

theorem gaussian_power_bound : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 powerFormula :=
  closeUniv 3 (.impI (bounded_power _ _ _ Prf.hyp0))

/-- Variables `0 = L`, `1 = z`, `2 = N`, `3 = R`. -/
def dominationFormula : Fm PTm 4 :=
  bounded (var 1) (var 3) ⟶
    bounded (series (var 1) (var 2) (var 0)) (numerator (var 3) (var 2) (var 0))

theorem finite_complex_logarithm_domination :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 dominationFormula :=
  closeUniv 4 (.impI (bounded_series _ _ _ _ Prf.hyp0))

/-- Variables `0 = L`, `1 = z`, `2 = N`, `3 = R`. -/
def canonicalFormula : Fm PTm 4 :=
  bounded (var 1) (var 3) ⟶ le (two * var 3) (var 2) ⟶
    bounded (scale (three * var 2 * var 2 * var 2) (series (var 1) (var 2) (var 0)))
      (two * var 3 * var 3 * var 3 * denominator (var 2) (var 0))

theorem finite_complex_canonical_factor_bound :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 canonicalFormula :=
  closeUniv 4 (.impI (.impI (canonical_bound _ _ _ _ Prf.hyp1 Prf.hyp0)))

/-- Variables `0 = L`, `1 = z`, `2 = N`. The coded exact rational evaluator
retains a positive common denominator whenever its input divisor is positive. -/
def evaluatorFormula : Fm PTm 3 :=
  (series (var 1) (var 2) zero ≐ zeroCode) ⋏
    ((series (var 1) (var 2) (succ (var 0)) ≐
        add (scale ((var 0 + three) * var 2) (series (var 1) (var 2) (var 0)))
          (neg (scale (fact (var 0 + two)) (power (neg (var 1)) (var 0 + three))))) ⋏
      (le one (var 2) ⟶ le one (denominator (var 2) (var 0))))

theorem exact_finite_complex_taylor_evaluator :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 evaluatorFormula :=
  closeUniv 3 (.andI (series_zero _ _) (.andI (series_succ _ _ _)
    (.impI (denominator_positive _ _ Prf.hyp0))))

#print axioms normSq_mul
#print axioms gaussian_power_bound
#print axioms finite_complex_logarithm_domination
#print axioms finite_complex_canonical_factor_bound
#print axioms exact_finite_complex_taylor_evaluator

end LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder
