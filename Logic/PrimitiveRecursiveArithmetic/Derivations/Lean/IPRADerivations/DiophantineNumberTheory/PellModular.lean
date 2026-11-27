import IPRADerivations.DiophantineNumberTheory.PellGcd
import IPRADerivations.Core.Pigeonhole

/-!
# Pell powers return to `(1, 0)` modulo `h`

Packet: `diophantine-number-theory/pell_ipra_2026-11-15`, Theorem `thm:modular`: for every
`h ≥ 1` one can compute `t` with `1 ≤ t ≤ h²`, `X_t ≡ 1` and `Y_t ≡ 0 (mod h)`.

The residue pair `σ(k) = (X_k mod h) + h (Y_k mod h) < h²` collides on `0, …, h²` (`Pigeonhole`),
at `i₀ < j₀`; with `t = j₀ − i₀`, the exact identities `X_t + D Y_i Y_j = X_i X_j` and
`Y_t + X_j Y_i = X_i Y_j` (addition formula and norm) turn equal residues into the congruences.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.PellModular

open_ipra exports
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel)
open LeanProofs.IPRA.DiophantineNumberTheory.PellGcd
open LeanProofs.IPRA.Foundations.ChineseRemainder (rem_of_balanced_add rem_mul_right_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Congruence of the Pell powers in all arguments -/

theorem congrPX4 {u u' v v' D D' m m' : PTm n} (hu : Γ ⊢[PRAAx] u ≐ u') (hv : Γ ⊢[PRAAx] v ≐ v')
    (hD : Γ ⊢[PRAAx] D ≐ D') (hm : Γ ⊢[PRAAx] m ≐ m') : Γ ⊢[PRAAx] PX u v D m ≐ PX u' v' D' m' := by
  unfold PX Recurrences.X sim₁
  refine congrFst (congrApp _ fun i => ?_)
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hm
  · fin_cases j
    · exact hu
    · exact hv
    · exact hD

theorem congrPY4 {u u' v v' D D' m m' : PTm n} (hu : Γ ⊢[PRAAx] u ≐ u') (hv : Γ ⊢[PRAAx] v ≐ v')
    (hD : Γ ⊢[PRAAx] D ≐ D') (hm : Γ ⊢[PRAAx] m ≐ m') : Γ ⊢[PRAAx] PY u v D m ≐ PY u' v' D' m' := by
  unfold PY Recurrences.Y sim₂
  refine congrSnd (congrApp _ fun i => ?_)
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hm
  · fin_cases j
    · exact hu
    · exact hv
    · exact hD

/-! ## The residue code -/

/-- Decoding `x = ⟨h, ⟨u, ⟨v, D⟩⟩⟩`. -/
abbrev dH (x : PTm n) : PTm n := fstT x
abbrev dU (x : PTm n) : PTm n := fstT (sndT x)
abbrev dV (x : PTm n) : PTm n := fstT (sndT (sndT x))
abbrev dD (x : PTm n) : PTm n := sndT (sndT (sndT x))

abbrev code (h u v D : PTm n) : PTm n := pairT h (pairT u (pairT v D))

/-- `σ(k) = (X_k mod h) + h (Y_k mod h)`, over `0 = k`, `1 = x`. -/
abbrev sigB : PTm 2 :=
  rem (PX (dU (var 1)) (dV (var 1)) (dD (var 1)) (var 0)) (dH (var 1)) +
    dH (var 1) * rem (PY (dU (var 1)) (dV (var 1)) (dD (var 1)) (var 0)) (dH (var 1))

theorem inst2_sig (k x : PTm n) :
    inst2 sigB k x = rem (PX (dU x) (dV x) (dD x) k) (dH x) + dH x * rem (PY (dU x) (dV x) (dD x) k) (dH x) := by
  simp [inst2]

theorem at_code (h u v D k : PTm n) :
    Γ ⊢[PRAAx] inst2 sigB k (code h u v D) ≐ rem (PX u v D k) h + h * rem (PY u v D k) h := by
  rw [inst2_sig]
  have eh : Γ ⊢[PRAAx] dH (code h u v D) ≐ h := fst_pair _ _
  have eu : Γ ⊢[PRAAx] dU (code h u v D) ≐ u := (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
  have ev : Γ ⊢[PRAAx] dV (code h u v D) ≐ v :=
    (congrFst ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
  have eD : Γ ⊢[PRAAx] dD (code h u v D) ≐ D :=
    (congrSnd ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)
  exact congrAdd (congrAp2 remF (congrPX4 eu ev eD (.eqRefl _)) eh)
    (congrMul eh (congrAp2 remF (congrPY4 eu ev eD (.eqRefl _)) eh))

/-- `a < h`, `b < h` give `a + h b < h²`. -/
theorem digit_lt {a b h : PTm n} (ha : Γ ⊢[PRAAx] lt a h) (hb : Γ ⊢[PRAAx] lt b h) :
    Γ ⊢[PRAAx] lt (a + h * b) (h * h) :=
  lt_congr ((congrAdd (mul_comm _ _) (.eqRefl _)).eqTrans (add_comm _ _))
    (.eqRefl _) (Order.mul_add_lt_mul hb ha)

/-- Two-digit uniqueness: `a + h b = a' + h b'` with `a, a' < h`. -/
theorem digit_eq {a b a' b' h : PTm n} (hh : Γ ⊢[PRAAx] h ≐ succ (pred h)) (ha : Γ ⊢[PRAAx] lt a h)
    (ha' : Γ ⊢[PRAAx] lt a' h) (e : Γ ⊢[PRAAx] a + h * b ≐ a' + h * b') :
    Γ ⊢[PRAAx] a ≐ a' ⋏ b ≐ b' := by
  have r₁ := rem_eq' hh (z := a + h * b) (q := b) (r := a) (add_comm _ _) ha
  have r₂ := rem_eq' hh (z := a' + h * b') (q := b') (r := a') (add_comm _ _) ha'
  have ea := r₁.eqSymm.eqTrans ((congrAp2 remF e (.eqRefl _)).eqTrans r₂)
  refine .andI ea (mul_cancel hh ?_)
  ipra_lc natEq e - natEq ea

/-! ## The theorem -/

section Main

variable {h u v D : PTm n} (hU : Γ ⊢[PRAAx] u * u ≐ D * (v * v) + one) (hh : Γ ⊢[PRAAx] h ≐ succ (pred h))
include hU hh

omit hU in
theorem sig_range : Γ ⊢[PRAAx] Permutation.rangeAll sigB (h * h) (code h u v D) := by
  refine .allI ?_
  have e : Syn.shift (code h u v D) = code (Syn.shift h) (Syn.shift u) (Syn.shift v) (Syn.shift D) := by
    simp [Syn.shift]
  rw [e, AnalyticNumberTheory.SumPhi.shift_mul']
  have hh' := AnalyticNumberTheory.GcdFiber.shift_pos hh
  exact lt_congr (at_code _ _ _ _ _).eqSymm (.eqRefl _) (digit_lt (rem_lt' hh' _) (rem_lt' hh' _))

/-- The returning exponent `t = j₀ − i₀`. -/
abbrev tRet (h u v D : PTm n) : PTm n :=
  monus (Pigeonhole.phpJ sigB (h * h) (code h u v D)) (Pigeonhole.phpI sigB (h * h) (code h u v D))

/-- `thm:modular` at arbitrary terms. -/
theorem pell_modular_at :
    Γ ⊢[PRAAx] le one (tRet h u v D) ⋏ (le (tRet h u v D) (h * h) ⋏
      ((rem (PX u v D (tRet h u v D)) h ≐ rem one h) ⋏ (rem (PY u v D (tRet h u v D)) h ≐ rem zero h))) := by
  let i := Pigeonhole.phpI sigB (h * h) (code h u v D)
  let j := Pigeonhole.phpJ sigB (h * h) (code h u v D)
  let t := tRet h u v D
  let xi := PX u v D i
  let yi := PY u v D i
  let xj := PX u v D j
  let yj := PY u v D j
  let xt := PX u v D t
  let yt := PY u v D t
  have collision := Pigeonhole.pigeonhole (sig_range hh (u := u) (v := v) (D := D))
  have before : Γ ⊢[PRAAx] lt i j := collision.andE₁
  have codeEq := (at_code (Γ := Γ) h u v D i).eqSymm.eqTrans
    (collision.andE₂.andE₂.eqTrans (at_code h u v D j))
  have residues := digit_eq hh (rem_lt' hh _) (rem_lt' hh _) codeEq.eqSymm
  have difference : Γ ⊢[PRAAx] j ≐ t + i :=
    (eq_add_of_le (le_of_lt before)).eqTrans (add_comm _ _)
  have recurrence := add_formula (Γ := Γ) (u := u) (v := v) (D := D) t i
  have advanceX := natEq ((congrPX u v D difference).eqTrans recurrence.andE₁)
  have advanceY := natEq ((congrPY u v D difference).eqTrans recurrence.andE₂)
  have norm := natEq (pell_norm hU i)
  refine .andI (Common.one_le_monus_of_lt i j before)
    (.andI (le_trans (Common.monus_le_self j i) collision.andE₂.andE₁) (.andI ?_ ?_))
  · refine rem_of_balanced_add hh (a := yj * (D * yi)) (b := xj * xi) ?_ ?_
      (rem_mul_right_congr (D * yi) hh residues.andE₂) (rem_mul_right_congr xi hh residues.andE₁)
    · ipra_lc -𝔞 xi * advanceX + 𝔞 D * 𝔞 yi * advanceY - 𝔞 xt * norm
    · ipra_lc -norm
  · refine rem_of_balanced_add hh (a := xj * yi) (b := yj * xi) ?_ (zero_add (xi * yi))
      (rem_mul_right_congr yi hh residues.andE₁)
      ((rem_mul_right_congr xi hh residues.andE₂).eqTrans (congrAp2 remF (mul_comm yi xi) (.eqRefl _)))
    ipra_lc 𝔞 yi * advanceX - 𝔞 xi * advanceY - 𝔞 yt * norm

end Main

/-- `thm:modular`: variables `0 = h − 1`, `1 = u`, `2 = v`, `3 = D`. -/
abbrev pellModularFormula : Fm PTm 4 :=
  var 1 * var 1 ≐ var 3 * (var 2 * var 2) + one ⟶
    le one (tRet (succ (var 0)) (var 1) (var 2) (var 3)) ⋏
      (le (tRet (succ (var 0)) (var 1) (var 2) (var 3)) (succ (var 0) * succ (var 0)) ⋏
        ((rem (PX (var 1) (var 2) (var 3) (tRet (succ (var 0)) (var 1) (var 2) (var 3))) (succ (var 0)) ≐
            rem one (succ (var 0))) ⋏
          (rem (PY (var 1) (var 2) (var 3) (tRet (succ (var 0)) (var 1) (var 2) (var 3))) (succ (var 0)) ≐
            rem zero (succ (var 0)))))

theorem pell_modular : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 pellModularFormula :=
  closeUniv 4 (.impI (pell_modular_at Prf.hyp0 (congrSucc (pred_succ _).eqSymm)))

end LeanProofs.IPRA.DiophantineNumberTheory.PellModular
