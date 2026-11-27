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

variable {n : ℕ} {Γ : List (Fm PTm n)}

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
    Γ ⊢[PRAAx] lt (a + h * b) (h * h) := by
  have h₁ := natEq (eq_add_of_le ha); have h₂ := natEq (eq_add_of_le hb)
  refine le_of_eq_add (d := monus h (succ a) + h * monus h (succ b)) ?_
  ipra_lc Groth.ι (Q.mk _ h) * h₂ + h₁

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
  have php := Pigeonhole.pigeonhole (sig_range hh (u := u) (v := v) (D := D))
  have hlt := Prf.andE₁ php
  have hJK := Prf.andE₁ (Prf.andE₂ php)
  have ec := (at_code (Γ := Γ) h u v D _).eqSymm.eqTrans ((Prf.andE₂ (Prf.andE₂ php)).eqTrans (at_code _ _ _ _ _))
  have dg := digit_eq hh (rem_lt' hh _) (rem_lt' hh _) ec
  -- `j₀ = t + i₀`.
  have hJ : Γ ⊢[PRAAx] Pigeonhole.phpJ sigB (h * h) (code h u v D) ≐
      tRet h u v D + Pigeonhole.phpI sigB (h * h) (code h u v D) :=
    (eq_add_of_le (le_of_lt hlt)).eqTrans (add_comm _ _)
  have ad := add_formula (Γ := Γ) (u := u) (v := v) (D := D) (tRet h u v D) (Pigeonhole.phpI sigB (h * h) (code h u v D))
  have erx := natEq (Prf.andE₁ dg); have ery := natEq (Prf.andE₂ dg)
  refine .andI ?_ (.andI ?_ (.andI ?_ ?_))
  · -- `t ≥ 1`.
    refine le_of_eq_add (d := monus (Pigeonhole.phpJ sigB (h * h) (code h u v D))
      (succ (Pigeonhole.phpI sigB (h * h) (code h u v D)))) ?_
    have w := natEq (eq_add_of_le hlt)
    ipra_lc w - natEq ((eq_add_of_le (le_of_lt hlt)).eqTrans (add_comm _ _))
  · exact le_trans (le_of_eq_add (d := Pigeonhole.phpI sigB (h * h) (code h u v D)) hJ) hJK
  · refine rem_eq_of_eq hh
      (k₁ := PX u v D (Pigeonhole.phpI sigB (h * h) (code h u v D)) *
        quo (PX u v D (Pigeonhole.phpI sigB (h * h) (code h u v D))) h +
        D * (PY u v D (Pigeonhole.phpI sigB (h * h) (code h u v D)) *
          quo (PY u v D (Pigeonhole.phpJ sigB (h * h) (code h u v D))) h))
      (k₂ := PX u v D (Pigeonhole.phpI sigB (h * h) (code h u v D)) *
        quo (PX u v D (Pigeonhole.phpJ sigB (h * h) (code h u v D))) h +
        D * (PY u v D (Pigeonhole.phpI sigB (h * h) (code h u v D)) *
          quo (PY u v D (Pigeonhole.phpI sigB (h * h) (code h u v D))) h)) ?_
    ipra_lc -Groth.ι (Q.mk _ (PX u v D (Pigeonhole.phpI sigB (h * h) (code h u v D)))) * natEq (div_eq (j := PX u v D (Pigeonhole.phpI sigB (h * h) (code h u v D))) hh) +
      Groth.ι (Q.mk _ (PX u v D (Pigeonhole.phpI sigB (h * h) (code h u v D)))) * natEq (div_eq (j := PX u v D (Pigeonhole.phpJ sigB (h * h) (code h u v D))) hh) -
      Groth.ι (Q.mk _ D) * Groth.ι (Q.mk _ (PY u v D (Pigeonhole.phpI sigB (h * h) (code h u v D)))) * natEq (div_eq (j := PY u v D (Pigeonhole.phpJ sigB (h * h) (code h u v D))) hh) +
      Groth.ι (Q.mk _ D) * Groth.ι (Q.mk _ (PY u v D (Pigeonhole.phpI sigB (h * h) (code h u v D)))) * natEq (div_eq (j := PY u v D (Pigeonhole.phpI sigB (h * h) (code h u v D))) hh) +
      (1 - Groth.ι (Q.mk _ (PX u v D (tRet h u v D)))) * natEq (pell_norm hU (Pigeonhole.phpI sigB (h * h) (code h u v D))) -
      Groth.ι (Q.mk _ (PX u v D (Pigeonhole.phpI sigB (h * h) (code h u v D)))) * natEq ((congrPX u v D hJ).eqTrans (Prf.andE₁ ad)) +
      Groth.ι (Q.mk _ D) * Groth.ι (Q.mk _ (PY u v D (Pigeonhole.phpI sigB (h * h) (code h u v D)))) * natEq ((congrPY u v D hJ).eqTrans (Prf.andE₂ ad)) -
      Groth.ι (Q.mk _ (PX u v D (Pigeonhole.phpI sigB (h * h) (code h u v D)))) * erx +
      Groth.ι (Q.mk _ D) * Groth.ι (Q.mk _ (PY u v D (Pigeonhole.phpI sigB (h * h) (code h u v D)))) * ery
  · refine rem_eq_of_eq hh
      (k₁ := PX u v D (Pigeonhole.phpI sigB (h * h) (code h u v D)) *
        quo (PY u v D (Pigeonhole.phpI sigB (h * h) (code h u v D))) h +
        PY u v D (Pigeonhole.phpI sigB (h * h) (code h u v D)) *
          quo (PX u v D (Pigeonhole.phpJ sigB (h * h) (code h u v D))) h)
      (k₂ := PX u v D (Pigeonhole.phpI sigB (h * h) (code h u v D)) *
        quo (PY u v D (Pigeonhole.phpJ sigB (h * h) (code h u v D))) h +
        PY u v D (Pigeonhole.phpI sigB (h * h) (code h u v D)) *
          quo (PX u v D (Pigeonhole.phpI sigB (h * h) (code h u v D))) h) ?_
    ipra_lc Groth.ι (Q.mk _ (PY u v D (Pigeonhole.phpI sigB (h * h) (code h u v D)))) * natEq ((congrPX u v D hJ).eqTrans (Prf.andE₁ ad)) -
      Groth.ι (Q.mk _ (PX u v D (Pigeonhole.phpI sigB (h * h) (code h u v D)))) * natEq ((congrPY u v D hJ).eqTrans (Prf.andE₂ ad)) -
      Groth.ι (Q.mk _ (PY u v D (tRet h u v D))) * natEq (pell_norm hU (Pigeonhole.phpI sigB (h * h) (code h u v D))) -
      Groth.ι (Q.mk _ (PX u v D (Pigeonhole.phpI sigB (h * h) (code h u v D)))) * ery +
      Groth.ι (Q.mk _ (PY u v D (Pigeonhole.phpI sigB (h * h) (code h u v D)))) * erx -
      Groth.ι (Q.mk _ (PX u v D (Pigeonhole.phpI sigB (h * h) (code h u v D)))) * natEq (div_eq (j := PY u v D (Pigeonhole.phpI sigB (h * h) (code h u v D))) hh) -
      Groth.ι (Q.mk _ (PY u v D (Pigeonhole.phpI sigB (h * h) (code h u v D)))) * natEq (div_eq (j := PX u v D (Pigeonhole.phpJ sigB (h * h) (code h u v D))) hh) +
      Groth.ι (Q.mk _ (PX u v D (Pigeonhole.phpI sigB (h * h) (code h u v D)))) * natEq (div_eq (j := PY u v D (Pigeonhole.phpJ sigB (h * h) (code h u v D))) hh) +
      Groth.ι (Q.mk _ (PY u v D (Pigeonhole.phpI sigB (h * h) (code h u v D)))) * natEq (div_eq (j := PX u v D (Pigeonhole.phpI sigB (h * h) (code h u v D))) hh)

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
