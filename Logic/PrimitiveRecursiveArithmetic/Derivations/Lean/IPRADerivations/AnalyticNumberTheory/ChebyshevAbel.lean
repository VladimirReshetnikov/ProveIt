import IPRADerivations.AnalyticNumberTheory.SymmetryBound
import IPRADerivations.Core.LinearCombination

/-!
# Partial summation against the harmonic logarithm (`pnt_ipra_constructive_2026-11-14`, `sb:error-equation`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `selberg.tex`, proof of Lemma `sb:error-equation`:
"Integrating the finite step function `ψ` gives `Σ_{n≤x} Λ(n) log n = ψ(x) log x − ∫_1^x ψ(t)/t dt`. The integral
is nonnegative and at most `4x` by (`sb:chebyshev-bound`)." With the harmonic logarithm `u_n = F λ_K(n)`,
`x_n = S(Kn)` and `F = L!`:

* `abel_gen`: for every body `a` with `a(0) = 0`, `Σ_{n≤N} a(n) u_n + Σ_{n<N} A(n)(x_{n+1} − x_n) = A(N) u_N`,
  `A(N) = Σ_{n≤N} a(n)` — one closed QF induction (the generic form of `TauAbelIdentity.abel_tau`);
* `pw_exp_le`, `psi_k`, `lam_k`: `ψ(k) ≤ 4kF` and `Λ(k) ≤ 4xF` for `k ≤ x`, `K 2^{4x} ≤ L`;
* `dlt_k`, `i_pt`, `I_le`: `k (x_{k+1} − x_k) ≤ F`, hence the "integral" `I(N) = Σ_{k<N} ψ(k)(x_{k+1} − x_k) ≤ 4F²N`;
* `lw_u_lo`, `lw_u_hi`, `lam_bridge`: `Σ Λ L_w ≤ Σ Λ u ≤ Σ Λ L_w + 4F²` for `(x+1)⁴ ≤ K`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.ChebyshevAbel

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicChebyshev (S_mono wt psi_le)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicMertens (le_scale)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicMertensLower (delta_le)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicLogSquareSum (U)
open LeanProofs.IPRA.AnalyticNumberTheory.LcmUpto (Psi LamB inst2_LamB pos_of_lt_zero)
open LeanProofs.IPRA.AnalyticNumberTheory.WeightedMangoldt (Lam Lw)
open LeanProofs.IPRA.AnalyticNumberTheory.FactorialLambda (lam_zero)
open LeanProofs.IPRA.AnalyticNumberTheory.WeightBridge (lw_le_u u_le_lw sum_le_add_const)
open LeanProofs.IPRA.AnalyticNumberTheory.SymmetryInstances (bs_shift)
open LeanProofs.IPRA.AnalyticNumberTheory.SymmetryPointwise (le_succ' quo_mul_le)
open LeanProofs.IPRA.AnalyticNumberTheory.FourthRootSum (Q4)
open LeanProofs.IPRA.AnalyticNumberTheory.ComparisonEnvelope (le_mul2)
open LeanProofs.IPRA.AnalyticNumberTheory.ConvSummatory (bS inst2_bS Bs)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (pw_pos')
open LeanProofs.IPRA.AnalyticNumberTheory.ChebyshevBounds (two_pos')
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (zero_mul_l)
open LeanProofs.IPRA.AnalyticNumberTheory.DivisorHarmonic (shift_fact')
open LeanProofs.IPRA.Foundations.AuxiliaryEnvelope (sum_le_const)
open LeanProofs.IPRA.Analysis.Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The generic Abel identity -/

section Abel

variable (a : PTm 2)

/-- `a(k, z) u_k`, `z = (K, F)`. -/
def auB : PTm 2 := a * monus (S (fstT (var 1) * var 0) (sndT (var 1))) (S (fstT (var 1)) (sndT (var 1)))

/-- `A(k) (x_{k+1} − x_k)`, `A(k) = Σ_{j≤k} a(j, z)`. -/
def adB : PTm 2 := ap2 (sumF a) (succ (var 0)) (var 1) *
  monus (S (fstT (var 1) * succ (var 0)) (sndT (var 1))) (S (fstT (var 1) * var 0) (sndT (var 1)))

theorem inst2_auB (k z : PTm n) : inst2 (auB a) k z =
    inst2 a k z * monus (S (fstT z * k) (sndT z)) (S (fstT z) (sndT z)) := by
  simp [inst2, auB]

theorem inst2_adB (k z : PTm n) : inst2 (adB a) k z =
    ap2 (sumF a) (succ k) z * monus (S (fstT z * succ k) (sndT z)) (S (fstT z * k) (sndT z)) := by
  simp [inst2, adB]

theorem auB_at (k K F : PTm n) :
    Γ ⊢[PRAAx] inst2 (auB a) k (pairT K F) ≐ inst2 a k (pairT K F) * U k K F := by
  rw [inst2_auB]
  exact congrMul (.eqRefl _) (congrMonus (congrAp2 (sumF hB) (congrMul (fst_pair _ _) (.eqRefl _)) (snd_pair _ _))
    (congrAp2 (sumF hB) (fst_pair _ _) (snd_pair _ _)))

theorem adB_at (k K F : PTm n) :
    Γ ⊢[PRAAx] inst2 (adB a) k (pairT K F) ≐
      ap2 (sumF a) (succ k) (pairT K F) * monus (S (K * succ k) F) (S (K * k) F) := by
  rw [inst2_adB]
  exact congrMul (.eqRefl _) (congrMonus (congrAp2 (sumF hB) (congrMul (fst_pair _ _) (.eqRefl _)) (snd_pair _ _))
    (congrAp2 (sumF hB) (congrMul (fst_pair _ _) (.eqRefl _)) (snd_pair _ _)))

/-- `Σ_{n≤N} a(n) u_n + Σ_{n<N} A(n)(x_{n+1} − x_n) = A(N) u_N`. -/
abbrev Ab (N K F : PTm n) : Fm PTm n :=
  ap2 (sumF (auB a)) (succ N) (pairT K F) + ap2 (sumF (adB a)) N (pairT K F) ≐
    ap2 (sumF a) (succ N) (pairT K F) * U N K F

theorem U_zero (K F : PTm n) : Γ ⊢[PRAAx] U zero K F ≐ zero :=
  (congrMonus ((congrAp2 (sumF hB) (mul_zero K) (.eqRefl F)).eqTrans (sum_zero _ _)) (.eqRefl _)).eqTrans
    (zero_monus _)

theorem ab_zero (K F : PTm n) : Γ ⊢[PRAAx] Ab a zero K F := by
  ipra_lc natEq (sum_succ' (Γ := Γ) (auB a) zero (pairT K F)) + natEq (sum_zero (Γ := Γ) (auB a) (pairT K F)) +
    natEq ((auB_at (Γ := Γ) a zero K F).eqTrans ((congrMul (.eqRefl _) (U_zero K F)).eqTrans (mul_zero _))) +
    natEq (sum_zero (Γ := Γ) (adB a) (pairT K F)) -
    𝔞 (ap2 (sumF a) (succ zero) (pairT K F)) * natEq (U_zero (Γ := Γ) K F)

theorem ab_step {N K F : PTm n} (h0 : Γ ⊢[PRAAx] inst2 a zero (pairT K F) ≐ zero) (ih : Γ ⊢[PRAAx] Ab a N K F) :
    Γ ⊢[PRAAx] Ab a (succ N) K F := by
  have d := natEq (sum_succ' (Γ := Γ) (adB a) N (pairT K F))
  have key : Γ ⊢[PRAAx] ap2 (sumF a) (succ N) (pairT K F) * (U N K F + monus (S (K * succ N) F) (S (K * N) F)) ≐
      ap2 (sumF a) (succ N) (pairT K F) * U (succ N) K F := by
    refine .orE (zero_or_succ N) ?_ ?_
    · let C : List (Fm PTm n) := (N ≐ zero) :: Γ
      have hN : C ⊢[PRAAx] N ≐ zero := Prf.hyp0
      have a0 : C ⊢[PRAAx] ap2 (sumF a) (succ N) (pairT K F) ≐ zero :=
        (sum_succ' _ _ _).eqTrans ((congrAdd ((congrAp2 _ hN (.eqRefl _)).eqTrans (sum_zero _ _))
          ((congrInst2 a hN (.eqRefl _)).eqTrans h0.wk)).eqTrans (add_zero _))
      exact (zero_mul_l a0 _).eqTrans (zero_mul_l a0 _).eqSymm
    · let C : List (Fm PTm n) := (N ≐ succ (pred N)) :: Γ
      have hN : C ⊢[PRAAx] N ≐ succ (pred N) := Prf.hyp0
      have wN := natEq hN
      have m1 : C ⊢[PRAAx] le (S K F) (S (K * N) F) :=
        S_mono F (le_of_eq_add (d := K * pred N) (by apply deriveNat; ipra_simps; linear_combination 𝔞 K * wN))
      have m2 : C ⊢[PRAAx] le (S K F) (S (K * succ N) F) :=
        S_mono F (le_of_eq_add (d := K * N) (by ipra_ring))
      have m3 : C ⊢[PRAAx] le (S (K * N) F) (S (K * succ N) F) :=
        S_mono F (le_of_eq_add (d := K) (by ipra_ring))
      ipra_lc 𝔞 (ap2 (sumF a) (succ N) (pairT K F)) * (natEq (eq_add_of_le m2) - natEq (eq_add_of_le m1) - natEq (eq_add_of_le m3))
  ipra_lc natEq (sum_succ' (Γ := Γ) (auB a) (succ N) (pairT K F)) + natEq (auB_at (Γ := Γ) a (succ N) K F) + d +
    natEq (adB_at (Γ := Γ) a N K F) + natEq ih + natEq key -
    𝔞 (U (succ N) K F) * natEq (sum_succ' (Γ := Γ) a (succ N) (pairT K F))

/-- Variables `0 = N`, `1 = K`, `2 = F`. -/
private abbrev abF : Fm PTm 3 :=
  (inst2 a zero (pairT (var 1) (var 2)) ≐ zero) ⟶ Ab a (var 0) (var 1) (var 2)

private theorem ab₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] abF a := by
  refine ind _ ⟨trivial, trivial⟩ ?_ ?_
  · simp only [Fm.subst_imp, Fm.subst_eq, subst_ap2, subst_pairT, subst_inst2, PTm.subst_add, PTm.subst_mul,
      PTm.subst_monus, Syn.subst_var, Syn.inst_zero, Syn.inst_one, inst_two, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ]
    exact .impI (ab_zero a _ _)
  · simp only [Fm.subst_imp, Fm.subst_eq, subst_ap2, subst_pairT, subst_inst2, PTm.subst_add, PTm.subst_mul,
      PTm.subst_monus, Syn.subst_var, Syn.repl_zero, repl_one, repl_two, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ]
    exact .impI (ab_step a Prf.hyp0 (Prf.impE Prf.hyp1 Prf.hyp0))

/-- The finite partial summation for any `a` with `a(0) = 0`. -/
theorem abel_gen (N K F : PTm n) (h0 : Γ ⊢[PRAAx] inst2 a zero (pairT K F) ≐ zero) : Γ ⊢[PRAAx] Ab a N K F := by
  have i := inst (Γ := Γ) (ab₀ a) (![N, K, F] : Fin 3 → PTm n)
  simp at i
  exact Prf.impE i h0

end Abel

/-! ## `ψ(k) ≤ 4kF` and the integral -/

theorem lam0 (K F : PTm n) : Γ ⊢[PRAAx] inst2 (LamB wt) zero (pairT K F) ≐ zero := by
  rw [inst2_LamB]; exact lam_zero wt _

/-- `2^a ≤ 2^b` for `a ≤ b`. -/
theorem pw_exp_le {a b : PTm n} (h : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx] le (pw two a) (pw two b) := by
  have e := eq_add_of_le h
  have pb : Γ ⊢[PRAAx] pw two b ≐ pw two a * pw two (monus b a) :=
    (congrAp2 powF e (.eqRefl two)).eqTrans (pw_add two a _)
  have pd := natEq (pw_pos' (Γ := Γ) two_pos' (monus b a))
  have f := natEq pb
  ipra_le 𝔞 (pw two a) * 𝔞 (pred (pw two (monus b a))) with f + 𝔞 (pw two a) * pd

section Cheb
variable {x K L : PTm n} (hK : Γ ⊢[PRAAx] le one K) (hP : Γ ⊢[PRAAx] le (K * pw two (two * (two * x))) L)
include hK hP

/-- `ψ(k) ≤ 4kF` for `k ≤ x`. -/
theorem psi_k {k : PTm n} (hkx : Γ ⊢[PRAAx] le k x) :
    Γ ⊢[PRAAx] le (Psi wt k (pairT K (fact L))) (two * (two * k) * fact L) :=
  psi_le hK (le_trans (le_scale K (pw_exp_le (le_scale two (le_scale two hkx)))) hP)

/-- `Λ(k) ≤ 4xF` for `k ≤ x`. -/
theorem lam_k {k : PTm n} (hkx : Γ ⊢[PRAAx] le k x) :
    Γ ⊢[PRAAx] le (Lam wt k (pairT K (fact L))) (two * (two * x) * fact L) := by
  have p := psi_k hK hP hkx
  have q := mul_le_mul_right (fact L) (le_scale two (le_scale two hkx))
  have s := sum_succ' (Γ := Γ) (LamB wt) k (pairT K (fact L))
  rw [inst2_LamB] at s
  have e := natEq s
  ipra_le sl p + sl q + 𝔞 (ap2 (sumF (LamB wt)) k (pairT K (fact L))) with e

omit hP in
/-- `k (x_{k+1} − x_k) ≤ F`. -/
theorem dlt_k (k F : PTm n) : Γ ⊢[PRAAx] le (k * monus (S (K * succ k) F) (S (K * k) F)) F := by
  have dl := delta_le (Γ := Γ) k F (pos_of_lt_zero hK)
  have m : Γ ⊢[PRAAx] le (S (K * k) F) (S (K * succ k) F) :=
    S_mono F (le_of_eq_add (d := K) (by ipra_ring))
  have e := natEq (eq_add_of_le m)
  ipra_le sl dl with 𝔞 k * e

/-- `ψ(k)(x_{k+1} − x_k) ≤ 4F²`. -/
theorem i_pt {k : PTm n} (hkx : Γ ⊢[PRAAx] le k x) :
    Γ ⊢[PRAAx] le (inst2 (adB (LamB wt)) k (pairT K (fact L))) (two * (two * (fact L * fact L))) := by
  refine le_congr (adB_at _ _ _ _).eqSymm (.eqRefl _) ?_
  have p := mul_le_mul_right (monus (S (K * succ k) (fact L)) (S (K * k) (fact L))) (psi_k hK hP hkx)
  have q := le_scale (two * (two * fact L)) (dlt_k hK k (fact L))
  ipra_le sl p + sl q

/-- `I(N) = Σ_{k<N} ψ(k)(x_{k+1} − x_k) ≤ 4F² N` for `N ≤ x`. -/
theorem I_le {N : PTm n} (hNx : Γ ⊢[PRAAx] le N x) :
    Γ ⊢[PRAAx] le (ap2 (sumF (adB (LamB wt))) N (pairT K (fact L))) (N * (two * (two * (fact L * fact L)))) := by
  have hK' : (Γ.map Fm.shift) ⊢[PRAAx] le one (Syn.shift K) := by simpa [Fm.shift, Syn.shift] using hK.shift
  have hP' : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift K * pw two (two * (two * Syn.shift x))) (Syn.shift L) := by
    simpa [Fm.shift, Syn.shift] using hP.shift
  have hN' : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift N) (Syn.shift x) := by simpa [Fm.shift, Syn.shift] using hNx.shift
  refine sum_le_const _ (.allI (.impI ?_))
  rw [shift_pairT, shift_fact', show Syn.shift (two * (two * (fact L * fact L)) : PTm n) =
    two * (two * (fact (Syn.shift L) * fact (Syn.shift L))) by simp [Syn.shift]]
  have hv : (lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) ⊢[PRAAx] le (var 0) (Syn.shift x) :=
    le_trans (le_trans (le_succ_self _) Prf.hyp0) hN'.wk
  exact i_pt hK'.wk hP'.wk hv

end Cheb

/-! ## `Σ Λ L_w` against `Σ Λ u` -/

/-- `Λ_w(k) L_w(k)`. -/
abbrev lwB : PTm 2 := LamB wt * Lw wt (var 0) (var 1)

theorem inst2_lwB (k y : PTm n) : inst2 lwB k y = Lam wt k y * Lw wt k y := by simp [inst2]

theorem lw0 (y : PTm n) : Γ ⊢[PRAAx] inst2 lwB zero y ≐ zero := by
  rw [inst2_lwB]; exact zero_mul_l (lam_zero wt _) _

/-- `Σ_{n≤x} Λ(n) L_w(n) ≤ Σ_{n≤x} Λ(n) u_n` for `K ≥ 1`, `Kx ≤ L`. -/
theorem lw_u_lo {x K L : PTm n} (hK : Γ ⊢[PRAAx] le one K) (hKx : Γ ⊢[PRAAx] le (K * x) L) :
    Γ ⊢[PRAAx] le (ap2 (sumF lwB) (succ x) (pairT K (fact L)))
      (ap2 (sumF (auB (LamB wt))) (succ x) (pairT K (fact L))) := by
  have hK' : (Γ.map Fm.shift) ⊢[PRAAx] le one (Syn.shift K) := by simpa [Fm.shift, Syn.shift] using hK.shift
  have hKx' : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift K * Syn.shift x) (Syn.shift L) := by
    simpa [Fm.shift, Syn.shift] using hKx.shift
  have s := sum_le_params (Γ := Γ) (bS lwB) (bS (auB (LamB wt))) (pairT K (fact L)) (pairT K (fact L)) x
    (.allI (.impI (by
      rw [shift_pairT, shift_fact', inst2_bS, inst2_bS, inst2_lwB]
      refine le_congr (.eqRefl _) (auB_at _ _ _ _).eqSymm ?_
      rw [inst2_LamB]
      exact le_scale _ (lw_le_u hK'.wk
        (le_trans (le_scale _ (Prf.hyp0 : (lt (var 0) (Syn.shift x) :: Γ.map Fm.shift) ⊢[PRAAx] _)) hKx'.wk)))))
  have b1 := natEq (bs_shift (Γ := Γ) lwB x (pairT K (fact L)))
  have b2 := natEq (bs_shift (Γ := Γ) (auB (LamB wt)) x (pairT K (fact L)))
  have z1 := natEq (lw0 (Γ := Γ) (pairT K (fact L)))
  have z2 := natEq ((auB_at (Γ := Γ) (LamB wt) zero K (fact L)).eqTrans (zero_mul_l (lam0 K (fact L)) _))
  ipra_le sl s with b2 + z2 - b1 - z1

/-- `Σ_{n≤x} Λ(n) u_n ≤ Σ_{n≤x} Λ(n) L_w(n) + x · 4xF · x ⌊F/K⌋`. -/
theorem lw_u_hi {x K L : PTm n} (hK : Γ ⊢[PRAAx] le one K) (hP : Γ ⊢[PRAAx] le (K * pw two (two * (two * x))) L)
    (hKx : Γ ⊢[PRAAx] le (K * x) L) :
    Γ ⊢[PRAAx] le (ap2 (sumF (auB (LamB wt))) (succ x) (pairT K (fact L)))
      (ap2 (sumF lwB) (succ x) (pairT K (fact L)) + x * (two * (two * x) * fact L * (x * quo (fact L) K))) := by
  have hK' : (Γ.map Fm.shift) ⊢[PRAAx] le one (Syn.shift K) := by simpa [Fm.shift, Syn.shift] using hK.shift
  have hP' : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift K * pw two (two * (two * Syn.shift x))) (Syn.shift L) := by
    simpa [Fm.shift, Syn.shift] using hP.shift
  have hKx' : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift K * Syn.shift x) (Syn.shift L) := by
    simpa [Fm.shift, Syn.shift] using hKx.shift
  have s := sum_le_add_const (Γ := Γ) (bS (auB (LamB wt))) (bS lwB) (x := pairT K (fact L)) (y := pairT K (fact L))
    (c := two * (two * x) * fact L * (x * quo (fact L) K)) (N := x) (.allI (.impI (by
      rw [shift_pairT, shift_fact', inst2_bS, inst2_bS, inst2_lwB,
        show Syn.shift (two * (two * x) * fact L * (x * quo (fact L) K)) =
          two * (two * Syn.shift x) * fact (Syn.shift L) * (Syn.shift x * quo (fact (Syn.shift L)) (Syn.shift K)) by
          simp [Syn.shift]]
      refine le_congr (auB_at _ _ _ _).eqSymm (.eqRefl _) ?_
      rw [inst2_LamB]
      let C := (lt (var 0) (Syn.shift x) :: Γ.map Fm.shift)
      have hv : C ⊢[PRAAx] le (succ (var 0)) (Syn.shift x) := Prf.hyp0
      have ul := u_le_lw hK'.wk (le_trans (le_scale _ hv) hKx'.wk)
      have lk := lam_k hK'.wk hP'.wk hv
      have p1 := le_scale (Lam wt (succ (var 0)) (pairT (Syn.shift K) (fact (Syn.shift L)))) ul
      have p2 := le_mul2 lk (mul_le_mul_right (quo (fact (Syn.shift L)) (Syn.shift K)) hv)
      ipra_le sl p1 + sl p2)))
  have b1 := natEq (bs_shift (Γ := Γ) lwB x (pairT K (fact L)))
  have b2 := natEq (bs_shift (Γ := Γ) (auB (LamB wt)) x (pairT K (fact L)))
  have z1 := natEq (lw0 (Γ := Γ) (pairT K (fact L)))
  have z2 := natEq ((auB_at (Γ := Γ) (LamB wt) zero K (fact L)).eqTrans (zero_mul_l (lam0 K (fact L)) _))
  ipra_le sl s with b2 + z2 - b1 - z1

/-- `x³ ≤ (x+1)⁴`. -/
theorem cube_le_Q4' (x : PTm n) : Γ ⊢[PRAAx] le (x * (x * x)) (Q4 x) := by
  ipra_le 𝔞 x * 𝔞 x * 𝔞 x * 𝔞 x + 3 * (𝔞 x * 𝔞 x * 𝔞 x) + 6 * (𝔞 x * 𝔞 x) + 4 * 𝔞 x + 1

/-- `Σ Λ L_w ≤ Σ Λ u ≤ Σ Λ L_w + 4F²` for `K ≥ 1`, `(x+1)⁴ ≤ K`, `K 2^{4x} ≤ L`, `Kx ≤ L`. -/
theorem lam_bridge {x K L : PTm n} (hK : Γ ⊢[PRAAx] le one K) (hx4 : Γ ⊢[PRAAx] le (Q4 x) K)
    (hP : Γ ⊢[PRAAx] le (K * pw two (two * (two * x))) L) (hKx : Γ ⊢[PRAAx] le (K * x) L) :
    Γ ⊢[PRAAx] le (ap2 (sumF lwB) (succ x) (pairT K (fact L)))
        (ap2 (sumF (auB (LamB wt))) (succ x) (pairT K (fact L))) ⋏
      le (ap2 (sumF (auB (LamB wt))) (succ x) (pairT K (fact L)))
        (ap2 (sumF lwB) (succ x) (pairT K (fact L)) + two * (two * (fact L * fact L))) := by
  refine .andI (lw_u_lo hK hKx) ?_
  have h := lw_u_hi hK hP hKx
  have c := mul_le_mul_right (quo (fact L) K) (le_trans (cube_le_Q4' x) hx4)
  have r := quo_mul_le (Γ := Γ) (x := fact L) (pos_of_lt_zero hK)
  have q := le_scale (two * (two * fact L)) (le_trans c (le_congr (mul_comm _ _) (.eqRefl _) r))
  ipra_le sl h + sl q

end LeanProofs.IPRA.AnalyticNumberTheory.ChebyshevAbel
