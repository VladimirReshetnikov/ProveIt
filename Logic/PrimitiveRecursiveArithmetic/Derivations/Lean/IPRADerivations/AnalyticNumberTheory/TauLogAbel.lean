import IPRADerivations.AnalyticNumberTheory.DivisorBound
import IPRADerivations.AnalyticNumberTheory.HarmonicLogSquareSum

/-!
# The divisor–logarithm sum by finite partial summation (`pnt_ipra_constructive_2026-11-14`, `sb:divisor-approx`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `selberg.tex`, proof of Lemma
`sb:divisor-approx`: "For `T(y) = Σ_{n≤y} τ(n) log n`, finite partial summation gives
`T(y) = D(y) log y − ∫_1^y D(t)/t dt`. Write `D(t) = t log t + (2c − 1)t + E(t)` … Substitution and elementary
integration yield `T(y) = y((log y)² + (2c − 2) log y + 2 − 2c) + E_T(y)`."

With the packet's rational logarithm `λ_K`, `F = L!`, `x_N = S(KN)`, `u_N = F λ_K(N) = x_N ∸ S(K)`, the finite
`c = H_X − λ_K(X)` (`F c = C = (S(X) + S(K)) ∸ S(KX)`), and the Abel sum

  `A(N) = Σ_{n<N} D(n) (x_{n+1} − x_n)`   (so that `F T(N) = D(N) u_N − A(N)` exactly),

this module proves the "elementary integration" step as two invariants, for `1 ≤ N ≤ N₀ ≤ min(X, K)`:

* upper (`IU`): `F A(N) ≤ Φ(N) + 2F S(N) + 8 m_N F u_N`;
* lower (`IL`): `Φ(N) ≤ F A(N) + F u_N + (u_N + 2C) S(N) + 11 m_N F u_N`,

where `Φ(N) = F[N u_N − N F + (2C − F) N]` and `m_N = ⌊√N⌋`. The step uses `DivisorBound.divisor_upper` and
`divisor_lower` at `y = N` (times `x_{N+1} − x_N`), `HarmonicLogSum.inc_lower` and
`HarmonicMertensLower.delta_le`; the certificates were found by exact polynomial residuals and are
re-checked by the kernel.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.TauLogAbel

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB inst2_h)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicLogSquareSum (S_succ U delta_paired)
open LeanProofs.IPRA.AnalyticNumberTheory.DivisorBound (eta_bounds divisor_upper divisor_lower)
open LeanProofs.IPRA.Analysis.Products (fact)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## The Abel sum -/

/-- `D(k) (x_{k+1} − x_k)` with parameter `z = (K, F)`. -/
abbrev AB : PTm 2 :=
  S (var 0) (var 0) * monus (S (fstT (var 1) * succ (var 0)) (sndT (var 1))) (S (fstT (var 1) * var 0) (sndT (var 1)))

theorem inst2_AB (k z : PTm n) : inst2 AB k z =
    S k k * monus (S (fstT z * succ k) (sndT z)) (S (fstT z * k) (sndT z)) := by simp [inst2]

abbrev As (N K F : PTm n) : PTm n := ap2 (sumF AB) N (pairT K F)

theorem A_succ (N K F : PTm n) :
    Γ ⊢[PRAAx] As (succ N) K F ≐ As N K F + S N N * monus (S (K * succ N) F) (S (K * N) F) := by
  refine (sum_succ' AB N (pairT K F)).eqTrans (congrAdd (.eqRefl _) ?_)
  rw [inst2_AB]
  exact congrMul (.eqRefl _) (delta_paired N K F)

/-- `F c = C = (S(X) + S(K)) ∸ S(KX)`. -/
abbrev CT (K X F : PTm n) : PTm n := monus (S X F + S K F) (S (K * X) F)

theorem quo_one' (F : PTm n) : Γ ⊢[PRAAx] quo F (succ zero) ≐ F :=
  quo_eq (congrSucc (pred_succ _).eqSymm) (q := F) (r := zero) (by ipra_ring) (le_refl _)

/-- `0 ≤ c`: `S(KX) ≤ S(X) + S(K)` for `K, X ≥ 1`, `KX ≤ L` (`eta_bounds` at `m = 1`). -/
theorem c_nonneg {K X L : PTm n} (hK : Γ ⊢[PRAAx] le one K) (hX : Γ ⊢[PRAAx] le one X)
    (hL : Γ ⊢[PRAAx] le (K * X) L) :
    Γ ⊢[PRAAx] le (S (K * X) (fact L)) (S X (fact L) + S K (fact L)) := by
  have c2 := Prf.andE₂ (eta_bounds (m := one) (le_refl _) hX hK hL)
  have q1 : Γ ⊢[PRAAx] K * one ≐ K := by ipra_ring
  have eK1 := natEq (congrAp2 (Γ := Γ) (sumF hB) q1 (.eqRefl (fact L)))
  have eSs := natEq (S_succ (Γ := Γ) zero (fact L))
  have eS0 := natEq (sum_zero (Γ := Γ) hB (fact L))
  ipra_le sl c2 with eK1 - eSs - eS0

/-! ## The invariants -/

/-- `m_N F u_N` at `N = k + 1`. -/
abbrev Tm (k K L : PTm n) : PTm n := isqrt (succ k) * (fact L * U (succ k) K (fact L))

abbrev IU (k K L X : PTm n) : Fm PTm n :=
  le (fact L * As (succ k) K (fact L) + two * (succ k * (fact L * S (K * X) (fact L))) +
        two * (succ k * (fact L * fact L)))
    (fact L * (succ k * S (K * succ k) (fact L)) + fact L * (succ k * S K (fact L)) +
        two * (fact L * (succ k * S X (fact L))) + two * (fact L * S (succ k) (fact L)) +
        two * (two * (two * Tm k K L)))

abbrev IL (k K L X : PTm n) : Fm PTm n :=
  le (fact L * (succ k * S (K * succ k) (fact L)) + fact L * (succ k * S K (fact L)) +
        two * (fact L * (succ k * S X (fact L))))
    (fact L * As (succ k) K (fact L) + two * (succ k * (fact L * S (K * X) (fact L))) +
        two * (succ k * (fact L * fact L)) + fact L * U (succ k) K (fact L) +
        (U (succ k) K (fact L) + two * CT K X (fact L)) * S (succ k) (fact L) +
        (two * (two * (two * Tm k K L)) + two * Tm k K L + Tm k K L))

abbrev Ht (k K L X N0 : PTm n) : Fm PTm n :=
  le one K ⋏ (le (K * X) L ⋏ (le N0 X ⋏ (le N0 K ⋏ le (succ k) N0)))

theorem i_zero {K L X N0 : PTm n} (h : Γ ⊢[PRAAx] Ht zero K L X N0) : Γ ⊢[PRAAx] IU zero K L X ⋏ IL zero K L X := by
  have hK := Prf.andE₁ h
  have hL := Prf.andE₁ (Prf.andE₂ h)
  have hN0X := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ h))
  have h1 := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h)))
  have hX : Γ ⊢[PRAAx] le one X := le_trans h1 hN0X
  have eA1 := natEq (A_succ (Γ := Γ) zero K (fact L))
  have eA0 := natEq (sum_zero (Γ := Γ) AB (pairT K (fact L)))
  have eD0 := natEq (sum_zero (Γ := Γ) hB (zero : PTm n))
  have q1 : Γ ⊢[PRAAx] K * succ zero ≐ K := by ipra_ring
  have ex1 := natEq (congrAp2 (Γ := Γ) (sumF hB) q1 (.eqRefl (fact L)))
  have eu1 := natEq ((congrMonus (congrAp2 (sumF hB) q1 (.eqRefl (fact L))) (.eqRefl _)).eqTrans
    (le_refl (S K (fact L))) : Γ ⊢[PRAAx] U (succ zero) K (fact L) ≐ zero)
  have eSs := natEq (S_succ (Γ := Γ) zero (fact L))
  have eS0 := natEq (sum_zero (Γ := Γ) hB (fact L))
  have eq1 := natEq (quo_one' (Γ := Γ) (fact L))
  have eC := natEq (eq_add_of_le (c_nonneg hK hX hL))
  refine .andI ?_ ?_
  · ipra_le 2 * 𝔞 (fact L) * 𝔞 (CT K X (fact L)) with
      𝔞 (fact L) * eA1 + 𝔞 (fact L) * eA0 +
        𝔞 (fact L) * 𝔞 (monus (S (K * succ zero) (fact L)) (S (K * zero) (fact L))) * eD0 -
        𝔞 (fact L) * ex1 - 8 * 𝔞 (fact L) * 𝔞 (isqrt (succ zero)) * eu1 -
        2 * 𝔞 (fact L) * (eSs + eS0 + eq1) - 2 * 𝔞 (fact L) * eC
  · ipra_le 2 * 𝔞 (fact L) * 𝔞 (fact L) with
      -(𝔞 (fact L)) * eA1 - 𝔞 (fact L) * eA0 -
        𝔞 (fact L) * 𝔞 (monus (S (K * succ zero) (fact L)) (S (K * zero) (fact L))) * eD0 +
        𝔞 (fact L) * ex1 +
        (-(11 * 𝔞 (fact L) * 𝔞 (isqrt (succ zero))) - 𝔞 (fact L) - 𝔞 (S (succ zero) (fact L))) * eu1 -
        2 * 𝔞 (CT K X (fact L)) * (eSs + eS0 + eq1) + 2 * 𝔞 (fact L) * eC

/-- `1 ≤ ⌊√(k+1)⌋`. -/
theorem isqrt_pos (k : PTm n) : Γ ⊢[PRAAx] le one (isqrt (succ k)) := by
  refine .orE (lt_or_le zero (isqrt (succ k))) Prf.hyp0 ?_
  have m0 : (le (isqrt (succ k)) zero :: Γ) ⊢[PRAAx] isqrt (succ k) ≐ zero := le_antisymm Prf.hyp0 (zero_le _)
  have sp := lt_isqrt_succ_sq (Γ := le (isqrt (succ k)) zero :: Γ) (succ k)
  have e : (le (isqrt (succ k)) zero :: Γ) ⊢[PRAAx] (isqrt (succ k) + one) * (isqrt (succ k) + one) ≐ one := by
    ipra_lc (𝔞 (isqrt (succ k)) + 2) * natEq m0
  have c : (le (isqrt (succ k)) zero :: Γ) ⊢[PRAAx] le (succ (succ k)) (succ zero) := le_congr (.eqRefl _) e sp
  have c' : (le (isqrt (succ k)) zero :: Γ) ⊢[PRAAx] le (succ zero) zero :=
    le_trans (le_of_eq_add (d := k) (by ipra_ring) : (le (isqrt (succ k)) zero :: Γ) ⊢[PRAAx] le (succ zero) (succ k))
      ((succ_monus_succ _ _).eqSymm.eqTrans c)
  exact not_succ_le_self zero _ c'

theorem i_step {k K L X N0 : PTm n} (h : Γ ⊢[PRAAx] Ht (succ k) K L X N0)
    (ih : Γ ⊢[PRAAx] IU k K L X ⋏ IL k K L X) : Γ ⊢[PRAAx] IU (succ k) K L X ⋏ IL (succ k) K L X := by
  have hK := Prf.andE₁ h
  have hL := Prf.andE₁ (Prf.andE₂ h)
  have hN0X := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ h))
  have hN0K := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h)))
  have hk := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h)))
  have hKp := pos_of_lt_zero hK
  have hy1 : Γ ⊢[PRAAx] le (succ k) N0 := le_trans (le_succ_self _) hk
  have hyX := le_trans hy1 hN0X
  have hyK := le_trans hy1 hN0K
  have hX : Γ ⊢[PRAAx] le one X :=
    le_trans (le_of_eq_add (d := k) (by ipra_ring) : Γ ⊢[PRAAx] le one (succ k)) hyX
  -- the divisor bound at `y = k + 1`
  have hm1 := isqrt_pos (Γ := Γ) k
  have h1 := isqrt_le (Γ := Γ) (succ k)
  have hm2 : Γ ⊢[PRAAx] lt (succ k) (succ (isqrt (succ k)) * succ (isqrt (succ k))) :=
    le_congr (.eqRefl _) (by ipra_ring) (lt_isqrt_succ_sq (succ k))
  have hmy : Γ ⊢[PRAAx] le (isqrt (succ k)) (succ k) := by
    have t := le_scale (isqrt (succ k)) hm1
    exact le_trans (by ipra_le sl t) h1
  have hmX := le_trans hmy hyX
  have hXL : Γ ⊢[PRAAx] le X L := le_trans (by have t := le_scale X hK; ipra_le sl t) hL
  have hmL := le_trans hmX hXL
  have hLy := le_trans (le_scale K hyX) hL
  have dU := divisor_upper hm1 h1 hm2 hmX hK hL hLy hmL
  have dL := divisor_lower hm1 h1 hm2 hmX hK hyK hL hLy hmL
  -- increments
  have hKL2 : Γ ⊢[PRAAx] le (K * succ (succ k)) L := le_trans (le_scale K (le_trans hk hN0X)) hL
  have hNL : Γ ⊢[PRAAx] le (succ (succ k)) L := by
    refine le_trans (le_of_eq_add (d := pred K * succ (succ k)) ?_) hKL2
    ipra_lc (𝔞 k + 2) * natEq hKp
  have inc := inc_lower hKp hKL2
  have dl := delta_le (Γ := Γ) (succ k) (fact L) hKp
  have mm : Γ ⊢[PRAAx] le (isqrt (succ k)) (isqrt (succ (succ k))) :=
    le_of_eq_add (isqrt_succ (succ k))
  have m1x : Γ ⊢[PRAAx] le (S K (fact L)) (S (K * succ k) (fact L)) :=
    S_mono (fact L) (le_of_eq_add (d := K * k) (by ipra_ring))
  have m2x : Γ ⊢[PRAAx] le (S K (fact L)) (S (K * succ (succ k)) (fact L)) :=
    S_mono (fact L) (le_of_eq_add (d := K * succ k) (by ipra_ring))
  have m3 : Γ ⊢[PRAAx] le (S (K * succ k) (fact L)) (S (K * succ (succ k)) (fact L)) :=
    S_mono (fact L) (le_of_eq_add (d := K) (by ipra_ring))
  have Eu := natEq (eq_add_of_le m1x)
  have Eup := natEq (eq_add_of_le m2x)
  have Ed := natEq (eq_add_of_le m3)
  have EC := natEq (eq_add_of_le (c_nonneg hK hX hL))
  have EA := natEq (A_succ (Γ := Γ) (succ k) K (fact L))
  have ES := natEq (S_succ (Γ := Γ) (succ k) (fact L))
  have EF := natEq (fact_quo hNL)
  -- scaled facts
  have a1 := le_scale (monus (S (K * succ (succ k)) (fact L)) (S (K * succ k) (fact L))) dU
  have a2 := le_scale (U (succ k) K (fact L) + two * CT K X (fact L)) dl
  have a3 := le_scale (two * (fact L * succ k)) inc
  have a4 := le_scale (fact L * U (succ (succ k)) K (fact L)) mm
  have b1 := le_scale (monus (S (K * succ (succ k)) (fact L)) (S (K * succ k) (fact L))) dL
  have b2 := le_scale (two * fact L) dl
  have b3 := le_scale (succ k * (U (succ k) K (fact L) + two * CT K X (fact L))) inc
  refine .andI ?_ ?_
  · ipra_le sl (Prf.andE₁ ih) + sl a1 + sl a2 + sl a3 +
        𝔞 (fact L) * 𝔞 (monus (S (K * succ (succ k)) (fact L)) (S (K * succ k) (fact L))) + 8 * sl a4 with
      8 * 𝔞 (fact L) * 𝔞 (isqrt (succ k)) * Eup +
      (-2 * 𝔞 (CT K X (fact L)) * (𝔞 k + 1) + 𝔞 (fact L) * (𝔞 k + 1) -
          8 * 𝔞 (fact L) * 𝔞 (isqrt (succ k)) - 𝔞 (fact L) - (𝔞 k + 1) * 𝔞 (U (succ k) K (fact L))) * Ed +
      (-8 * 𝔞 (fact L) * 𝔞 (isqrt (succ k)) - 𝔞 (fact L) +
          (𝔞 k + 1) * 𝔞 (monus (S (K * succ (succ k)) (fact L)) (S (K * succ k) (fact L)))) * Eu +
      𝔞 (fact L) * EA - 2 * 𝔞 (fact L) * ES -
      2 * (𝔞 (fact L) - (𝔞 k + 1) * 𝔞 (monus (S (K * succ (succ k)) (fact L)) (S (K * succ k) (fact L)))) * EC +
      2 * 𝔞 (fact L) * EF
  · ipra_le sl (Prf.andE₂ ih) + sl b1 + sl b2 + sl b3 +
        𝔞 (monus (S (K * succ (succ k)) (fact L)) (S (K * succ k) (fact L))) * 𝔞 (S (succ k) (fact L)) +
        𝔞 (quo (fact L) (succ (succ k))) * 𝔞 (monus (S (K * succ (succ k)) (fact L)) (S (K * succ k) (fact L))) +
        11 * sl a4 with
      (11 * 𝔞 (fact L) * 𝔞 (isqrt (succ k)) + 𝔞 (fact L) + 𝔞 (S (succ (succ k)) (fact L))) * Eup +
      (2 * 𝔞 (CT K X (fact L)) * (𝔞 k + 1) - 𝔞 (fact L) * (𝔞 k + 1) -
          11 * 𝔞 (fact L) * 𝔞 (isqrt (succ k)) + (𝔞 k + 1) * 𝔞 (U (succ k) K (fact L)) -
          𝔞 (S (succ (succ k)) (fact L))) * Ed +
      (-11 * 𝔞 (fact L) * 𝔞 (isqrt (succ k)) -
          (𝔞 k + 1) * 𝔞 (monus (S (K * succ (succ k)) (fact L)) (S (K * succ k) (fact L))) -
          𝔞 (S (succ (succ k)) (fact L))) * Eu -
      𝔞 (fact L) * EA +
      (-2 * 𝔞 (CT K X (fact L)) - 𝔞 (monus (S (K * succ (succ k)) (fact L)) (S (K * succ k) (fact L))) -
          𝔞 (U (succ k) K (fact L))) * ES +
      2 * (𝔞 (fact L) - (𝔞 k + 1) * 𝔞 (monus (S (K * succ (succ k)) (fact L)) (S (K * succ k) (fact L)))) * EC +
      (2 * 𝔞 (CT K X (fact L)) + 𝔞 (U (succ k) K (fact L))) * EF

/-- The finite partial-summation step of `sb:divisor-approx` at `N = k + 1 ≤ min(X, K)`, `K ≥ 1`, `KX ≤ L`. -/
theorem tau_abel {k K L X : PTm n} (hK : Γ ⊢[PRAAx] le one K) (hL : Γ ⊢[PRAAx] le (K * X) L)
    (hX : Γ ⊢[PRAAx] le (succ k) X) (hKk : Γ ⊢[PRAAx] le (succ k) K) :
    Γ ⊢[PRAAx] IU k K L X ⋏ IL k K L X := by
  let I : Fm PTm (n + 1) :=
    IU (var 0) (Syn.shift K) (Syn.shift L) (Syn.shift X) ⋏ IL (var 0) (Syn.shift K) (Syn.shift L) (Syn.shift X)
  have hK' := LeanProofs.IPRA.Order.shift_one_le hK
  have hL' : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift K * Syn.shift X) (Syn.shift L) := by
    simpa [Syn.shift] using LeanProofs.IPRA.Order.shift_le hL
  have hX' := LeanProofs.IPRA.Order.shift_lt (a := k) (b := X) hX
  have hKk' := LeanProofs.IPRA.Order.shift_lt (a := k) (b := K) hKk
  have h : Γ ⊢[PRAAx] I.subst (Syn.inst k) := by
    refine qfIndUpTo k ⟨le_QF _ _, le_QF _ _⟩ ?_ ?_
    · simp [I]
      exact i_zero (N0 := succ k) (.andI hK (.andI hL (.andI hX (.andI hKk
        (LeanProofs.IPRA.Order.succ_le_succ (zero_le k))))))
    · simp [I, subst_repl_shift]
      exact .impI (i_step (N0 := succ (Syn.shift k))
        (.andI hK'.wk.wk (.andI hL'.wk.wk (.andI hX'.wk.wk (.andI hKk'.wk.wk
          (LeanProofs.IPRA.Order.succ_le_succ Prf.hyp0))))) Prf.hyp1)
  simpa [I] using h

end LeanProofs.IPRA.AnalyticNumberTheory.TauLogAbel

export_ipra AnalyticNumberTheory.TauLogAbel (c_nonneg)
