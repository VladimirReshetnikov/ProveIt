import IPRADerivations.Analysis.Integration.Moments.Even.EvenPowerIntegrals
import IPRADerivations.AnalyticNumberTheory.LocalFactor

/-!
# Euler's series for `π` against the Riemann-sum code

Packet: `analysis/cauchy_residue_ipra`, `report.tex`, "A fast rational construction of `π`":
`eq:pigeometric`, `1/(1+t²) = ∑_{j<N} (1−t²)^j/2^{j+1} + ((1−t²)/2)^N/(1+t²)`, and `eq:piapprox`, `eq:pibound`:
with `J_j = ∫_0^1 (1−t²)^j dt` and `p_N = 4 ∑_{j<N} J_j/2^{j+1}`, `p_N ≤ π ≤ p_N + 4 · 2^{−N}`.

Here `π/4` is the Riemann-sum code `Q_M = M ∑_{i<M} 1/(M² + i²)` of `basel_ipra` (`BaselQuadrature.Q`, cleared
by `F = L!`, `2M² ≤ L`), and `J_j = (2j)!!/(2j+1)!!` by `EvenPowerIntegrals`. With `x_i = M² − i²`,
`u_i = F/(M² + i²)`:

* `geo_step` (`eq:pigeometric`, one step): for `R_N = ∑_{i<M} x_i^N u_i`, `R_{N+1} + F P_N = 2M² R_N`, from
  `x u + F = 2M² u`;
* `horner`: `(2M²)^N R_0 = F · Th N + R_N` for the Horner sum `Th N = ∑_{j<N} (2M²)^{N−1−j} P_j`;
  `R_le`: `R_N ≤ M^{2N} R_0`; `Q_eq`: `Q(M) = M R_0`;
* `eu_all`: with `Eu N = 2^{N−1} (2N−1)!! ∑_{j<N} J_j/2^j` (recursion `Eu (N+1) = 2(2N+1) · Eu N + (2N)!!`),
  `|M² · da N · Th N − M^{2N+1} · Eu N| ≤ (3 · 2^N − (2N+3)) · da N · M^{2N}`;
* `euler_pi` (`eq:pibound` with its mesh error): `F M · Eu N ≤ 2^N da N (M Q + 3F)` and
  `2^N da N · M Q ≤ F M · Eu N + 3 · 2^N da N · F + da N · M Q`, i.e.
  `p_N/4 − 3/M ≤ Q_M ≤ p_N/4 + 3/M + Q_M/2^N` with `p_N/4 = Eu N/(2^N (2N−1)!!)`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.EulerPiSeries

open_ipra
open LeanProofs.IPRA.Analysis.BaselQuadrature (uq lift4 inst2_lift4 Qb inst_Qb)
open LeanProofs.IPRA.Analysis.BaselCore (sum_lin)
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open LeanProofs.IPRA.Analysis.WallisGrid (u_eq_le)
open LeanProofs.IPRA.Analysis.WallisFinite (da db bB da_zero db_zero da_succ)
open LeanProofs.IPRA.Analysis.EvenPowerIntegrals
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Analysis.Products (fact)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The remainder sums -/

/-- `x_i^N u_i` over `(i, N, M, L)`. -/
abbrev Rb : PTm 2 := lift4 (pw (monus (var 2 * var 2) (var 0 * var 0)) (var 1) *
  quo (fact (var 3)) (var 2 * var 2 + var 0 * var 0))

/-- `2M² x_i^N u_i` over `(i, N, M, L)`. -/
abbrev KRb : PTm 2 := lift4 (two * (var 2 * var 2) * (pw (monus (var 2 * var 2) (var 0 * var 0)) (var 1) *
  quo (fact (var 3)) (var 2 * var 2 + var 0 * var 0)))

/-- `M^{2N} u_i` over `(i, N, M, L)`. -/
abbrev SRb : PTm 2 := lift4 (pw (var 2 * var 2) (var 1) * quo (fact (var 3)) (var 2 * var 2 + var 0 * var 0))

/-- `R_N = ∑_{i<M} x_i^N u_i`. -/
abbrev Rs (N M L : PTm n) : PTm n := ap2 (sumF Rb) M (pairT N (pairT M L))

theorem inst_Rb (i N M L : PTm n) :
    Γ ⊢[PRAAx] inst2 Rb i (pairT N (pairT M L)) ≐ pw (xs i M) N * uq i M L := by
  have h := inst2_lift4 (Γ := Γ) (pw (monus (var 2 * var 2) (var 0 * var 0)) (var 1) *
    quo (fact (var 3)) (var 2 * var 2 + var 0 * var 0)) i N M L
  simp at h; exact h

theorem inst_KRb (i N M L : PTm n) :
    Γ ⊢[PRAAx] inst2 KRb i (pairT N (pairT M L)) ≐ two * (M * M) * (pw (xs i M) N * uq i M L) := by
  have h := inst2_lift4 (Γ := Γ) (two * (var 2 * var 2) * (pw (monus (var 2 * var 2) (var 0 * var 0)) (var 1) *
    quo (fact (var 3)) (var 2 * var 2 + var 0 * var 0))) i N M L
  simp at h; exact h

theorem inst_SRb (i N M L : PTm n) :
    Γ ⊢[PRAAx] inst2 SRb i (pairT N (pairT M L)) ≐ pw (M * M) N * uq i M L := by
  have h := inst2_lift4 (Γ := Γ) (pw (var 2 * var 2) (var 1) *
    quo (fact (var 3)) (var 2 * var 2 + var 0 * var 0)) i N M L
  simp at h; exact h

/-- `eq:pigeometric`, one step: `R_{N+1} + F P_N = 2M² R_N`. -/
theorem geo_step {N M₀ L : PTm n} (hL : Γ ⊢[PRAAx] le (two * (succ M₀ * succ M₀)) L) :
    Γ ⊢[PRAAx] Rs (succ N) (succ M₀) L + fact L * Ps N (succ M₀) (succ M₀) ≐
      two * (succ M₀ * succ M₀) * Rs N (succ M₀) L := by
  have hLs := (LeanProofs.IPRA.Analysis.BaselAverages.shift_le hL).wk (ψ := lt (var 0) (Syn.shift (succ M₀)))
  have es2 : Syn.shift (two * (succ M₀ * succ M₀)) = two * (succ (Syn.shift M₀) * succ (Syn.shift M₀)) := by
    simp [Syn.shift]
  have es1 : Syn.shift (succ M₀) = succ (Syn.shift M₀) := by simp [Syn.shift]
  have esN : Syn.shift (succ N) = succ (Syn.shift N) := by simp [Syn.shift]
  have esF : Syn.shift (fact L) = fact (Syn.shift L) := by simp [Syn.shift]
  rw [es2, es1] at hLs
  have a := sum_lin (Γ := Γ) Rb Pb KRb (succ M₀) (pairT (succ N) (pairT (succ M₀) L)) (pairT N (succ M₀))
    (pairT N (pairT (succ M₀) L)) (fact L) (.allI (.impI (by
      simp only [shift_pairT, es1, esN, esF]
      have hj : (lt (var 0) (succ (Syn.shift M₀)) :: Γ.map Fm.shift) ⊢[PRAAx] le (var 0) (succ (Syn.shift M₀)) :=
        le_trans (le_succ_self _) Prf.hyp0
      have ue := natEq (u_eq_le hj hLs)
      have hm := natEq (eq_add_of_le (le_mul_mono hj hj))
      have i1 := natEq (inst_Rb (Γ := lt (var 0) (succ (Syn.shift M₀)) :: Γ.map Fm.shift) (var 0)
        (succ (Syn.shift N)) (succ (Syn.shift M₀)) (Syn.shift L))
      have i2 := natEq (inst_Pb (Γ := lt (var 0) (succ (Syn.shift M₀)) :: Γ.map Fm.shift) (var 0)
        (Syn.shift N) (succ (Syn.shift M₀)))
      have i3 := natEq (inst_KRb (Γ := lt (var 0) (succ (Syn.shift M₀)) :: Γ.map Fm.shift) (var 0)
        (Syn.shift N) (succ (Syn.shift M₀)) (Syn.shift L))
      have px := natEq (pw_succ (Γ := lt (var 0) (succ (Syn.shift M₀)) :: Γ.map Fm.shift)
        (xs (var 0) (succ (Syn.shift M₀))) (Syn.shift N))
      apply deriveNat; ipra_simps
      rw [i1, i2, i3]
      linear_combination 𝔟 (uq (var 0) (succ (Syn.shift M₀)) (Syn.shift L)) * px +
        𝔟 (pw (xs (var 0) (succ (Syn.shift M₀))) (Syn.shift N)) * ue -
        (𝔟 (pw (xs (var 0) (succ (Syn.shift M₀))) (Syn.shift N)) *
          𝔟 (uq (var 0) (succ (Syn.shift M₀)) (Syn.shift L))) * hm)))
  have b := sum_scale (Γ := Γ) KRb Rb (succ M₀) (two * (succ M₀ * succ M₀)) (pairT N (pairT (succ M₀) L))
    (pairT N (pairT (succ M₀) L)) (.allI (.impI (by
      simp only [shift_pairT, es1]
      have e : Syn.shift (two * (succ M₀ * succ M₀)) = two * (succ (Syn.shift M₀) * succ (Syn.shift M₀)) := by
        simp [Syn.shift]
      rw [e]
      exact (inst_KRb _ _ _ _).eqTrans (congrMul (.eqRefl _) (inst_Rb _ _ _ _).eqSymm))))
  exact a.eqTrans b

/-- `R_N ≤ M^{2N} R_0`. -/
theorem R_le (N M L : PTm n) : Γ ⊢[PRAAx] le (Rs N M L) (pw (M * M) N * Rs zero M L) := by
  have h1 := sum_le_params (Γ := Γ) Rb SRb (pairT N (pairT M L)) (pairT N (pairT M L)) M (.allI (.impI (by
      simp only [shift_pairT]
      have hj : (lt (var 0) (Syn.shift M) :: Γ.map Fm.shift) ⊢[PRAAx] le (var 0) (Syn.shift M) :=
        le_trans (le_succ_self _) Prf.hyp0
      exact le_congr (inst_Rb _ _ _ _).eqSymm (inst_SRb _ _ _ _).eqSymm
        (le_mul_mono (pw_le_pw (Syn.shift N) (x_le_sq hj)) (le_refl _)))))
  have h2 := sum_scale (Γ := Γ) SRb Rb M (pw (M * M) N) (pairT zero (pairT M L)) (pairT N (pairT M L))
    (.allI (.impI (by
      simp only [shift_pairT]
      have e0 : Syn.shift (zero : PTm n) = zero := by simp [Syn.shift]
      have e : Syn.shift (pw (M * M) N) = pw (Syn.shift M * Syn.shift M) (Syn.shift N) := by simp [Syn.shift]
      rw [e0, e]
      have a := natEq (inst_SRb (Γ := lt (var 0) (Syn.shift M) :: Γ.map Fm.shift) (var 0) (Syn.shift N)
        (Syn.shift M) (Syn.shift L))
      have b := natEq (inst_Rb (Γ := lt (var 0) (Syn.shift M) :: Γ.map Fm.shift) (var 0) zero
        (Syn.shift M) (Syn.shift L))
      have c := natEq (pw_zero (Γ := lt (var 0) (Syn.shift M) :: Γ.map Fm.shift) (xs (var 0) (Syn.shift M)))
      apply deriveNat; ipra_simps
      rw [a, b, c]; ring)))
  exact le_congr (.eqRefl _) h2 h1

/-- `Q(M) = M R_0`. -/
theorem Q_eq (M L : PTm n) :
    Γ ⊢[PRAAx] LeanProofs.IPRA.Analysis.BaselQuadrature.Q M L ≐ M * Rs zero M L := by
  refine sum_scale Qb Rb M M (pairT zero (pairT M L)) (pairT M L) (.allI (.impI ?_))
  simp only [shift_pairT]
  have e0 : Syn.shift (zero : PTm n) = zero := by simp [Syn.shift]
  rw [e0]
  have a := natEq (inst_Qb (Γ := lt (var 0) (Syn.shift M) :: Γ.map Fm.shift) (var 0) (Syn.shift M) (Syn.shift L))
  have b := natEq (inst_Rb (Γ := lt (var 0) (Syn.shift M) :: Γ.map Fm.shift) (var 0) zero
    (Syn.shift M) (Syn.shift L))
  have c := natEq (pw_zero (Γ := lt (var 0) (Syn.shift M) :: Γ.map Fm.shift) (xs (var 0) (Syn.shift M)))
  apply deriveNat; ipra_simps
  rw [a, b, c]; ring

/-! ## The Horner sum -/

/-- Step of `Th`: variables `0 = N`, `1 = Th N`, `2 = M`. -/
abbrev thStep : PTm 3 := two * (var 2 * var 2) * var 1 + ap2 (sumF Pb) (var 2) (pairT (var 0) (var 2))
abbrev thF : PR 2 := rec2 zero thStep

/-- `Th N M = ∑_{j<N} (2M²)^{N−1−j} P_j`. -/
abbrev Th (N M : PTm n) : PTm n := ap2 thF N M

theorem Th_zero (M : PTm n) : Γ ⊢[PRAAx] Th zero M ≐ zero := by
  have h := rec2_zero (Γ := Γ) zero thStep M
  simpa using h

theorem Th_succ (N M : PTm n) : Γ ⊢[PRAAx] Th (succ N) M ≐ two * (M * M) * Th N M + Ps N M M := by
  have h := rec2_succ (Γ := Γ) zero thStep N M
  simpa using h

/-- `(2M²)^N R_0 = F · Th N + R_N`. -/
abbrev Horner (N M₀ L : PTm n) : Fm PTm n :=
  pw (two * (succ M₀ * succ M₀)) N * Rs zero (succ M₀) L ≐ fact L * Th N (succ M₀) + Rs N (succ M₀) L

theorem horner_base (M₀ L : PTm n) : Γ ⊢[PRAAx] Horner zero M₀ L := by
  have p0 := natEq (pw_zero (Γ := Γ) (two * (succ M₀ * succ M₀)))
  have t0 := natEq (Th_zero (Γ := Γ) (succ M₀))
  apply deriveNat; ipra_simps
  rw [p0, t0]; ring

theorem horner_step {N M₀ L : PTm n} (hL : Γ ⊢[PRAAx] le (two * (succ M₀ * succ M₀)) L)
    (ih : Γ ⊢[PRAAx] Horner N M₀ L) : Γ ⊢[PRAAx] Horner (succ N) M₀ L := by
  have e := natEq ih
  have g := natEq (geo_step (N := N) hL)
  have ps := natEq (pw_succ (Γ := Γ) (two * (succ M₀ * succ M₀)) N)
  have t := natEq (Th_succ (Γ := Γ) N (succ M₀))
  apply deriveNat; ipra_simps
  rw [ps, t]
  linear_combination (2 * ((𝔞 M₀ + 1) * (𝔞 M₀ + 1))) * e - g

/-- Variables: `0 = N` (induction), `1 = M₀`, `2 = L`. -/
private abbrev hoF : Fm PTm 3 :=
  le (two * (succ (var 1) * succ (var 1))) (var 2) ⟶ Horner (var 0) (var 1) (var 2)

private theorem ho₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] hoF := by
  ipra_ind (⟨le_QF _ _, trivial⟩) [subst_le, subst_ap2, subst_pairT]
  · exact .impI (horner_base _ _)
  · exact .impI (horner_step Prf.hyp0 (Prf.impE Prf.hyp1 Prf.hyp0))

theorem horner {M₀ L : PTm n} (hL : Γ ⊢[PRAAx] le (two * (succ M₀ * succ M₀)) L) (N : PTm n) :
    Γ ⊢[PRAAx] Horner N M₀ L := by
  have h := inst (Γ := Γ) ho₀ (![N, M₀, L] : Fin 3 → PTm n)
  simp at h
  exact Prf.impE h hL

/-! ## Euler's numerators -/

/-- Step of `Eu`: variables `0 = N`, `1 = Eu N`, `2` unused. -/
abbrev euStep : PTm 3 := two * succ (two * var 0) * var 1 + ap2 (prodF bB) (var 0) zero
abbrev euF : PR 2 := rec2 zero euStep

/-- `Eu N = 2^{N−1} (2N−1)!! ∑_{j<N} J_j/2^j` with `J_j = (2j)!!/(2j+1)!!`, by
`Eu 0 = 0`, `Eu (N+1) = 2 (2N+1) · Eu N + (2N)!!`; so `p_N/4 = Eu N/(2^N (2N−1)!!)`. -/
abbrev Eu (N : PTm n) : PTm n := ap2 euF N zero

theorem Eu_zero : Γ ⊢[PRAAx] Eu (zero : PTm n) ≐ zero := by
  have h := rec2_zero (Γ := Γ) zero euStep (zero : PTm n)
  simpa using h

theorem Eu_succ (N : PTm n) : Γ ⊢[PRAAx] Eu (succ N) ≐ two * succ (two * N) * Eu N + db N := by
  have h := rec2_succ (Γ := Γ) zero euStep N (zero : PTm n)
  simpa using h

/-- `|M² · da N · Th N − M^{2N+1} · Eu N| ≤ (3 · 2^N − (2N+3)) · da N · M^{2N}`. -/
abbrev EInv (N M : PTm n) : Fm PTm n :=
  le (M * M * (da N * Th N M) + succ (succ (succ (two * N))) * (da N * pw (M * M) N))
      (M * (pw (M * M) N * Eu N) + num 3 * (pw two N * (da N * pw (M * M) N))) ⋏
    le (M * (pw (M * M) N * Eu N) + succ (succ (succ (two * N))) * (da N * pw (M * M) N))
      (M * M * (da N * Th N M) + num 3 * (pw two N * (da N * pw (M * M) N)))

theorem eu_base (M : PTm n) : Γ ⊢[PRAAx] EInv zero M := by
  have t0 := natEq (Th_zero (Γ := Γ) M); have e0 := natEq (Eu_zero (Γ := Γ))
  have a0 := natEq (da_zero (Γ := Γ)); have pz := natEq (pw_zero (Γ := Γ) (M * M))
  have p2 := natEq (pw_zero (Γ := Γ) (two : PTm n))
  refine .andI ?_ ?_
  · ipra_le 0 using rw [t0, e0, a0, pz, p2]; ring
  · ipra_le 0 using rw [t0, e0, a0, pz, p2]; ring

theorem eu_step {N M : PTm n} (ih : Γ ⊢[PRAAx] EInv N M) : Γ ⊢[PRAAx] EInv (succ N) M := by
  have ihU := Prf.andE₁ ih; have ihL := Prf.andE₂ ih
  have q := even_power_integral (Γ := Γ) N M
  have qU := Prf.andE₁ q; have qL := Prf.andE₂ q
  have t := natEq (Th_succ (Γ := Γ) N M); have eu := natEq (Eu_succ (Γ := Γ) N)
  have a1 := natEq (da_succ (Γ := Γ) N)
  have pS := natEq (pw_succ (Γ := Γ) (M * M) N); have p2 := natEq (pw_succ (Γ := Γ) two N)
  refine .andI ?_ ?_
  · ipra_le 2 * (2 * 𝔞 N + 1) * (𝔞 M * 𝔞 M) * sl ihU + (𝔞 M * 𝔞 M) * sl qU +
        𝔞 N * (𝔞 (da (succ N)) * 𝔞 (pw (M * M) (succ N))) using
      rw [t, eu, a1, pS, p2]; ring
  · ipra_le 2 * (2 * 𝔞 N + 1) * (𝔞 M * 𝔞 M) * sl ihL + (𝔞 M * 𝔞 M) * sl qL +
        𝔞 (da (succ N)) * 𝔞 (pw (M * M) (succ N)) using
      rw [t, eu, a1, pS, p2]; ring

/-- Variables: `0 = N` (induction), `1 = M`. -/
private abbrev euFm : Fm PTm 2 := EInv (var 0) (var 1)

private theorem eu₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] euFm := by
  ipra_ind (⟨le_QF _ _, le_QF _ _⟩) [subst_le, subst_ap2, subst_pairT]
  · exact eu_base _
  · exact eu_step Prf.hyp0

theorem eu_all (N M : PTm n) : Γ ⊢[PRAAx] EInv N M := by
  have h := inst (Γ := Γ) eu₀ (![N, M] : Fin 2 → PTm n)
  simp at h
  exact h

/-! ## Euler's series against the Riemann-sum code (`eq:pibound`) -/

theorem sq_pos (M₀ : PTm n) : Γ ⊢[PRAAx] succ M₀ * succ M₀ ≐ succ (pred (succ M₀ * succ M₀)) :=
  LeanProofs.IPRA.AnalyticNumberTheory.Primes.eq_succ_pred (y := M₀ * M₀ + two * M₀)
    (by ipra_ring)

/-- `eq:pibound` with its mesh error, for `M = M₀ + 1`, `2M² ≤ L`, `F = L!`, `Q = Q(M)` the Riemann-sum code
of `π/4`: `F M · Eu N ≤ 2^N da N (M Q + 3F)` and
`2^N da N · M Q ≤ F M · Eu N + 3 · 2^N da N · F + da N · M Q`, i.e.
`p_N/4 − 3/M ≤ Q_M ≤ p_N/4 + 3/M + Q_M/2^N`. -/
theorem euler_pi {M₀ L : PTm n} (hL : Γ ⊢[PRAAx] le (two * (succ M₀ * succ M₀)) L) (N : PTm n) :
    Γ ⊢[PRAAx] le (fact L * (succ M₀ * Eu N))
        (pw two N * da N *
          (succ M₀ * LeanProofs.IPRA.Analysis.BaselQuadrature.Q (succ M₀) L + num 3 * fact L)) ⋏
      le (pw two N * da N * (succ M₀ * LeanProofs.IPRA.Analysis.BaselQuadrature.Q (succ M₀) L))
        (fact L * (succ M₀ * Eu N) + num 3 * (pw two N * da N * fact L) +
          da N * (succ M₀ * LeanProofs.IPRA.Analysis.BaselQuadrature.Q (succ M₀) L)) := by
  have e := eu_all (Γ := Γ) N (succ M₀)
  have eU := Prf.andE₁ e; have eL := Prf.andE₂ e
  have hR := R_le (Γ := Γ) N (succ M₀) L
  have h := natEq (horner hL N)
  have pmb := natEq (LeanProofs.IPRA.AnalyticNumberTheory.LocalFactor.pw_mul_base (Γ := Γ) two
    (succ M₀ * succ M₀) N)
  have qR := natEq (Q_eq (Γ := Γ) (succ M₀) L)
  have hS := LeanProofs.IPRA.AnalyticNumberTheory.Valuation.pw_pos' (sq_pos (Γ := Γ) M₀) N
  refine .andI
    (mul_le_cancel (d' := pred (pw (succ M₀ * succ M₀) N))
      (le_congr (congrMul hS (.eqRefl _)) (congrMul hS (.eqRefl _)) ?_))
    (mul_le_cancel (d' := pred (pw (succ M₀ * succ M₀) N))
      (le_congr (congrMul hS (.eqRefl _)) (congrMul hS (.eqRefl _)) ?_))
  · ipra_le 𝔞 (fact L) * sl eL + (𝔞 M₀ + 1) * (𝔞 M₀ + 1) * 𝔞 (da N) * 𝔞 (Rs N (succ M₀) L) +
        (2 * 𝔞 N + 3) * 𝔞 (da N) * 𝔞 (pw (succ M₀ * succ M₀) N) * 𝔞 (fact L) using
      rw [pmb] at h
      rw [qR]
      linear_combination ((𝔞 M₀ + 1) * (𝔞 M₀ + 1) * 𝔞 (da N)) * h
  · ipra_le 𝔞 (fact L) * sl eU +
        (2 * 𝔞 N + 3) * 𝔞 (da N) * 𝔞 (pw (succ M₀ * succ M₀) N) * 𝔞 (fact L) +
        𝔞 (da N) * ((𝔞 M₀ + 1) * (𝔞 M₀ + 1)) * sl hR using
      rw [pmb] at h
      rw [qR]
      linear_combination (-((𝔞 M₀ + 1) * (𝔞 M₀ + 1) * 𝔞 (da N))) * h

end LeanProofs.IPRA.Analysis.EulerPiSeries
