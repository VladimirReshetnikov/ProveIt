import IPRADerivations.Analysis.Series.Basel.BaselUniform
import IPRADerivations.Core.LinearCombination

/-!
# The rational identification of the Basel constant

Packet: `analysis/basel_ipra`, `paper/basel_ipra.tex`, Section `sec:riemann`, Proposition `prop:quadrature`:
for `N, M ≥ 1` and `Q_M = M ∑_{i<M} 1/(M² + i²)`, `|Q_M − A_N| ≤ N/M + 1/(2N + 1)` (`eq:quadrature`).

Denominators are cleared by `F = L!` with `2M² ≤ L` and `2N + 1 ≤ L`, so that `u_i = F/(M² + i²)` and
`g_j = F/(2j+1)` are exact: `Q(M) = ∑_{i<M} M u_i = F Q_M`. The paper averages the finite geometric identity
`1/(1+x²) = ∑_{j<N} (−1)^j x^{2j} + (−1)^N x^{2N}/(1+x²)` over `x = i/M` and exchanges the two sums. Here the
remainder `U_N = ∑_{i<M} i^{2N} M² u_i` (`= F M^{2N+1} ρ_N`) satisfies the one-step identity
`M² U_N + U_{N+1} = M² F ∑_{i<M} i^{2N}` (`U_step`), and induction on `N` (`inv`) carries
`|M^{2N+1} (Q(M) − F A_N) − (−1)^N U_N| ≤ N F M^{2N}`, each step costing at most `F M^{2N}` by `lem:moment`.
Finally `(2N + 1) U_N ≤ F M^{2N+1}`, again by `lem:moment`.

* `quadrature` (`prop:quadrature`): `(2N+1) M^{2N+1} |Q(M) − (A⁺ − A⁻)| ≤ (2N+1) N F M^{2N} + F M^{2N+1}`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.BaselQuadrature

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.BaselCore (Ap Am Ap_succ Am_succ lift3 inst2_lift3 sum_lin)
open LeanProofs.IPRA.Analysis.BaselAverages (g)
open LeanProofs.IPRA.Analysis.BaselFinite (tB odd_pos par_sum compl_succ)
open LeanProofs.IPRA.Analysis.PowerSums (Bq moment)
open LeanProofs.IPRA.Analysis.Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Bodies with three parameters -/

/-- A body over `0 = i`, `1 = N`, `2 = M`, `3 = L`, read over `0 = i`, `1 = ⟨N, ⟨M, L⟩⟩`. -/
def lift4 (K : PTm 4) : PTm 2 := Syn.subst ![var 0, fstT (var 1), fstT (sndT (var 1)), sndT (sndT (var 1))] K

theorem inst2_lift4 (K : PTm 4) (i N M L : PTm n) :
    Γ ⊢[PRAAx] inst2 (lift4 K) i (pairT N (pairT M L)) ≐ Syn.subst ![i, N, M, L] K := by
  have e : inst2 (lift4 K) i (pairT N (pairT M L)) =
      Syn.subst ![i, fstT (pairT N (pairT M L)), fstT (sndT (pairT N (pairT M L))),
        sndT (sndT (pairT N (pairT M L)))] K := by
    simp only [inst2, lift4, Syn.subst_subst]
    congr 1; funext j; fin_cases j <;> simp
  rw [e]
  exact Prf.eqCongr K fun j => by
    fin_cases j
    · exact .eqRefl _
    · exact fst_pair _ _
    · exact (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
    · exact (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)

/-! ## The quadrature sums -/

/-- `u_i = L!/(M² + i²)`. -/
abbrev uq (i M L : PTm n) : PTm n := quo (fact L) (M * M + i * i)

/-- `M u_i` over `(i, M, L)`; `Q(M) = ∑_{i<M} M u_i`. -/
abbrev Qb : PTm 2 := lift3 (var 1 * quo (fact (var 2)) (var 1 * var 1 + var 0 * var 0))
abbrev Q (M L : PTm n) : PTm n := ap2 (sumF Qb) M (pairT M L)

/-- `i^{2N} M² u_i` over `(i, N, M, L)`; `U_N = ∑_{i<M} i^{2N} M² u_i`. -/
abbrev Ub : PTm 2 := lift4 (pw (var 0) (two * var 1) * (var 2 * var 2) * quo (fact (var 3)) (var 2 * var 2 + var 0 * var 0))
abbrev U (N M L : PTm n) : PTm n := ap2 (sumF Ub) M (pairT N (pairT M L))

/-- `i^{2N} M² F` over `(i, N, M, L)`. -/
abbrev kb : PTm 2 := lift4 (pw (var 0) (two * var 1) * (var 2 * var 2) * fact (var 3))

/-- `∑_{i<M} iᵖ`. -/
abbrev Pm (p M : PTm n) : PTm n := ap2 (sumF Bq) M p

theorem inst_Qb (i M L : PTm n) : Γ ⊢[PRAAx] inst2 Qb i (pairT M L) ≐ M * uq i M L := by
  have h := inst2_lift3 (Γ := Γ) (var 1 * quo (fact (var 2)) (var 1 * var 1 + var 0 * var 0)) i M L
  simp at h; exact h

theorem inst_Ub (i N M L : PTm n) :
    Γ ⊢[PRAAx] inst2 Ub i (pairT N (pairT M L)) ≐ pw i (two * N) * (M * M) * uq i M L := by
  have h := inst2_lift4 (Γ := Γ) (pw (var 0) (two * var 1) * (var 2 * var 2) *
    quo (fact (var 3)) (var 2 * var 2 + var 0 * var 0)) i N M L
  simp at h; exact h

theorem inst_kb (i N M L : PTm n) :
    Γ ⊢[PRAAx] inst2 kb i (pairT N (pairT M L)) ≐ pw i (two * N) * (M * M) * fact L := by
  have h := inst2_lift4 (Γ := Γ) (pw (var 0) (two * var 1) * (var 2 * var 2) * fact (var 3)) i N M L
  simp at h; exact h

/-! ## Exactness of `u_i` -/

theorem d_pos (i M₀ : PTm n) : Γ ⊢[PRAAx] succ M₀ * succ M₀ + i * i ≐ succ (pred (succ M₀ * succ M₀ + i * i)) :=
  LeanProofs.IPRA.AnalyticNumberTheory.Primes.eq_succ_pred (y := M₀ * M₀ + two * M₀ + i * i)
    (by ipra_ring)

/-- `L! = (M² + i²) u_i` for `i < M = M₀ + 1` and `2M² ≤ L`. -/
theorem u_eq {i M₀ L : PTm n} (hi : Γ ⊢[PRAAx] lt i (succ M₀)) (hL : Γ ⊢[PRAAx] le (two * (succ M₀ * succ M₀)) L) :
    Γ ⊢[PRAAx] fact L ≐ (succ M₀ * succ M₀ + i * i) * uq i (succ M₀) L := by
  have hii : Γ ⊢[PRAAx] le (i * i) (succ M₀ * succ M₀) :=
    LeanProofs.IPRA.AnalyticNumberTheory.PhiLower.le_mul_mono (le_of_lt hi) (le_of_lt hi)
  have hd : Γ ⊢[PRAAx] le (succ M₀ * succ M₀ + i * i) L := by
    refine le_trans (le_of_eq_add (d := monus (succ M₀ * succ M₀) (i * i)) ?_) hL
    ipra_lc natEq (eq_add_of_le hii)
  have dv : Γ ⊢[PRAAx] dvd (succ M₀ * succ M₀ + i * i) (fact L) :=
    dvd_congr_left (d_pos i M₀).eqSymm
      (LeanProofs.IPRA.AnalyticNumberTheory.Primes.dvd_fact (le_congr (d_pos i M₀) (.eqRefl _) hd))
  exact LeanProofs.IPRA.DiophantineNumberTheory.Coprime.eq_of_dvd' (d_pos i M₀) dv

/-! ## The remainder recursion -/

theorem shift_sq (M₀ : PTm n) : Syn.shift (succ M₀ * succ M₀) = succ (Syn.shift M₀) * succ (Syn.shift M₀) := by
  simp [Syn.shift]

/-- `U_{N+1} + M² U_N = M² F ∑_{i<M} i^{2N}` for `M = M₀ + 1`, `2M² ≤ L`. -/
theorem U_step {N M₀ L : PTm n} (hL : Γ ⊢[PRAAx] le (two * (succ M₀ * succ M₀)) L) :
    Γ ⊢[PRAAx] U (succ N) (succ M₀) L + succ M₀ * succ M₀ * U N (succ M₀) L ≐
      succ M₀ * succ M₀ * fact L * Pm (two * N) (succ M₀) := by
  have hLs := (LeanProofs.IPRA.Analysis.BaselAverages.shift_le hL).wk (ψ := lt (var 0) (Syn.shift (succ M₀)))
  have es2 : Syn.shift (two * (succ M₀ * succ M₀)) = two * (succ (Syn.shift M₀) * succ (Syn.shift M₀)) := by
    simp [Syn.shift]
  rw [es2] at hLs
  have es1 : Syn.shift (succ M₀) = succ (Syn.shift M₀) := by simp [Syn.shift]
  have esN : Syn.shift (succ N) = succ (Syn.shift N) := by simp [Syn.shift]
  have s1 := natEq (sum_lin (Γ := Γ) Ub Ub kb (succ M₀) (pairT (succ N) (pairT (succ M₀) L))
    (pairT N (pairT (succ M₀) L)) (pairT N (pairT (succ M₀) L)) (succ M₀ * succ M₀) (.allI (.impI (by
      simp only [shift_pairT, es1, esN, shift_sq]
      rw [es1] at hLs
      have i1 := natEq (inst_Ub (Γ := lt (var 0) (succ (Syn.shift M₀)) :: Γ.map Fm.shift) (var 0)
        (succ (Syn.shift N)) (succ (Syn.shift M₀)) (Syn.shift L))
      have i2 := natEq (inst_Ub (Γ := lt (var 0) (succ (Syn.shift M₀)) :: Γ.map Fm.shift) (var 0)
        (Syn.shift N) (succ (Syn.shift M₀)) (Syn.shift L))
      have i3 := natEq (inst_kb (Γ := lt (var 0) (succ (Syn.shift M₀)) :: Γ.map Fm.shift) (var 0)
        (Syn.shift N) (succ (Syn.shift M₀)) (Syn.shift L))
      have ue := natEq (u_eq Prf.hyp0 hLs)
      have pe := natEq ((congrAp2 powF (by ipra_ring :
          (lt (var 0) (succ (Syn.shift M₀)) :: Γ.map Fm.shift) ⊢[PRAAx]
            two * succ (Syn.shift N) ≐ succ (succ (two * Syn.shift N))) (.eqRefl (var 0))).eqTrans
        ((pw_succ _ _).eqTrans (congrMul (pw_succ _ _) (.eqRefl _))))
      apply deriveNat; ipra_simps
      rw [i1, i2, i3, pe]
      linear_combination -(𝔞 (pw (var 0) (two * Syn.shift N)) * (𝔞 (Syn.shift M₀) + 1) * (𝔞 (Syn.shift M₀) + 1)) * ue))))
  have s2 := natEq (LeanProofs.IPRA.Probability.Independence.sum_scale (Γ := Γ) kb Bq (succ M₀)
    (succ M₀ * succ M₀ * fact L) (two * N) (pairT N (pairT (succ M₀) L)) (.allI (.impI (by
      simp only [shift_pairT, es1]
      have e : Syn.shift (succ M₀ * succ M₀ * fact L) = succ (Syn.shift M₀) * succ (Syn.shift M₀) * fact (Syn.shift L) := by
        simp [Syn.shift]
      have e' : Syn.shift (two * N) = two * Syn.shift N := by simp [Syn.shift]
      rw [e, e', LeanProofs.IPRA.Analysis.PowerSums.inst2_B]
      refine (inst_kb _ _ _ _).eqTrans ?_
      ipra_ring))))
  apply deriveNat; ipra_simps
  linear_combination s1 + s2

/-- `U_0 = M Q(M)`. -/
theorem U_zero (M L : PTm n) : Γ ⊢[PRAAx] U zero M L ≐ M * Q M L := by
  refine LeanProofs.IPRA.Probability.Independence.sum_scale Ub Qb M M (pairT M L) (pairT zero (pairT M L))
    (.allI (.impI ?_))
  simp only [shift_pairT]
  have e0 : Syn.shift (zero : PTm n) = zero := by simp [Syn.shift]
  rw [e0]
  have a := natEq (inst_Ub (Γ := lt (var 0) (Syn.shift M) :: Γ.map Fm.shift) (var 0) zero (Syn.shift M) (Syn.shift L))
  have b := natEq (inst_Qb (Γ := lt (var 0) (Syn.shift M) :: Γ.map Fm.shift) (var 0) (Syn.shift M) (Syn.shift L))
  have c := natEq ((congrAp2 powF (by ipra_ring :
      (lt (var 0) (Syn.shift M) :: Γ.map Fm.shift) ⊢[PRAAx] two * zero ≐ (zero : PTm (n + 1))) (.eqRefl (var 0))).eqTrans
    (pw_zero _))
  apply deriveNat; ipra_simps
  rw [a, b, c]
  ring

/-! ## The cost of one step (`lem:moment`) -/

/-- With `F = (2N+1) g_N`: `F ∑ i^{2N} ≤ M^{2N+1} g_N ≤ F ∑ i^{2N} + F M^{2N}`. -/
theorem step_cost {N M L : PTm n} (hN : Γ ⊢[PRAAx] le (succ (two * N)) L) :
    Γ ⊢[PRAAx] le (fact L * Pm (two * N) M) (pw M (succ (two * N)) * g N L) ⋏
      le (pw M (succ (two * N)) * g N L) (fact L * Pm (two * N) M + fact L * pw M (two * N)) := by
  have m := moment (Γ := Γ) (two * N) M
  have m1 := natEq (eq_add_of_le (Prf.andE₁ m)); have m2 := natEq (eq_add_of_le (Prf.andE₂ m))
  refine .andI (le_of_eq_add (d := g N L * monus (pw M (succ (two * N))) (succ (two * N) * Pm (two * N) M)) ?_)
    (le_of_eq_add (d := g N L * monus (succ (two * N) * Pm (two * N) M + succ (two * N) * pw M (two * N))
      (pw M (succ (two * N)))) ?_)
  · ipra_lc 𝔞 (g N L) * m1 - 𝔞 (Pm (two * N) M) * natEq (LeanProofs.IPRA.Analysis.BaselSquares.fact_eq hN)
  · ipra_lc 𝔞 (g N L) * m2 +
      (𝔞 (Pm (two * N) M) + 𝔞 (pw M (two * N))) * natEq (LeanProofs.IPRA.Analysis.BaselSquares.fact_eq hN)

/-! ## The invariant -/

/-- The ring form of the induction step. -/
theorem quad_ring {R : Type*} [CommRing R] (m2 Pw Pe Q Ap Am ApN AmN U UN PwN PeN p q pN qN g F P ε ε' w1 w2 Nn : R)
    (hPw : PwN = Pw * m2) (hPe : PeN = Pe * m2) (hap : ApN = Ap + q * g) (ham : AmN = Am + p * g)
    (hus : UN + m2 * U = m2 * F * P) (he1 : Pw * g = F * P + ε) (he2 : F * P + F * Pe = Pw * g + ε')
    (hp : pN = q) (hq : qN = p) (hps : p + q = 1)
    (ih1 : Pw * Ap + q * U + Nn * (F * Pe) = Pw * (Q + Am) + p * U + w1)
    (ih2 : Pw * (Q + Am) + p * U + Nn * (F * Pe) = Pw * Ap + q * U + w2) :
    (PwN * ApN + qN * UN + (Nn + 1) * (F * PeN) = PwN * (Q + AmN) + pN * UN + (m2 * w1 + m2 * (q * (F * Pe + ε) + p * ε'))) ∧
    (PwN * (Q + AmN) + pN * UN + (Nn + 1) * (F * PeN) = PwN * ApN + qN * UN + (m2 * w2 + m2 * (q * ε' + p * (F * Pe + ε)))) := by
  have hus' : UN = m2 * F * P - m2 * U := by linear_combination hus
  subst hPw hPe hap ham hus'
  rw [hp, hq]
  constructor
  · linear_combination m2 * ih1 - m2 * F * Pe * hps + m2 * q * he1 + m2 * p * he2
  · linear_combination m2 * ih2 + m2 * p * he1 + m2 * q * he2 - m2 * F * Pe * hps

/-- `X⁺ = M^{2N+1} (Q + A⁻) + par N · U_N`, `X⁻ = M^{2N+1} A⁺ + (1 ∸ par N) U_N`, so that
`X⁺ − X⁻ = M^{2N+1} (Q(M) − F A_N) − (−1)^N U_N`. -/
abbrev Xp (N M L : PTm n) : PTm n := pw M (succ (two * N)) * (Q M L + Am N L) + par N * U N M L
abbrev Xm (N M L : PTm n) : PTm n := pw M (succ (two * N)) * Ap N L + monus one (par N) * U N M L

abbrev Inv (N M L : PTm n) : Fm PTm n :=
  le (Xp N M L) (Xm N M L + N * (fact L * pw M (two * N))) ⋏ le (Xm N M L) (Xp N M L + N * (fact L * pw M (two * N)))

theorem inv_zero (M L : PTm n) : Γ ⊢[PRAAx] Inv zero M L := by
  have u := natEq (U_zero (Γ := Γ) M L)
  have a0 := natEq (sum_zero (Γ := Γ) (LeanProofs.IPRA.Analysis.BaselFinite.eB tB) (fact L))
  have b0 := natEq (sum_zero (Γ := Γ) (LeanProofs.IPRA.Analysis.BaselFinite.oB tB) (fact L))
  have z0 := natEq ((congrMonus (.eqRefl one) (par_zero (Γ := Γ))).eqTrans (monus_zero _))
  have z1 := natEq (par_zero (Γ := Γ) (n := n))
  have p1 := natEq ((congrAp2 powF (congrSucc (by ipra_ring :
      Γ ⊢[PRAAx] two * zero ≐ (zero : PTm n))) (.eqRefl M)).eqTrans ((pw_succ _ _).eqTrans
    ((congrMul (pw_zero _) (.eqRefl _)).eqTrans (one_mul _))))
  refine .andI (le_of_eq_add (d := zero) ?_) (le_of_eq_add (d := zero) ?_)
  · apply deriveNat; ipra_simps
    rw [u, a0, b0, z0, z1, p1]; ring
  · apply deriveNat; ipra_simps
    rw [u, a0, b0, z0, z1, p1]; ring

theorem inv_step {N M₀ L : PTm n} (hL : Γ ⊢[PRAAx] le (two * (succ M₀ * succ M₀)) L)
    (ih : Γ ⊢[PRAAx] le (succ (two * N)) L ⟶ Inv N (succ M₀) L)
    (h : Γ ⊢[PRAAx] le (succ (two * succ N)) L) : Γ ⊢[PRAAx] Inv (succ N) (succ M₀) L := by
  have h' : Γ ⊢[PRAAx] le (succ (two * N)) L :=
    le_trans (le_of_eq_add (d := two) (by ipra_ring)) h
  have i := Prf.impE ih h'
  have i1 := natEq (eq_add_of_le (Prf.andE₁ i)); have i2 := natEq (eq_add_of_le (Prf.andE₂ i))
  have ap := natEq (Ap_succ (Γ := Γ) N L); have am := natEq (Am_succ (Γ := Γ) N L)
  have us := natEq (U_step (N := N) hL)
  have c := step_cost (M := succ M₀) h'
  have e1 := natEq (eq_add_of_le (Prf.andE₁ c)); have e2 := natEq (eq_add_of_le (Prf.andE₂ c))
  have p1 := natEq (par_succ (Γ := Γ) N); have q1 := natEq (compl_succ (Γ := Γ) N)
  have ps := natEq (par_sum (Γ := Γ) N)
  have pw1 := natEq ((congrAp2 powF (by ipra_ring :
      Γ ⊢[PRAAx] succ (two * succ N) ≐ succ (succ (succ (two * N)))) (.eqRefl (succ M₀))).eqTrans
    ((pw_succ _ _).eqTrans (congrMul (pw_succ _ _) (.eqRefl _))))
  have pw2 := natEq ((congrAp2 powF (by ipra_ring :
      Γ ⊢[PRAAx] two * succ N ≐ succ (succ (two * N))) (.eqRefl (succ M₀))).eqTrans
    ((pw_succ _ _).eqTrans (congrMul (pw_succ _ _) (.eqRefl _))))
  ipra_simps
  have r := quad_ring ((𝔞 M₀ + 1) * (𝔞 M₀ + 1)) (𝔞 (pw (succ M₀) (succ (two * N)))) (𝔞 (pw (succ M₀) (two * N)))
    (𝔞 (Q (succ M₀) L)) (𝔞 (Ap N L)) (𝔞 (Am N L)) (𝔞 (Ap (succ N) L)) (𝔞 (Am (succ N) L))
    (𝔞 (U N (succ M₀) L)) (𝔞 (U (succ N) (succ M₀) L))
    (𝔞 (pw (succ M₀) (succ (two * succ N)))) (𝔞 (pw (succ M₀) (two * succ N)))
    (𝔞 (par N)) (𝔞 (monus one (par N))) (𝔞 (par (succ N))) (𝔞 (monus one (par (succ N))))
    (𝔞 (g N L)) (𝔞 (fact L)) (𝔞 (Pm (two * N) (succ M₀)))
    (𝔞 (monus (pw (succ M₀) (succ (two * N)) * g N L) (fact L * Pm (two * N) (succ M₀))))
    (𝔞 (monus (fact L * Pm (two * N) (succ M₀) + fact L * pw (succ M₀) (two * N)) (pw (succ M₀) (succ (two * N)) * g N L)))
    (𝔞 (monus (Xm N (succ M₀) L + N * (fact L * pw (succ M₀) (two * N))) (Xp N (succ M₀) L)))
    (𝔞 (monus (Xp N (succ M₀) L + N * (fact L * pw (succ M₀) (two * N))) (Xm N (succ M₀) L)))
    (𝔞 N)
    (by linear_combination pw1) (by linear_combination pw2) (by linear_combination ap) (by linear_combination am)
    (by linear_combination us) (by linear_combination e1) (by linear_combination e2)
    (by linear_combination p1) (by linear_combination q1) (by linear_combination ps)
    (by linear_combination i1) (by linear_combination i2)
  refine .andI (le_of_eq_add (d := succ M₀ * succ M₀ *
      monus (Xm N (succ M₀) L + N * (fact L * pw (succ M₀) (two * N))) (Xp N (succ M₀) L) +
      succ M₀ * succ M₀ * (monus one (par N) * (fact L * pw (succ M₀) (two * N) +
        monus (pw (succ M₀) (succ (two * N)) * g N L) (fact L * Pm (two * N) (succ M₀))) +
        par N * monus (fact L * Pm (two * N) (succ M₀) + fact L * pw (succ M₀) (two * N))
          (pw (succ M₀) (succ (two * N)) * g N L))) ?_)
    (le_of_eq_add (d := succ M₀ * succ M₀ *
      monus (Xp N (succ M₀) L + N * (fact L * pw (succ M₀) (two * N))) (Xm N (succ M₀) L) +
      succ M₀ * succ M₀ * (monus one (par N) * monus (fact L * Pm (two * N) (succ M₀) + fact L * pw (succ M₀) (two * N))
          (pw (succ M₀) (succ (two * N)) * g N L) +
        par N * (fact L * pw (succ M₀) (two * N) +
          monus (pw (succ M₀) (succ (two * N)) * g N L) (fact L * Pm (two * N) (succ M₀))))) ?_)
  · ipra_lc r.1
  · ipra_lc r.2

/-- Variables: `0 = N`, `1 = M₀`, `2 = L`. -/
private abbrev invF : Fm PTm 3 :=
  le (two * (succ (var 1) * succ (var 1))) (var 2) ⟶ le (succ (two * var 0)) (var 2) ⟶
    Inv (var 0) (succ (var 1)) (var 2)

private theorem inv₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] invF := by
  refine ind _ ⟨le_QF _ _, le_QF _ _, le_QF _ _, le_QF _ _⟩ ?_ ?_
  · simp only [Fm.subst_imp, Fm.subst_and, Fm.subst_eq, subst_le, subst_ap2, subst_ap1, subst_pairT,
      PTm.subst_add, PTm.subst_mul, PTm.subst_monus, Syn.subst_var, Syn.inst_zero, Syn.inst_one, inst_two,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact .impI (.impI (inv_zero _ _))
  · simp only [Fm.subst_imp, Fm.subst_and, Fm.subst_eq, subst_le, subst_ap2, subst_ap1, subst_pairT,
      PTm.subst_add, PTm.subst_mul, PTm.subst_monus, Syn.subst_var, Syn.repl_zero, repl_one, repl_two,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact .impI (.impI (inv_step Prf.hyp1 (Prf.impE Prf.hyp1.wk Prf.hyp1) Prf.hyp0))

theorem inv {N M₀ L : PTm n} (hM : Γ ⊢[PRAAx] le (two * (succ M₀ * succ M₀)) L)
    (hN : Γ ⊢[PRAAx] le (succ (two * N)) L) : Γ ⊢[PRAAx] Inv N (succ M₀) L := by
  have i := inst (Γ := Γ) inv₀ (![N, M₀, L] : Fin 3 → PTm n)
  simp at i
  exact Prf.impE (Prf.impE i hM) hN

/-! ## The size of the remainder -/

/-- `i^{2N} F` over `(i, N, M, L)`. -/
abbrev kF : PTm 2 := lift4 (pw (var 0) (two * var 1) * fact (var 3))

theorem inst_kF (i N M L : PTm n) :
    Γ ⊢[PRAAx] inst2 kF i (pairT N (pairT M L)) ≐ pw i (two * N) * fact L := by
  have h := inst2_lift4 (Γ := Γ) (pw (var 0) (two * var 1) * fact (var 3)) i N M L
  simp at h; exact h

/-- `(2N + 1) U_N ≤ F M^{2N+1}`, i.e. `ρ_N ≤ 1/(2N+1)`. -/
theorem U_bound {N M₀ L : PTm n} (hM : Γ ⊢[PRAAx] le (two * (succ M₀ * succ M₀)) L) :
    Γ ⊢[PRAAx] le (succ (two * N) * U N (succ M₀) L) (fact L * pw (succ M₀) (succ (two * N))) := by
  have hMs := (LeanProofs.IPRA.Analysis.BaselAverages.shift_le hM).wk (ψ := lt (var 0) (Syn.shift (succ M₀)))
  have es2 : Syn.shift (two * (succ M₀ * succ M₀)) = two * (succ (Syn.shift M₀) * succ (Syn.shift M₀)) := by
    simp [Syn.shift]
  have es1 : Syn.shift (succ M₀) = succ (Syn.shift M₀) := by simp [Syn.shift]
  rw [es2, es1] at hMs
  have l := LeanProofs.IPRA.Analysis.PowerSums.sum_le (Γ := Γ) Ub kF (pairT N (pairT (succ M₀) L)) (succ M₀)
    (.allI (.impI (by
      simp only [shift_pairT, es1]
      have a := natEq (inst_Ub (Γ := lt (var 0) (succ (Syn.shift M₀)) :: Γ.map Fm.shift) (var 0) (Syn.shift N)
        (succ (Syn.shift M₀)) (Syn.shift L))
      have b := natEq (inst_kF (Γ := lt (var 0) (succ (Syn.shift M₀)) :: Γ.map Fm.shift) (var 0) (Syn.shift N)
        (succ (Syn.shift M₀)) (Syn.shift L))
      have ue := natEq (u_eq Prf.hyp0 hMs)
      refine le_of_eq_add (d := pw (var 0) (two * Syn.shift N) * (var 0 * var 0 *
        uq (var 0) (succ (Syn.shift M₀)) (Syn.shift L))) ?_
      apply deriveNat; ipra_simps
      rw [a, b]
      linear_combination 𝔞 (pw (var 0) (two * Syn.shift N)) * ue)))
  have s := natEq (LeanProofs.IPRA.Probability.Independence.sum_scale (Γ := Γ) kF Bq (succ M₀) (fact L) (two * N)
    (pairT N (pairT (succ M₀) L)) (.allI (.impI (by
      simp only [shift_pairT, es1]
      have e : Syn.shift (fact L) = fact (Syn.shift L) := by simp [Syn.shift]
      have e' : Syn.shift (two * N) = two * Syn.shift N := by simp [Syn.shift]
      rw [e, e', LeanProofs.IPRA.Analysis.PowerSums.inst2_B]
      refine (inst_kF _ _ _ _).eqTrans ?_
      ipra_ring))))
  refine le_of_eq_add (d := succ (two * N) * monus (ap2 (sumF kF) (succ M₀) (pairT N (pairT (succ M₀) L)))
      (U N (succ M₀) L) +
    fact L * monus (pw (succ M₀) (succ (two * N))) (succ (two * N) * Pm (two * N) (succ M₀))) ?_
  ipra_lc (2 * 𝔞 N + 1) * natEq (eq_add_of_le l) - (2 * 𝔞 N + 1) * s +
    𝔞 (fact L) * natEq (eq_add_of_le (Prf.andE₁ (moment (Γ := Γ) (two * N) (succ M₀))))

/-! ## The rational identification -/

/-- `prop:quadrature` (`eq:quadrature`), cleared by `F = L!` with `2M² ≤ L`, `2N + 1 ≤ L` (`M = M₀ + 1`):
`(2N+1) M^{2N+1} |Q(M) − (A⁺ − A⁻)| ≤ (2N+1) N F M^{2N} + F M^{2N+1}`, i.e.
`|Q_M − A_N| ≤ N/M + 1/(2N + 1)`. -/
theorem quadrature {N M₀ L : PTm n} (hM : Γ ⊢[PRAAx] le (two * (succ M₀ * succ M₀)) L)
    (hN : Γ ⊢[PRAAx] le (succ (two * N)) L) :
    Γ ⊢[PRAAx] le (succ (two * N) * (pw (succ M₀) (succ (two * N)) * (Q (succ M₀) L + Am N L)))
        (succ (two * N) * (pw (succ M₀) (succ (two * N)) * Ap N L) +
          succ (two * N) * (N * (fact L * pw (succ M₀) (two * N))) + fact L * pw (succ M₀) (succ (two * N))) ⋏
      le (succ (two * N) * (pw (succ M₀) (succ (two * N)) * Ap N L))
        (succ (two * N) * (pw (succ M₀) (succ (two * N)) * (Q (succ M₀) L + Am N L)) +
          succ (two * N) * (N * (fact L * pw (succ M₀) (two * N))) + fact L * pw (succ M₀) (succ (two * N))) := by
  have i := inv (N := N) hM hN
  have i1 := natEq (eq_add_of_le (Prf.andE₁ i)); have i2 := natEq (eq_add_of_le (Prf.andE₂ i))
  refine .andI (le_of_eq_add (d := succ (two * N) * monus (Xm N (succ M₀) L + N * (fact L * pw (succ M₀) (two * N)))
        (Xp N (succ M₀) L) + succ (two * N) * (two * (par N * U N (succ M₀) L)) +
      monus (fact L * pw (succ M₀) (succ (two * N))) (succ (two * N) * U N (succ M₀) L)) ?_)
    (le_of_eq_add (d := succ (two * N) * monus (Xp N (succ M₀) L + N * (fact L * pw (succ M₀) (two * N)))
        (Xm N (succ M₀) L) + succ (two * N) * (two * (monus one (par N) * U N (succ M₀) L)) +
      monus (fact L * pw (succ M₀) (succ (two * N))) (succ (two * N) * U N (succ M₀) L)) ?_)
  · ipra_lc (2 * 𝔞 N + 1) * i1 + natEq (eq_add_of_le (U_bound (N := N) hM)) -
      (2 * 𝔞 N + 1) * 𝔞 (U N (succ M₀) L) * natEq (par_sum (Γ := Γ) N)
  · ipra_lc (2 * 𝔞 N + 1) * i2 + natEq (eq_add_of_le (U_bound (N := N) hM)) -
      (2 * 𝔞 N + 1) * 𝔞 (U N (succ M₀) L) * natEq (par_sum (Γ := Γ) N)

end LeanProofs.IPRA.Analysis.BaselQuadrature
