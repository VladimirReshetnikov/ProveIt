import IPRADerivations.Analysis.BaselQuadrature

/-!
# The independent Riemann-sum code of the Basel constant

Packet: `analysis/basel_ipra`, `paper/basel_ipra.tex`, Section `sec:riemann`, Corollary `cor:riemann`:
with `P̃_k = 4 Q_{cut(k)²}` for the Riemann-sum code `Q_M = M ∑_{i<M} 1/(M² + i²)`,
`n ≥ cut(k) → |6 S_n − P̃_k²| ≤ 2^{−k}`.

Denominators are cleared by `F = L!` with `2 cut(k)⁴ ≤ L`, `2 cut(k) + 1 ≤ L` and `n ≤ L`, as in
`BaselQuadrature` and `BaselUniform`.

* `A_bounds` (`lem:decreasing` for the weights `g_j`): `A⁻ ≤ A⁺ ≤ A⁻ + F`, i.e. `0 ≤ A_N ≤ 1`;
  `Q_le`: `Q(M) ≤ F`, i.e. `Q_M ≤ 1`.
* `quad_lin`: `prop:quadrature` with the power `M^{2N}` cancelled:
  `(2N+1) M |Q(M) − F A_N| ≤ (2N+1) N F + F M`.
* `close_aux`: at `M = N²` this is `2N |Q(N²) − F A_N| ≤ 3F` (the paper's `|4Q_{N²} − 4A_N| ≤ 6/N`).
* `sq_aux`: `N |16 Q² − 16 (F A_N)²| ≤ 48 F²`, from `Q² − A² = (Q − A)(Q + A)` and `0 ≤ Q + A ≤ 2F`.
* `riemann_dyadic`: for `N = 2^r`, `N |6 S(n) − 16 Q(N²)²| ≤ (8r + 68) F²`, with `eq:dyadic`.
* `growth'`: `16k + 124 ≤ 128 · 2^k`.
* `riemann` (`cor:riemann`): `2^k · 6 S(n) ≤ 2^k · 16 Q(cut(k)²)² + F²` and conversely.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.BaselRiemann

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.BaselQuadrature (Qb U U_zero U_bound quadrature)
open LeanProofs.IPRA.Analysis.BaselUniform (Yp Ym dyadic cut cut_eq)
open LeanProofs.IPRA.Analysis.BaselCore (Ap Am)
open LeanProofs.IPRA.Analysis.BaselSquares (S)
open LeanProofs.IPRA.Analysis.BaselAverages (quo_one')
open LeanProofs.IPRA.Analysis.BaselFinite (tB inst2_t odd_pos Dec alt_decreasing)
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (quo_anti pw2_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (eq_succ_pred)
open LeanProofs.IPRA.Analysis.Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The cleared Riemann-sum code `Q(M) = ∑_{i<M} M u_i = F Q_M` of `BaselQuadrature`. -/
abbrev Qs (M L : PTm n) : PTm n := LeanProofs.IPRA.Analysis.BaselQuadrature.Q M L

/-! ## The sizes of the two codes -/

/-- The weights `g_j = F/(2j+1)` decrease. -/
theorem dec_tB (m F : PTm n) : Γ ⊢[PRAAx] Dec tB (succ m) F := by
  refine .allI (.impI ?_)
  rw [inst2_t, inst2_t]
  refine quo_anti (odd_pos _) (le_of_eq_add (d := two) ?_)
  apply deriveNat; ipra_simps; ring

/-- `0 ≤ A_N ≤ 1` for `N ≥ 1`, cleared: `A⁻ ≤ A⁺ ≤ A⁻ + F`. -/
theorem A_bounds {N N₀ : PTm n} (L : PTm n) (hN : Γ ⊢[PRAAx] N ≐ succ N₀) :
    Γ ⊢[PRAAx] le (Am N L) (Ap N L) ⋏ le (Ap N L) (Am N L + fact L) := by
  have h := alt_decreasing tB (dec_tB (Γ := Γ) N₀ (fact L))
  rw [inst2_t] at h
  have eA : Γ ⊢[PRAAx] Ap (succ N₀) L ≐ Ap N L := congrAp2 _ hN.eqSymm (.eqRefl _)
  have eB : Γ ⊢[PRAAx] Am (succ N₀) L ≐ Am N L := congrAp2 _ hN.eqSymm (.eqRefl _)
  exact .andI (le_congr eB eA (Prf.andE₁ h)) (le_congr eA (congrAdd eB (quo_one' _)) (Prf.andE₂ h))

/-- `Q_M ≤ 1`, cleared: `Q(M) ≤ F` for `M = M₀ + 1`, `2M² ≤ L`. -/
theorem Q_le {M₀ L : PTm n} (hM : Γ ⊢[PRAAx] le (two * (succ M₀ * succ M₀)) L) :
    Γ ⊢[PRAAx] le (Qs (succ M₀) L) (fact L) := by
  have ub := natEq (eq_add_of_le (U_bound (N := zero) hM))
  have u0 := natEq (U_zero (Γ := Γ) (succ M₀) L)
  have p1 := natEq ((congrAp2 powF (congrSucc (by apply deriveNat; ipra_simps; ring :
      Γ ⊢[PRAAx] two * zero ≐ (zero : PTm n))) (.eqRefl (succ M₀))).eqTrans ((pw_succ _ _).eqTrans
    ((congrMul (pw_zero _) (.eqRefl _)).eqTrans (one_mul _))))
  refine mul_le_cancel (d' := M₀) (le_of_eq_add (d := monus (fact L * pw (succ M₀) (succ (two * zero)))
    (succ (two * zero) * U zero (succ M₀) L)) ?_)
  apply deriveNat; ipra_simps
  linear_combination ub + u0 - 𝔞 (fact L) * p1

/-! ## The quadrature comparison at `M = N²` -/

/-- Cancelling a positive common factor `P` (`P' = P M`) from a bound of the shape of `eq:quadrature`. -/
theorem lin_cancel {P P' M c x y z F : PTm n} (hP : Γ ⊢[PRAAx] P ≐ succ (pred P)) (hs : Γ ⊢[PRAAx] P' ≐ P * M)
    (h : Γ ⊢[PRAAx] le (c * (P' * x)) (c * (P' * y) + c * (z * (F * P)) + F * P')) :
    Γ ⊢[PRAAx] le (c * (M * x)) (c * (M * y) + c * (z * F) + F * M) := by
  have h1 := natEq (eq_add_of_le h); have s := natEq hs
  refine mul_le_cancel (d' := pred P) (le_congr (congrMul hP (.eqRefl _)) (congrMul hP (.eqRefl _))
    (le_of_eq_add (d := monus (c * (P' * y) + c * (z * (F * P)) + F * P') (c * (P' * x))) ?_))
  apply deriveNat; ipra_simps
  linear_combination h1 + (𝔞 c * 𝔞 x - 𝔞 c * 𝔞 y - 𝔞 F) * s

/-- `prop:quadrature` without the power `M^{2N}`: `(2N+1) M |Q(M) − F A_N| ≤ (2N+1) N F + F M`. -/
theorem quad_lin {N M₀ L : PTm n} (hM : Γ ⊢[PRAAx] le (two * (succ M₀ * succ M₀)) L)
    (hN : Γ ⊢[PRAAx] le (succ (two * N)) L) :
    Γ ⊢[PRAAx] le (succ (two * N) * (succ M₀ * (Qs (succ M₀) L + Am N L)))
        (succ (two * N) * (succ M₀ * Ap N L) + succ (two * N) * (N * fact L) + fact L * succ M₀) ⋏
      le (succ (two * N) * (succ M₀ * Ap N L))
        (succ (two * N) * (succ M₀ * (Qs (succ M₀) L + Am N L)) + succ (two * N) * (N * fact L) +
          fact L * succ M₀) := by
  have q := quadrature (N := N) hM hN
  have hp := LeanProofs.IPRA.DiophantineNumberTheory.FLTMultiples.pw_pos (Γ := Γ) M₀ (two * N)
  have hs := pw_succ (Γ := Γ) (succ M₀) (two * N)
  exact .andI (lin_cancel hp hs (Prf.andE₁ q)) (lin_cancel hp hs (Prf.andE₂ q))

/-- At `M = N²`, `N = N₀ + 1`: a bound `(2N+1) M x ≤ (2N+1) M y + (2N+1) N F + F M` gives `2N x ≤ 2N y + 3F`
(`1/N + 1/(2N+1) ≤ 3/(2N)`). -/
theorem close_aux {N N₀ M F x y : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ N₀) (hM : Γ ⊢[PRAAx] M ≐ N * N)
    (h : Γ ⊢[PRAAx] le (succ (two * N) * (M * x)) (succ (two * N) * (M * y) + succ (two * N) * (N * F) + F * M)) :
    Γ ⊢[PRAAx] le (two * N * x) (two * N * y + num 3 * F) := by
  have l := natEq (eq_add_of_le h); have nN := natEq hN; have mM := natEq hM
  have hK : Γ ⊢[PRAAx] succ (two * N) * N ≐ succ (two * (N₀ * N₀) + num 5 * N₀ + two) := by
    apply deriveNat; ipra_simps
    linear_combination (2 * 𝔞 N + 2 * 𝔞 N₀ + 3) * nN
  refine mul_le_cancel (d' := two * (N₀ * N₀) + num 5 * N₀ + two)
    (le_congr (congrMul hK (.eqRefl _)) (congrMul hK (.eqRefl _))
      (le_of_eq_add (d := two * monus (succ (two * N) * (M * y) + succ (two * N) * (N * F) + F * M)
        (succ (two * N) * (M * x)) + N * F) ?_))
  apply deriveNat; ipra_simps
  linear_combination 2 * l + 2 * ((2 * 𝔞 N + 1) * 𝔞 x - (2 * 𝔞 N + 1) * 𝔞 y - 𝔞 F) * mM

/-- From `2N |q − (a − b)| ≤ 3F`, `0 ≤ a − b ≤ F` and `q ≤ F`: `N |16 q² − 16 (a − b)²| ≤ 48 F²`. -/
theorem sq_aux {N q a b F : PTm n}
    (h1 : Γ ⊢[PRAAx] le (two * N * (q + b)) (two * N * a + num 3 * F))
    (h2 : Γ ⊢[PRAAx] le (two * N * a) (two * N * (q + b) + num 3 * F))
    (hba : Γ ⊢[PRAAx] le b a) (haF : Γ ⊢[PRAAx] le a (b + F)) (hq : Γ ⊢[PRAAx] le q F) :
    Γ ⊢[PRAAx] le (N * (num 16 * (q * q + two * (a * b)))) (N * (num 16 * (a * a + b * b)) + num 48 * (F * F)) ⋏
      le (N * (num 16 * (a * a + b * b))) (N * (num 16 * (q * q + two * (a * b))) + num 48 * (F * F)) := by
  have e1 := natEq (eq_add_of_le h1); have e2 := natEq (eq_add_of_le h2)
  have ea := natEq (eq_add_of_le hba); have eb := natEq (eq_add_of_le haF); have es := natEq (eq_add_of_le hq)
  refine .andI
    (le_of_eq_add (d := num 8 * (monus (two * N * a + num 3 * F) (two * N * (q + b)) * (q + monus a b)) +
      num 24 * (F * (monus F q + monus (b + F) a))) ?_)
    (le_of_eq_add (d := num 8 * (monus (two * N * (q + b) + num 3 * F) (two * N * a) * (q + monus a b)) +
      num 24 * (F * (monus F q + monus (b + F) a))) ?_)
  · apply deriveNat; ipra_simps
    linear_combination 8 * (𝔞 a - 𝔞 b + 𝔞 q) * e1 +
      8 * 𝔞 (monus (two * N * a + num 3 * F) (two * N * (q + b))) * ea + 24 * 𝔞 F * (es + eb)
  · apply deriveNat; ipra_simps
    linear_combination 8 * (𝔞 a - 𝔞 b + 𝔞 q) * e2 +
      8 * 𝔞 (monus (two * N * (q + b) + num 3 * F) (two * N * a)) * ea + 24 * 𝔞 F * (es + eb)

/-! ## The dyadic estimate for the Riemann-sum code -/

/-- For `N = 2^r ≤ m`, `M = N²` (`M = M₀ + 1`), `2M² ≤ L`, `2N + 1 ≤ L`, `m ≤ L`:
`N · 6 S(m) ≤ N · 16 Q(M)² + (8r + 68) F²` and conversely, i.e.
`|6 S_m − 16 Q_{N²}²| ≤ (8r + 68)/2^r`. -/
theorem riemann_dyadic {r M₀ m L : PTm n} (hm : Γ ⊢[PRAAx] le (pw two r) m)
    (hL : Γ ⊢[PRAAx] le (succ (two * pw two r)) L) (hmL : Γ ⊢[PRAAx] le m L)
    (hM : Γ ⊢[PRAAx] succ M₀ ≐ pw two r * pw two r) (hQ : Γ ⊢[PRAAx] le (two * (succ M₀ * succ M₀)) L) :
    Γ ⊢[PRAAx] le (pw two r * (num 6 * S m L))
        (pw two r * (num 16 * (Qs (succ M₀) L * Qs (succ M₀) L)) + (num 8 * r + num 68) * (fact L * fact L)) ⋏
      le (pw two r * (num 16 * (Qs (succ M₀) L * Qs (succ M₀) L)))
        (pw two r * (num 6 * S m L) + (num 8 * r + num 68) * (fact L * fact L)) := by
  have hN := pw2_pos (Γ := Γ) r
  have ql := quad_lin (N := pw two r) hQ hL
  have c1 := close_aux hN hM (Prf.andE₁ ql)
  have c2 := close_aux hN hM (Prf.andE₂ ql)
  have ab := A_bounds L hN
  have sq := sq_aux c1 c2 (Prf.andE₁ ab) (Prf.andE₂ ab) (Q_le hQ)
  have dy := dyadic hm hL hmL
  have s1 := natEq (eq_add_of_le (Prf.andE₁ sq)); have s2 := natEq (eq_add_of_le (Prf.andE₂ sq))
  have d1 := natEq (eq_add_of_le (Prf.andE₁ dy)); have d2 := natEq (eq_add_of_le (Prf.andE₂ dy))
  refine .andI
    (le_of_eq_add (d := monus (pw two r * Ym (pw two r) L + (num 8 * r + num 20) * (fact L * fact L))
        (pw two r * Yp (pw two r) m L) +
      monus (pw two r * (num 16 * (Qs (succ M₀) L * Qs (succ M₀) L + two * (Ap (pw two r) L * Am (pw two r) L))) +
          num 48 * (fact L * fact L))
        (pw two r * (num 16 * (Ap (pw two r) L * Ap (pw two r) L + Am (pw two r) L * Am (pw two r) L)))) ?_)
    (le_of_eq_add (d := monus (pw two r * Yp (pw two r) m L + (num 8 * r + num 20) * (fact L * fact L))
        (pw two r * Ym (pw two r) L) +
      monus (pw two r * (num 16 * (Ap (pw two r) L * Ap (pw two r) L + Am (pw two r) L * Am (pw two r) L)) +
          num 48 * (fact L * fact L))
        (pw two r * (num 16 * (Qs (succ M₀) L * Qs (succ M₀) L + two * (Ap (pw two r) L * Am (pw two r) L))))) ?_)
  · apply deriveNat; ipra_simps
    linear_combination d1 + s2
  · apply deriveNat; ipra_simps
    linear_combination d2 + s1

/-! ## The growth inequality -/

/-- Variable `0 = k`. -/
private abbrev growthF : Fm PTm 1 := le (num 16 * var 0 + num 124) (num 128 * pw two (var 0))

private theorem growth₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] growthF := by
  refine ind _ (le_QF _ _) ?_ ?_
  · simp only [subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, PTm.subst_num,
      Syn.subst_var, Syn.inst_zero, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    have e := natEq (pw_zero (Γ := []) (two : PTm 0))
    refine le_of_eq_add (d := num 4) ?_
    apply deriveNat; ipra_simps
    linear_combination 128 * e
  · simp only [subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, PTm.subst_num,
      Syn.subst_var, Syn.repl_zero, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    have e₁ := natEq (eq_add_of_le (Prf.hyp0 : [growthF] ⊢[PRAAx] growthF))
    have e₂ := natEq (pw_succ (Γ := [growthF]) (two : PTm 1) (var 0))
    refine le_of_eq_add (d := num 16 * var 0 + num 108 + two * monus (num 128 * pw two (var 0))
      (num 16 * var 0 + num 124)) ?_
    apply deriveNat; ipra_simps
    linear_combination 128 * e₂ + 2 * e₁

/-- `16k + 124 ≤ 128 · 2^k`. -/
theorem growth' (k : PTm n) : Γ ⊢[PRAAx] le (num 16 * k + num 124) (num 128 * pw two k) := by
  have i := inst (Γ := Γ) growth₀ (![k] : Fin 1 → PTm n)
  simp at i
  exact i

/-- `2^k (8r + 68) ≤ 2^r` for `r = 2k + 7`. -/
theorem growth_cut' (k : PTm n) :
    Γ ⊢[PRAAx] le (pw two k * (num 8 * (two * k + num 7) + num 68)) (cut k) := by
  have g := natEq (eq_add_of_le (growth' (Γ := Γ) k))
  have c := natEq (cut_eq (Γ := Γ) k)
  refine le_of_eq_add (d := pw two k * monus (num 128 * pw two k) (num 16 * k + num 124)) ?_
  apply deriveNat; ipra_simps
  linear_combination c + 𝔞 (pw two k) * g

/-! ## The independent code (`cor:riemann`) -/

/-- `cor:riemann`, cleared by `F = L!`: for `n ≥ cut(k)`, `2 cut(k) + 1 ≤ L`, `2 cut(k)⁴ ≤ L`, `n ≤ L`, with
`P̃_k = 4 Q_{cut(k)²}` (so `16 Q² = P̃_k²`), `2^k · 6 S(n) ≤ 2^k · 16 Q² + F²` and
`2^k · 16 Q² ≤ 2^k · 6 S(n) + F²`, i.e. `|6 S_n − P̃_k²| ≤ 2^{−k}`. -/
theorem riemann {k m L : PTm n} (hm : Γ ⊢[PRAAx] le (cut k) m) (hL : Γ ⊢[PRAAx] le (succ (two * cut k)) L)
    (hQ : Γ ⊢[PRAAx] le (two * (cut k * cut k * (cut k * cut k))) L) (hmL : Γ ⊢[PRAAx] le m L) :
    Γ ⊢[PRAAx] le (pw two k * (num 6 * S m L))
        (pw two k * (num 16 * (Qs (cut k * cut k) L * Qs (cut k * cut k) L)) + fact L * fact L) ⋏
      le (pw two k * (num 16 * (Qs (cut k * cut k) L * Qs (cut k * cut k) L)))
        (pw two k * (num 6 * S m L) + fact L * fact L) := by
  have hp := pw2_pos (Γ := Γ) (two * k + num 7)
  have eM : Γ ⊢[PRAAx] cut k * cut k ≐ succ (pred (cut k * cut k)) := by
    have hp' := natEq hp
    refine eq_succ_pred (y := pred (cut k) * pred (cut k) + two * pred (cut k)) ?_
    apply deriveNat; ipra_simps
    linear_combination (𝔞 (cut k) + 𝔞 (pred (cut k)) + 1) * hp'
  have hQ' : Γ ⊢[PRAAx] le (two * (succ (pred (cut k * cut k)) * succ (pred (cut k * cut k)))) L :=
    le_congr (congrMul (.eqRefl two) (congrMul eM eM)) (.eqRefl _) hQ
  have rd := riemann_dyadic (r := two * k + num 7) hm hL hmL eM.eqSymm hQ'
  have r1 := natEq (eq_add_of_le (Prf.andE₁ rd)); have r2 := natEq (eq_add_of_le (Prf.andE₂ rd))
  have gc := natEq (eq_add_of_le (growth_cut' (Γ := Γ) k))
  have qe := natEq (congrAp2 (sumF Qb) eM (congrPairT eM (.eqRefl L)))
  refine .andI
    (mul_le_cancel (d' := pred (cut k)) (le_congr (congrMul hp (.eqRefl _)) (congrMul hp (.eqRefl _))
      (le_of_eq_add (d := pw two k * monus (cut k * (num 16 * (Qs (succ (pred (cut k * cut k))) L *
            Qs (succ (pred (cut k * cut k))) L)) + (num 8 * (two * k + num 7) + num 68) * (fact L * fact L))
          (cut k * (num 6 * S m L)) +
        monus (cut k) (pw two k * (num 8 * (two * k + num 7) + num 68)) * (fact L * fact L)) ?_)))
    (mul_le_cancel (d' := pred (cut k)) (le_congr (congrMul hp (.eqRefl _)) (congrMul hp (.eqRefl _))
      (le_of_eq_add (d := pw two k * monus (cut k * (num 6 * S m L) +
            (num 8 * (two * k + num 7) + num 68) * (fact L * fact L))
          (cut k * (num 16 * (Qs (succ (pred (cut k * cut k))) L * Qs (succ (pred (cut k * cut k))) L))) +
        monus (cut k) (pw two k * (num 8 * (two * k + num 7) + num 68)) * (fact L * fact L)) ?_)))
  · apply deriveNat; ipra_simps
    linear_combination 𝔞 (pw two k) * r1 + 𝔞 (fact L) * 𝔞 (fact L) * gc +
      16 * 𝔞 (pw two k) * 𝔞 (cut k) *
        (𝔞 (Qs (cut k * cut k) L) + 𝔞 (Qs (succ (pred (cut k * cut k))) L)) * qe
  · apply deriveNat; ipra_simps
    linear_combination 𝔞 (pw two k) * r2 + 𝔞 (fact L) * 𝔞 (fact L) * gc -
      16 * 𝔞 (pw two k) * 𝔞 (cut k) *
        (𝔞 (Qs (cut k * cut k) L) + 𝔞 (Qs (succ (pred (cut k * cut k))) L)) * qe

end LeanProofs.IPRA.Analysis.BaselRiemann
