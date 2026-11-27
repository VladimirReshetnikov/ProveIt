import IPRADerivations.AnalyticNumberTheory.Order

/-!
# A Zsigmondy-type divisibility

Packet: `analytic-number-theory/von_mangoldt_totient_ipra_2026-11-15`, Theorem `thm:order-am1`:
for `a > 1` and `m ≥ 1`, `m ∣ φ(aᵐ − 1)`.

With `N = aᵐ − 1`: `gcd(a, N) = 1` and `aᵐ ≡ 1 (mod N)`, so the order `o = ord(a, N)` satisfies
`o ≤ m` (minimality). If `o < m`, then `2 ≤ a^o < aᵐ = N + 1`, so `a^o mod N` is `a^o ≥ 2` or `0`,
never `1`. Hence `o = m`, and `m ∣ φ(N)` by `Order.order_dvd_totient`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.OrderPower

open_ipra exports
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (phi)
open LeanProofs.IPRA.AnalyticNumberTheory.Euler (rem_small N_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.Order

variable {n : ℕ} {Γ : List (Fm PTm n)}

section Main

variable {A m : PTm n} (hA : Γ ⊢[PRAAx] le two A) (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
include hA hm

omit hm in
/-- `A ≤ A^{k+1}` read at `A ≥ 2`. -/
theorem le_pw_succ (k : PTm n) : Γ ⊢[PRAAx] le A (pw A (succ k)) := by
  have hp := N_pos hA
  exact le_congr hp.eqSymm (congrPw hp.eqSymm (.eqRefl _)) (le_self_pw (pred A) k)

/-- `Aᵐ = (Aᵐ − 1) + 1`. -/
theorem pw_eq_succ : Γ ⊢[PRAAx] pw A m ≐ succ (monus (pw A m) one) := by
  have l := le_trans (le_of_lt hA) (le_congr (.eqRefl _) (congrPw (.eqRefl _) hm.eqSymm) (le_pw_succ hA (pred m)))
  exact (eq_add_of_le l).eqTrans (by ipra_ring)

theorem N_ge_one : Γ ⊢[PRAAx] monus (pw A m) one ≐ succ (pred (monus (pw A m) one)) := by
  have l := le_congr (.eqRefl _) (congrPw (.eqRefl _) hm.eqSymm) (le_trans hA (le_pw_succ hA (pred m)))
  have w' : Γ ⊢[PRAAx] pw A m ≐ succ (succ (monus (pw A m) two)) :=
    (eq_add_of_le l).eqTrans (by ipra_ring)
  exact AnalyticNumberTheory.Primes.eq_succ_pred
    ((congrMonus w' (.eqRefl one)).eqTrans ((succ_monus_succ _ _).eqTrans (monus_zero _)))

/-- `gcd(A, Aᵐ − 1) = 1`. -/
theorem gcd_A_N : Γ ⊢[PRAAx] gcd A (monus (pw A m) one) ≐ one := by
  have hAp := N_pos hA
  have hd := gcd_pos (B := monus (pw A m) one) hAp
  have hdd := gcd_dvd' (b := monus (pw A m) one) hAp
  have e₁ : Γ ⊢[PRAAx] pw A (pred m) * A ≐ pw A m := (pw_succ _ _).eqSymm.eqTrans (congrPw (.eqRefl _) hm.eqSymm)
  have dpw := dvd_congr e₁ (dvd_congr (mul_comm _ _) (dvd_mul' hd (pw A (pred m)) (Prf.andE₁ hdd)))
  have e₂ : Γ ⊢[PRAAx] pw A m ≐ one + monus (pw A m) one :=
    (pw_eq_succ hA hm).eqTrans (by ipra_ring)
  exact eq_one_of_dvd_one hd (dvd_sub' hd (dvd_congr e₂ dpw) (Prf.andE₂ hdd))

/-- `Aᵐ ≡ 1 (mod Aᵐ − 1)`. -/
theorem cong_m : Γ ⊢[PRAAx] rem (pw A m) (monus (pw A m) one) ≐ rem one (monus (pw A m) one) := by
  refine rem_eq_of_eq (N_ge_one hA hm) (k₁ := zero) (k₂ := one) ?_
  refine withEq (pw_eq_succ hA hm) fun e => ?_
  apply deriveNat; ipra_simps; rw [e]; ring

omit hA hm in
/-- `rem one N = one` and `rem N N = zero` for `N ≥ 2`. -/
theorem rem_one_small {N : PTm n} (hN : Γ ⊢[PRAAx] le two N) : Γ ⊢[PRAAx] rem one N ≐ one :=
  rem_small hN hN

omit hA hm in
theorem rem_self_eq {N : PTm n} (hN : Γ ⊢[PRAAx] le two N) : Γ ⊢[PRAAx] rem N N ≐ zero := by
  refine (rem_eq_of_eq (N_pos hN) (k₁ := zero) (k₂ := one) ?_).eqTrans (rem_small hN ?_)
  · ipra_ring
  · exact le_trans (le_succ_self _) hN

/-- The order of `A` modulo `Aᵐ − 1` is `m`. -/
theorem ord_eq : Γ ⊢[PRAAx] ord A (monus (pw A m) one) ≐ m := by
  have hNp := N_ge_one hA hm
  have hg := gcd_A_N hA hm
  have hc := cong_m hA hm
  refine le_antisymm ?_ ?_
  · -- `ord ≤ m`, by minimality.
    refine .orE (lt_or_le m (ord A (monus (pw A m) one))) ?_ Prf.hyp0
    refine .botE _ (.impE (order_minimal (a := A) hNp.wk (i := pred m) ?_) ?_)
    · have l : (lt m (ord A (monus (pw A m) one)) :: Γ) ⊢[PRAAx] le m (mu A (monus (pw A m) one)) :=
        (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
      exact le_congr hm.wk (.eqRefl _) l
    · exact (congrAp2 remF (congrPw (.eqRefl _) hm.wk.eqSymm) (.eqRefl _)).eqTrans hc.wk
  · -- `m ≤ ord`: a smaller order would give `2 ≤ A^o ≤ N` with `A^o ≡ 1`.
    refine .orE (lt_or_le (ord A (monus (pw A m) one)) m) ?_ Prf.hyp0
    refine .botE _ ?_
    have oc := (order_cong hg hNp).wk (ψ := lt (ord A (monus (pw A m) one)) m)
    have two_le := le_trans hA.wk (le_pw_succ (Γ := lt (ord A (monus (pw A m) one)) m :: Γ) hA.wk
      (mu A (monus (pw A m) one)))
    have hop := N_pos two_le
    -- `A^o < Aᵐ`.
    have w := eq_add_of_le (Prf.hyp0 : (lt (ord A (monus (pw A m) one)) m :: Γ) ⊢[PRAAx]
      le (succ (ord A (monus (pw A m) one))) m)
    have w₂ := eq_add_of_le (le_pw_succ (Γ := lt (ord A (monus (pw A m) one)) m :: Γ) hA.wk
      (monus m (succ (ord A (monus (pw A m) one)))))
    have hm' : (lt (ord A (monus (pw A m) one)) m :: Γ) ⊢[PRAAx] pw A m ≐
        pw A (ord A (monus (pw A m) one)) * pw A (succ (monus m (succ (ord A (monus (pw A m) one))))) :=
      (congrPw (.eqRefl _) (w.eqTrans (by ipra_ring))).eqTrans (pw_add _ _ _)
    have hA2 := eq_add_of_le (hA.wk (ψ := lt (ord A (monus (pw A m) one)) m))
    have ltm : (lt (ord A (monus (pw A m) one)) m :: Γ) ⊢[PRAAx]
        le (pw A (ord A (monus (pw A m) one))) (monus (pw A m) one) := by
      refine (succ_monus_succ _ _).eqSymm.eqTrans (le_congr (.eqRefl _) (pw_eq_succ hA.wk hm.wk) ?_)
      refine le_of_eq_add (d := pred (pw A (ord A (monus (pw A m) one))) +
        (monus A two + monus (pw A (succ (monus m (succ (ord A (monus (pw A m) one)))))) A) *
          pw A (ord A (monus (pw A m) one))) ?_
      ipra_lc natEq hm' + Groth.ι (Q.mk _ (pw A (ord A (monus (pw A m) one)))) * (natEq w₂ + natEq hA2) + natEq hop
    refine .orE (lt_or_eq_of_le ltm) ?_ ?_
    · have hlt : (lt (pw A (ord A (monus (pw A m) one))) (monus (pw A m) one) ::
          lt (ord A (monus (pw A m) one)) m :: Γ) ⊢[PRAAx]
          lt (pw A (ord A (monus (pw A m) one))) (monus (pw A m) one) := Prf.hyp0
      have hN2 := le_trans two_le.wk (le_of_lt hlt)
      have r₁ := rem_small hN2 hlt
      have r₂ := rem_one_small hN2
      exact lt_irrefl one _ (le_congr (.eqRefl _) (r₁.eqSymm.eqTrans (oc.wk.eqTrans r₂)) two_le.wk)
    · have heq : ((pw A (ord A (monus (pw A m) one)) ≐ monus (pw A m) one) ::
          lt (ord A (monus (pw A m) one)) m :: Γ) ⊢[PRAAx]
          pw A (ord A (monus (pw A m) one)) ≐ monus (pw A m) one := Prf.hyp0
      have hN2 := le_congr (.eqRefl _) heq two_le.wk
      have r₁ := (congrAp2 remF heq (.eqRefl _)).eqTrans (rem_self_eq hN2)
      exact succ_ne_zero' _ (a := zero) ((rem_one_small hN2).eqSymm.eqTrans (oc.wk.eqSymm.eqTrans r₁))

/-- `thm:order-am1` at arbitrary terms. -/
theorem zsigmondy_at : Γ ⊢[PRAAx] dvd m (phi (monus (pw A m) one)) :=
  dvd_congr_left (ord_eq hA hm) (order_dvd_totient (gcd_A_N hA hm) (N_ge_one hA hm))

end Main

/-- `thm:order-am1`: `a ≥ 2 → m ≥ 1 → m ∣ φ(aᵐ − 1)`; variables `0 = a − 2`, `1 = m − 1`. -/
abbrev zsigmondyFormula : Fm PTm 2 :=
  dvd (succ (var 1)) (phi (monus (pw (succ (succ (var 0))) (succ (var 1))) one))

theorem zsigmondy : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 zsigmondyFormula :=
  closeUniv 2 (zsigmondy_at (le_of_eq_add (d := var 0) (by ipra_ring))
    (congrSucc (pred_succ _).eqSymm))

end LeanProofs.IPRA.AnalyticNumberTheory.OrderPower
