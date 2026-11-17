import IPRADerivations.AnalyticNumberTheory.Valuation
import IPRADerivations.Core.ProdLemmas

/-!
# Legendre's formula in digit form

Packet: `catalan_numbers_ipra_2026-11-16`, `paper/05_number_theory.tex`, Lemma `lem:legendre`, the
digit identity `∑_{j≥1} ⌊m/p^j⌋ = (m − s_p(m))/(p − 1)`, multiplied by `p − 1`. With
`Q_j = ⌊m/p^j⌋` and the base-`p` digits `d_j = Q_j mod p`:

* `dm`, `dmu`: division with remainder by any positive `K`, and its uniqueness;
* `quo_quo`: `⌊⌊m/a⌋/b⌋ = ⌊m/(ab)⌋` for `a, b ≥ 1` (reusable);
* `quo_small`: `⌊z/K⌋ = 0` for `z < K`;
* `digit_step`: `Q_j = p Q_{j+1} + d_j`;
* `telescope`: `∑_{j<K} d_j + (p − 1) ∑_{j<K} Q_{j+1} + Q_K = m` for every `K`;
* `legendre_digits` (`lem:legendre`, digit form): for `p ≥ 2`,
  `s_p(m) + (p − 1) ∑_{j=1}^{m} ⌊m/p^j⌋ = m` with `s_p(m) = ∑_{j<m} d_j`, since `Q_m = 0`.

The identification `v_p(m!) = ∑_{j≥1} ⌊m/p^j⌋` and the Catalan valuation theorem are not
formalized.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.LegendreDigits

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (lt_pw pw_pos')
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Division by a positive modulus -/

theorem dm {K : PTm n} (hK : Γ ⊢[PRAAx] K ≐ succ (pred K)) (z : PTm n) :
    Γ ⊢[PRAAx] (z ≐ K * quo z K + rem z K) ⋏ lt (rem z K) K := by
  have d := div_mod (Γ := Γ) z (pred K)
  have q : Γ ⊢[PRAAx] quo z (succ (pred K)) ≐ quo z K := congrAp2 quoF (.eqRefl _) hK.eqSymm
  have r : Γ ⊢[PRAAx] rem z (succ (pred K)) ≐ rem z K := congrAp2 remF (.eqRefl _) hK.eqSymm
  exact .andI ((Prf.andE₁ d).eqTrans (congrAdd (congrMul hK.eqSymm q) r))
    (lt_congr r hK.eqSymm (Prf.andE₂ d))

theorem dmu {K z q r : PTm n} (hK : Γ ⊢[PRAAx] K ≐ succ (pred K)) (hz : Γ ⊢[PRAAx] z ≐ K * q + r)
    (hr : Γ ⊢[PRAAx] lt r K) : Γ ⊢[PRAAx] (quo z K ≐ q) ⋏ (rem z K ≐ r) := by
  have u := div_mod_unique (K' := pred K) (hz.eqTrans (congrAdd (congrMul hK (.eqRefl _)) (.eqRefl _)))
    (lt_congr (.eqRefl _) hK hr)
  exact .andI ((congrAp2 quoF (.eqRefl _) hK).eqTrans (Prf.andE₁ u))
    ((congrAp2 remF (.eqRefl _) hK).eqTrans (Prf.andE₂ u))

theorem pos_mul' {a b : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (hb : Γ ⊢[PRAAx] b ≐ succ (pred b)) :
    Γ ⊢[PRAAx] a * b ≐ succ (pred (a * b)) :=
  pos_of_eq_succ (c := pred a * succ (pred b) + pred b) ((congrMul ha hb).eqTrans (by apply deriveNat; ipra_simps; ring))

/-- `⌊⌊m/a⌋/b⌋ = ⌊m/(ab)⌋` for `a, b ≥ 1`. -/
theorem quo_quo {a b : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (hb : Γ ⊢[PRAAx] b ≐ succ (pred b)) (m : PTm n) :
    Γ ⊢[PRAAx] quo (quo m a) b ≐ quo m (a * b) := by
  have d₁ := dm ha m; have d₂ := dm hb (quo m a)
  have e₁ := natEq (Prf.andE₁ d₁); have e₂ := natEq (Prf.andE₁ d₂)
  -- the remainder `a r₂ + r₁ < a b`
  have hr₁ : Γ ⊢[PRAAx] le (succ (rem m a)) a := Prf.andE₂ d₁
  have hr₂ : Γ ⊢[PRAAx] le (succ (rem (quo m a) b)) b := Prf.andE₂ d₂
  have f₁ := natEq (eq_add_of_le hr₁); have f₂ := natEq (eq_add_of_le hr₂)
  have lt₁ : Γ ⊢[PRAAx] lt (a * rem (quo m a) b + rem m a) (a * b) := by
    refine le_of_eq_add (d := monus a (succ (rem m a)) + a * monus b (succ (rem (quo m a) b))) ?_
    apply deriveNat; ipra_simps
    linear_combination f₁ + 𝔞 a * f₂
  refine (Prf.andE₁ (dmu (pos_mul' ha hb) ?_ lt₁)).eqSymm
  apply deriveNat; ipra_simps
  linear_combination e₁ + 𝔞 a * e₂

/-- `⌊z/K⌋ = 0` for `z < K`. -/
theorem quo_small {K z : PTm n} (hK : Γ ⊢[PRAAx] K ≐ succ (pred K)) (h : Γ ⊢[PRAAx] lt z K) :
    Γ ⊢[PRAAx] quo z K ≐ zero :=
  Prf.andE₁ (dmu hK (by apply deriveNat; ipra_simps; ring) h)

/-! ## Digits -/

section Digits

/-- `Q_j = ⌊m/p^j⌋`, over `0 = j`, `1 = ⟨p, m⟩`. -/
abbrev qB : PTm 2 := quo (sndT (var 1)) (pw (fstT (var 1)) (var 0))
/-- `Q_{j+1}`. -/
abbrev qB' : PTm 2 := quo (sndT (var 1)) (pw (fstT (var 1)) (succ (var 0)))
/-- `d_j = Q_j mod p`. -/
abbrev dB : PTm 2 := rem (quo (sndT (var 1)) (pw (fstT (var 1)) (var 0))) (fstT (var 1))

theorem qB_at (j p m : PTm n) : Γ ⊢[PRAAx] inst2 qB j (pairT p m) ≐ quo m (pw p j) := by
  have e : inst2 qB j (pairT p m) = quo (sndT (pairT p m)) (pw (fstT (pairT p m)) j) := by simp [inst2]
  rw [e]; exact congrAp2 quoF (snd_pair _ _) (LeanProofs.IPRA.Combinatorics.BinomialTheorem.congrPw (fst_pair _ _) (.eqRefl _))

theorem qB'_at (j p m : PTm n) : Γ ⊢[PRAAx] inst2 qB' j (pairT p m) ≐ quo m (pw p (succ j)) := by
  have e : inst2 qB' j (pairT p m) = quo (sndT (pairT p m)) (pw (fstT (pairT p m)) (succ j)) := by simp [inst2]
  rw [e]; exact congrAp2 quoF (snd_pair _ _) (LeanProofs.IPRA.Combinatorics.BinomialTheorem.congrPw (fst_pair _ _) (.eqRefl _))

theorem dB_at (j p m : PTm n) : Γ ⊢[PRAAx] inst2 dB j (pairT p m) ≐ rem (quo m (pw p j)) p := by
  have e : inst2 dB j (pairT p m) = rem (quo (sndT (pairT p m)) (pw (fstT (pairT p m)) j)) (fstT (pairT p m)) := by
    simp [inst2]
  rw [e]
  exact congrAp2 remF (congrAp2 quoF (snd_pair _ _)
    (LeanProofs.IPRA.Combinatorics.BinomialTheorem.congrPw (fst_pair _ _) (.eqRefl _))) (fst_pair _ _)

/-- `Q_j = p Q_{j+1} + d_j`. -/
theorem digit_step {p : PTm n} (hp : Γ ⊢[PRAAx] p ≐ succ (pred p)) (m j : PTm n) :
    Γ ⊢[PRAAx] quo m (pw p j) ≐ p * quo m (pw p (succ j)) + rem (quo m (pw p j)) p := by
  have d := Prf.andE₁ (dm hp (quo m (pw p j)))
  have qq := quo_quo (pw_pos' hp j) hp m
  have e : Γ ⊢[PRAAx] quo m (pw p j * p) ≐ quo m (pw p (succ j)) := congrAp2 quoF (.eqRefl _) (pw_succ _ _).eqSymm
  exact d.eqTrans (congrAdd (congrMul (.eqRefl _) (qq.eqTrans e)) (.eqRefl _))

theorem tele_step {p m K : PTm n} (hp : Γ ⊢[PRAAx] p ≐ succ (pred p))
    (ih : Γ ⊢[PRAAx] ap2 (sumF dB) K (pairT p m) + monus p one * ap2 (sumF qB') K (pairT p m) + quo m (pw p K) ≐ m) :
    Γ ⊢[PRAAx] ap2 (sumF dB) (succ K) (pairT p m) + monus p one * ap2 (sumF qB') (succ K) (pairT p m) +
      quo m (pw p (succ K)) ≐ m := by
  have s₁ := (sum_succ' (Γ := Γ) dB K (pairT p m)).eqTrans (congrAdd (.eqRefl _) (dB_at K p m))
  have s₂ := (sum_succ' (Γ := Γ) qB' K (pairT p m)).eqTrans (congrAdd (.eqRefl _) (qB'_at K p m))
  have st := natEq (digit_step hp m K)
  have pp := natEq (eq_add_of_le (le_of_eq_add (d := pred p) (show Γ ⊢[PRAAx] p ≐ one + pred p from
    hp.eqTrans (by apply deriveNat; ipra_simps; ring))))
  have a := natEq s₁; have b := natEq s₂; have i := natEq ih
  apply deriveNat; ipra_simps
  linear_combination a + 𝔞 (monus p one) * b + i - st - (𝔞 (quo m (pw p (succ K)))) * pp

/-- Variables: `0 = K`, `1 = p`, `2 = m`. -/
private abbrev teleF : Fm PTm 3 :=
  (var 1 ≐ succ (pred (var 1))) ⟶
    (ap2 (sumF dB) (var 0) (pairT (var 1) (var 2)) + monus (var 1) one * ap2 (sumF qB') (var 0) (pairT (var 1) (var 2)) +
      quo (var 2) (pw (var 1) (var 0)) ≐ var 2)

private theorem tele₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] teleF := by
  refine ind _ ⟨trivial, trivial⟩ ?_ ?_
  · simp only [Fm.subst_imp, Fm.subst_eq, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, PTm.subst_monus,
      PTm.subst_pred, Syn.subst_var, Syn.inst_zero, Syn.inst_one, inst_two, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ]
    refine .impI ?_
    have z₁ := natEq (sum_zero (Γ := [(var 0 : PTm 2) ≐ succ (pred (var 0))]) dB (pairT (var 0) (var 1)))
    have z₂ := natEq (sum_zero (Γ := [(var 0 : PTm 2) ≐ succ (pred (var 0))]) qB' (pairT (var 0) (var 1)))
    have q0 := natEq ((congrAp2 quoF (.eqRefl (var 1 : PTm 2)) (pw_zero (Γ := [(var 0 : PTm 2) ≐ succ (pred (var 0))]) (var 0))).eqTrans
      (Prf.andE₁ (dmu (Γ := [(var 0 : PTm 2) ≐ succ (pred (var 0))]) (K := one) (q := var 1) (r := zero)
        (pos_of_eq_succ (c := zero) (.eqRefl _)) (by apply deriveNat; ipra_simps; ring) (le_refl one))))
    apply deriveNat; ipra_simps
    linear_combination z₁ + 𝔞 (monus (var 0 : PTm 2) one) * z₂ + q0
  · simp only [Fm.subst_imp, Fm.subst_eq, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, PTm.subst_monus,
      PTm.subst_pred, Syn.subst_var, Syn.repl_zero, repl_one, repl_two, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ]
    exact .impI (tele_step Prf.hyp0 (.impE Prf.hyp1 Prf.hyp0))

/-- `∑_{j<K} d_j + (p − 1) ∑_{j<K} Q_{j+1} + Q_K = m`. -/
theorem telescope {p : PTm n} (hp : Γ ⊢[PRAAx] p ≐ succ (pred p)) (K m : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF dB) K (pairT p m) + monus p one * ap2 (sumF qB') K (pairT p m) + quo m (pw p K) ≐ m := by
  have h := inst (Γ := Γ) tele₀ (![K, p, m] : Fin 3 → PTm n)
  simp at h
  exact .impE h hp

/-- `lem:legendre`, digit form: for `p ≥ 2`, `s_p(m) + (p − 1) ∑_{j=1}^{m} ⌊m/p^j⌋ = m`. -/
theorem legendre_digits {p : PTm n} (hp : Γ ⊢[PRAAx] le two p) (m : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF dB) m (pairT p m) + monus p one * ap2 (sumF qB') m (pairT p m) ≐ m := by
  have pos : Γ ⊢[PRAAx] p ≐ succ (pred p) := by
    have e := natEq (eq_add_of_le hp)
    exact pos_of_eq_succ (c := succ (monus p two)) (by apply deriveNat; ipra_simps; linear_combination e)
  have t := telescope pos m m
  have z := quo_small (pw_pos' pos m) (lt_pw hp m)
  exact (add_zero _).eqSymm.eqTrans ((congrAdd (.eqRefl _) z.eqSymm).eqTrans t)

end Digits

end LeanProofs.IPRA.Combinatorics.LegendreDigits
