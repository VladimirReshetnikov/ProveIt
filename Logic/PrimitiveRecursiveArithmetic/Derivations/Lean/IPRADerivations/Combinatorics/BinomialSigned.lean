import IPRADerivations.Combinatorics.BinomialTheorem
import IPRADerivations.Analysis.SpecialFunctions.Hypergeometric.TerminatingSeries
import IPRADerivations.Probability.Independence

/-!
# The signed binomial theorem and the binomial specialization

Packet: `analysis/hypergeometric_ipra_2026-11-16`, Corollary `cor:binomial-termination`:
`₂F₁(−m, b; b; z) = (1 − z)^m`. By `Analysis/TerminatingSeries` the coefficients of the left side are
`(−m)_n / n! = (−1)^n C(m, n)` (the factors `(b)_n` cancel), so the content is the signed binomial
theorem `∑_{n ≤ m} (−1)^n C(m, n) z^n = (1 − z)^m`.

* `pascal_sum` (reusable): for any body `g`,
  `∑_{k ≤ m+1} C(m+1, k) g(k) = ∑_{k ≤ m} C(m, k) g(k) + ∑_{k ≤ m} C(m, k) g(k + 1)`;
* `E m z = ∑_{k ≤ m} [k even] C(m, k) z^k`, `O m z = ∑_{k ≤ m} [k odd] C(m, k) z^k`, with
  `E_{m+1} = E_m + z O_m`, `O_{m+1} = O_m + z E_m` (`E_succ`, `O_succ`);
* `(1 − z)^m` as an integer term `⟨A_m, B_m⟩` defined by `(1 − z)^0 = 1`,
  `(1 − z)^{m+1} = (1 − z)^m (1 − z)` (simultaneous recursion);
* `signed_binomial` (`cor:binomial-termination`): `E_m = A_m` and `O_m = B_m`, i.e.
  `∑_{n ≤ m} (−1)^n C(m, n) z^n = (1 − z)^m`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.BinomialSigned

open_ipra
open LeanProofs.IPRA.Combinatorics.Binomial (binom)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (binom_zero')
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrBinom congrPw)
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open LeanProofs.IPRA.Analysis.Chebyshev (ps₂)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (zero_ne_one' one_ne_zero' congrEqb')

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## A Pascal step for binomial transforms -/

/-- `g(k, snd x)`. -/
def lB (g : PTm 2) : PTm 2 := Syn.subst ![var 0, sndT (var 1)] g

theorem inst2_lB (g : PTm 2) (k x : PTm n) : inst2 (lB g) k x = inst2 g k (sndT x) := by
  simp only [inst2, lB, Syn.subst_subst]
  congr 1; funext i; fin_cases i <;> simp

/-- `C(fst x, k) g(k, snd x)`. -/
abbrev cB (g : PTm 2) : PTm 2 := binom (fstT (var 1)) (var 0) * lB g
/-- `C(fst x, k) g(k + 1, snd x)`. -/
abbrev cS (g : PTm 2) : PTm 2 := binom (fstT (var 1)) (var 0) * lB (shiftBody g)

theorem inst2_cB (g : PTm 2) (k x : PTm n) : inst2 (cB g) k x = binom (fstT x) k * inst2 g k (sndT x) := by
  rw [← inst2_lB]; simp [inst2]
theorem inst2_cS (g : PTm 2) (k x : PTm n) :
    inst2 (cS g) k x = binom (fstT x) k * inst2 g (succ k) (sndT x) := by
  rw [← inst2_shiftBody, ← inst2_lB]; simp [inst2]

theorem cB_at (g : PTm 2) (k m y : PTm n) :
    Γ ⊢[PRAAx] inst2 (cB g) k (pairT m y) ≐ binom m k * inst2 g k y :=
  BinomialTheorem.weighted_at g k m y

theorem cS_at (g : PTm 2) (k m y : PTm n) :
    Γ ⊢[PRAAx] inst2 (cS g) k (pairT m y) ≐ binom m k * inst2 g (succ k) y := by
  rw [inst2_cS]; exact congrMul (congrBinom (fst_pair _ _) (.eqRefl _)) (congrInst2 g (.eqRefl _) (snd_pair _ _))

/-- `∑_{k ≤ m+1} C(m+1, k) g(k) = ∑_{k ≤ m} C(m, k) g(k) + ∑_{k ≤ m} C(m, k) g(k + 1)`. -/
theorem pascal_sum (g : PTm 2) (m y : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (cB g)) (succ (succ m)) (pairT (succ m) y) ≐
      ap2 (sumF (cB g)) (succ m) (pairT m y) + ap2 (sumF (cS g)) (succ m) (pairT m y) :=
  BinomialTheorem.weighted_pascal_sum g m y

/-! ## Even and odd parts -/

/-- `[k even] z^k`, over `0 = k`, `1 = z`. -/
abbrev gE : PTm 2 := eqb (rem (var 0) two) zero * pw (var 1) (var 0)
/-- `[k odd] z^k`. -/
abbrev gO : PTm 2 := eqb (rem (var 0) two) one * pw (var 1) (var 0)

theorem inst2_gE (k z : PTm n) : inst2 gE k z = eqb (rem k two) zero * pw z k := by simp [inst2]
theorem inst2_gO (k z : PTm n) : inst2 gO k z = eqb (rem k two) one * pw z k := by simp [inst2]

/-- `E m z = ∑_{k ≤ m} [k even] C(m, k) z^k`. -/
abbrev E (m z : PTm n) : PTm n := ap2 (sumF (cB gE)) (succ m) (pairT m z)
/-- `O m z = ∑_{k ≤ m} [k odd] C(m, k) z^k`. -/
abbrev O (m z : PTm n) : PTm n := ap2 (sumF (cB gO)) (succ m) (pairT m z)

theorem gE_succ (k z : PTm n) : Γ ⊢[PRAAx] inst2 gE (succ k) z ≐ z * inst2 gO k z := by
  rw [inst2_gE, inst2_gO]
  ipra_lc 𝔞 (pw z (succ k)) * natEq (Prf.andE₁ (LeanProofs.IPRA.AnalyticNumberTheory.Mobius.par_succ (Γ := Γ) k)) +
    𝔞 (eqb (rem k two) one) * natEq (pw_succ (Γ := Γ) z k)

theorem gO_succ (k z : PTm n) : Γ ⊢[PRAAx] inst2 gO (succ k) z ≐ z * inst2 gE k z := by
  rw [inst2_gE, inst2_gO]
  ipra_lc 𝔞 (pw z (succ k)) * natEq (Prf.andE₂ (LeanProofs.IPRA.AnalyticNumberTheory.Mobius.par_succ (Γ := Γ) k)) +
    𝔞 (eqb (rem k two) zero) * natEq (pw_succ (Γ := Γ) z k)

theorem scale_sum (g h : PTm 2) (hs : ∀ {k : ℕ} {Δ : List (Fm PTm k)} (a w : PTm k),
    Δ ⊢[PRAAx] inst2 g (succ a) w ≐ w * inst2 h a w) (m z : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (cS g)) (succ m) (pairT m z) ≐ z * ap2 (sumF (cB h)) (succ m) (pairT m z) := by
  refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
  rw [inst2_cS, inst2_cB, shift_pairT]
  ipra_lc 𝔞 (binom (fstT (pairT (Syn.shift m) (Syn.shift z))) (var 0)) * natEq (hs (Δ := lt (var 0) (Syn.shift (succ m)) :: Γ.map Fm.shift) (var 0) (sndT (pairT (Syn.shift m) (Syn.shift z)))) +
    𝔞 (binom (fstT (pairT (Syn.shift m) (Syn.shift z))) (var 0)) * 𝔞 (inst2 h (var 0) (sndT (pairT (Syn.shift m) (Syn.shift z)))) * natEq (snd_pair (Γ := lt (var 0) (Syn.shift (succ m)) :: Γ.map Fm.shift) (Syn.shift m) (Syn.shift z))

theorem E_succ (m z : PTm n) : Γ ⊢[PRAAx] E (succ m) z ≐ E m z + z * O m z :=
  (pascal_sum gE m z).eqTrans (congrAdd (.eqRefl _) (scale_sum gE gO (fun a w => gE_succ a w) m z))

theorem O_succ (m z : PTm n) : Γ ⊢[PRAAx] O (succ m) z ≐ O m z + z * E m z :=
  (pascal_sum gO m z).eqTrans (congrAdd (.eqRefl _) (scale_sum gO gE (fun a w => gO_succ a w) m z))

theorem E_zero (z : PTm n) : Γ ⊢[PRAAx] (E zero z ≐ one) ⋏ (O zero z ≐ zero) := by
  have r0 : Γ ⊢[PRAAx] rem (zero : PTm n) two ≐ zero := rem_zero _
  have cE := natEq (cB_at (Γ := Γ) gE zero zero z); have cO := natEq (cB_at (Γ := Γ) gO zero zero z)
  rw [inst2_gE] at cE; rw [inst2_gO] at cO
  refine .andI ?_ ?_
  · ipra_lc natEq (sum_succ' (Γ := Γ) (cB gE) zero (pairT zero z)) +
      natEq (sum_zero (Γ := Γ) (cB gE) (pairT zero z)) + cE +
      𝔞 (eqb (rem (zero : PTm n) two) zero) * 𝔞 (pw z zero) * natEq (binom_zero' (Γ := Γ) (zero : PTm n)) +
      𝔞 (pw z zero) * natEq ((congrEqb' r0 (.eqRefl _)).eqTrans (eqb_of_eq (.eqRefl _)) : Γ ⊢[PRAAx] eqb (rem zero two) zero ≐ one) +
      natEq (pw_zero (Γ := Γ) z)
  · ipra_lc natEq (sum_succ' (Γ := Γ) (cB gO) zero (pairT zero z)) +
      natEq (sum_zero (Γ := Γ) (cB gO) (pairT zero z)) + cO +
      𝔞 (eqb (rem (zero : PTm n) two) one) * 𝔞 (pw z zero) * natEq (binom_zero' (Γ := Γ) (zero : PTm n)) +
      𝔞 (pw z zero) * natEq ((congrEqb' r0 (.eqRefl _)).eqTrans (eqb_of_ne zero_ne_one') : Γ ⊢[PRAAx] eqb (rem zero two) one ≐ zero)

/-! ## `(1 − z)^m` and the signed binomial theorem -/

/-- Step variables: `0 = j`, `1 = A_j`, `2 = B_j`, `3 = z`; multiplication by `1 − z`. -/
abbrev sA : PTm 4 := var 1 + var 2 * var 3
abbrev sB : PTm 4 := var 1 * var 3 + var 2

/-- `(1 − z)^j = A_j − B_j`, with `ps 0 = z`. -/
abbrev AA (j : PTm n) (ps : Fin 1 → PTm n) : PTm n := sim₁ one zero sA sB j ps
abbrev BB (j : PTm n) (ps : Fin 1 → PTm n) : PTm n := sim₂ one zero sA sB j ps

theorem AA_succ (j : PTm n) (ps : Fin 1 → PTm n) : Γ ⊢[PRAAx] AA (succ j) ps ≐ AA j ps + BB j ps * ps 0 := by
  have h := sim₁_succ (Γ := Γ) one zero sA sB ps j
  simp only [PTm.subst_add, PTm.subst_mul, Syn.subst_var, Fin.cases_zero, finCases_one, finCases_two,
    finCases_three] at h
  exact h

theorem BB_succ (j : PTm n) (ps : Fin 1 → PTm n) : Γ ⊢[PRAAx] BB (succ j) ps ≐ AA j ps * ps 0 + BB j ps := by
  have h := sim₂_succ (Γ := Γ) one zero sA sB ps j
  simp only [PTm.subst_add, PTm.subst_mul, Syn.subst_var, Fin.cases_zero, finCases_one, finCases_two,
    finCases_three] at h
  exact h

theorem bin_base (ps : Fin 1 → PTm n) :
    Γ ⊢[PRAAx] (E zero (ps 0) ≐ AA zero ps) ⋏ (O zero (ps 0) ≐ BB zero ps) := by
  have a := sim₁_zero (Γ := Γ) one zero sA sB ps
  have b := sim₂_zero (Γ := Γ) one zero sA sB ps
  simp only [ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at a b
  have z := E_zero (Γ := Γ) (ps 0)
  exact .andI ((Prf.andE₁ z).eqTrans a.eqSymm) ((Prf.andE₂ z).eqTrans b.eqSymm)

theorem bin_step {j : PTm n} {ps : Fin 1 → PTm n}
    (ih : Γ ⊢[PRAAx] (E j (ps 0) ≐ AA j ps) ⋏ (O j (ps 0) ≐ BB j ps)) :
    Γ ⊢[PRAAx] (E (succ j) (ps 0) ≐ AA (succ j) ps) ⋏ (O (succ j) (ps 0) ≐ BB (succ j) ps) := by
  have h₁ := natEq (Prf.andE₁ ih); have h₂ := natEq (Prf.andE₂ ih)
  have e₁ := natEq (E_succ (Γ := Γ) j (ps 0)); have e₂ := natEq (O_succ (Γ := Γ) j (ps 0))
  have a₁ := natEq (AA_succ (Γ := Γ) j ps); have a₂ := natEq (BB_succ (Γ := Γ) j ps)
  refine .andI ?_ ?_
  · ipra_lc e₁ - a₁ + h₁ + 𝔞 (ps 0) * h₂
  · ipra_lc e₂ - a₂ + h₂ + 𝔞 (ps 0) * h₁

/-- Variables: `0 = m`, `1 = z`. -/
private abbrev binF : Fm PTm 2 :=
  (E (var 0) (var 1) ≐ AA (var 0) ps₂) ⋏ (O (var 0) (var 1) ≐ BB (var 0) ps₂)

private theorem bin₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] binF := by
  ipra_ind (⟨trivial, trivial⟩) [subst_ap2, subst_pairT, subst_sim₁, subst_sim₂, Syn.inst_succ, Syn.repl_succ]
  · exact bin_base _
  · have s := bin_step (Γ := [binF]) (j := var 0) (ps := ps₂) Prf.hyp0
    simpa [ps₂] using s

/-- `cor:binomial-termination`: `∑_{n ≤ m} (−1)^n C(m, n) z^n = (1 − z)^m`, as `E_m = A_m` and `O_m = B_m`. -/
theorem signed_binomial (m z : PTm n) :
    Γ ⊢[PRAAx] (E m z ≐ AA m (fun _ => z)) ⋏ (O m z ≐ BB m (fun _ => z)) := by
  have i := inst (Γ := Γ) bin₀ (![m, z] : Fin 2 → PTm n)
  simpa using i

end LeanProofs.IPRA.Combinatorics.BinomialSigned
