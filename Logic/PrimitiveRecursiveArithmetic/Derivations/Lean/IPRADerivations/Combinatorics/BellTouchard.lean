import IPRADerivations.Combinatorics.BellSpivey
import IPRADerivations.Combinatorics.BellStirling
import IPRADerivations.AnalyticNumberTheory.Fermat
import IPRADerivations.Combinatorics.LegendreFact
import IPRADerivations.Combinatorics.FallingFactorial
import IPRADerivations.Core.SumSplit
import IPRADerivations.AnalyticNumberTheory.ValuationMul

/-!
# Touchard's congruence

Packet: `combinatorics/bell_numbers_ipra`, `paper/04_congruences.tex`, Theorem `thm:touchard`:
for a prime `p`, `B_{n+p} ≡ B_{n+1} + B_n (mod p)`.

* `weighted_stirling`: `∑_{k ≤ n} k S(n, k) + B_n = B_{n+1}`, from the Stirling recurrence and
  `B_n = ∑_k S(n, k)`;
* `spivey_prime`, `touchard_pre`: Spivey's identity `B_{p+n} = ∑_j S(n, j) ∑_k C(p, k) j^{p−k} B_k`,
  with `p ∣ C(p, k)` for `0 < k < p` and Fermat's `j^p ≡ j`, gives
  `B_{p+n} + B_n ≡ B_{n+1} + B_p B_n (mod p)`;
* `stir_dvd_step`, `all_viol`: `p ∣ S(p, k)` for `2 ≤ k < p`, by induction on `k`: from
  `k^p = ∑_j S(p, j) (k)_j`, Fermat, `S(p, 1) = 1`, `p ∤ k!` and Euclid's lemma;
* `bell_prime`, `bell_prime_two`: `B_p = 2 + p w`, i.e. `B_p ≡ 2 (mod p)`;
* `touchard` (`thm:touchard`): `B_{p+n} ≡ B_{n+1} + B_n (mod p)`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.BellTouchard

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.Stirling (stir stir_above stir_succ_zero stir_zero)
open LeanProofs.IPRA.Combinatorics.StirlingPowers (congrStir)
open LeanProofs.IPRA.Combinatorics.StirlingBinomial (stir_rec)
open LeanProofs.IPRA.Combinatorics.BellStirling (T bell_stirling)
open LeanProofs.IPRA.Combinatorics.Bell (bell bell_zero)
open LeanProofs.IPRA.Combinatorics.BellSpivey (gB G g_at fB f_at spivey)
open LeanProofs.IPRA.Combinatorics.Vandermonde (gb congrGb gb_zero gb_self)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open LeanProofs.IPRA.Combinatorics.BellPascalInversion (congrBell)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (prime)
open LeanProofs.IPRA.AnalyticNumberTheory.Fermat (prime_dvd_binom dvd_sum prime_shift fermat_at)
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open LeanProofs.IPRA.Combinatorics.Vandermonde (zB)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (dvd_mul' dvd_of_eq' eq_of_dvd' dvd_sub' dvd_add')
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## `∑_k k S(n, k) + B_n = B_{n+1}` -/

/-- `k S(n, k)`; variables `0 = k`, `1 = n`. -/
abbrev jB : PTm 2 := var 0 * stir (var 1) (var 0)

/-- `J(n) = ∑_{k ≤ n} k S(n, k)`. -/
abbrev J (N : PTm n) : PTm n := ap2 (sumF jB) (succ N) N

theorem inst2_j (k x : PTm n) : inst2 jB k x = k * stir x k := by simp [inst2]
theorem inst2_t (k x : PTm n) : inst2 BellStirling.tB k x = stir x k := by simp [inst2]

theorem shift_j (k x : PTm n) : inst2 (shiftBody jB) k x = succ k * stir x (succ k) := by
  rw [inst2_shiftBody, inst2_j]

theorem shift_t (k x : PTm n) : inst2 (shiftBody BellStirling.tB) k x = stir x (succ k) := by
  rw [inst2_shiftBody, inst2_t]

theorem weighted_stirling (N : PTm n) : Γ ⊢[PRAAx] J N + bell N ≐ bell (succ N) := by
  -- `T(N + 1) = S(N + 1, 0) + ∑_{k ≤ N} S(N + 1, k + 1)`
  have a1 := sum_shift (Γ := Γ) BellStirling.tB (succ N) (succ N)
  rw [inst2_t] at a1
  -- `∑_{k ≤ N} S(N + 1, k + 1) = ∑_{k ≤ N} ((k + 1) S(N, k + 1) + S(N, k))`
  have a2 : Γ ⊢[PRAAx] ap2 (sumF (shiftBody BellStirling.tB)) (succ N) (succ N) ≐
      ap2 (sumF (addBody (shiftBody jB) BellStirling.tB)) (succ N) N := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    have e1 : Syn.shift (succ N) = succ (Syn.shift N) := by simp [Syn.shift]
    rw [e1, shift_t, inst2_addBody, shift_j, inst2_t]
    exact stir_rec _ _
  have a3 := sum_add (Γ := Γ) (shiftBody jB) BellStirling.tB (succ N) N
  -- `∑_{k ≤ N + 1} k S(N, k) = 0 + ∑_{k ≤ N} (k + 1) S(N, k + 1)`
  have a4 := sum_shift (Γ := Γ) jB (succ N) N
  rw [inst2_j] at a4
  have a5 := sum_succ' (Γ := Γ) jB (succ N) N
  rw [inst2_j] at a5
  have a1c := a1.eqTrans ((congrAdd (stir_succ_zero N) (.eqRefl _)).eqTrans (zero_add _))
  have a4c := a4.eqTrans ((congrAdd (zero_mul _) (.eqRefl _)).eqTrans (zero_add _))
  have a5c := a5.eqTrans ((congrAdd (.eqRefl _) ((congrMul (.eqRefl _) (stir_above (le_refl (succ N)))).eqTrans
    (mul_zero _))).eqTrans (add_zero _))
  have b0 : Γ ⊢[PRAAx] ap2 (sumF BellStirling.tB) (succ N) N ≐ bell N := bell_stirling N
  have b1 : Γ ⊢[PRAAx] ap2 (sumF BellStirling.tB) (succ (succ N)) (succ N) ≐ bell (succ N) := bell_stirling (succ N)
  have b0' := natEq b0; have b1' := natEq b1
  have a1' := natEq a1c; have a2' := natEq a2; have a3' := natEq a3; have a4' := natEq a4c; have a5' := natEq a5c
  apply deriveNat; ipra_simps
  linear_combination b1' - b0' - a1' - a2' - a3' + a4' - a5'

/-! ## Spivey's inner sum at a prime -/

/-- The middle terms `∑_{0 < k < p} C(p, k) j^{p−k} B_k`. -/
abbrev Mid (p j : PTm n) : PTm n := ap2 (sumF (shiftBody gB)) (pred p) (pairT p j)

theorem shift_pairT2 (a b : PTm n) : Syn.shift (pairT a b) = pairT (Syn.shift a) (Syn.shift b) := by
  simp [Syn.shift]

/-- `G(p, j) = j^p + Mid(p, j) + B_p`. -/
theorem G_split {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (j : PTm n) :
    Γ ⊢[PRAAx] G p j ≐ pw j p + Mid p j + bell p := by
  have hq := prime_eq_succ_pred hp
  have s1 := sum_shift (Γ := Γ) gB p (pairT p j)
  have s2 : Γ ⊢[PRAAx] ap2 (sumF (shiftBody gB)) p (pairT p j) ≐
      ap2 (sumF (shiftBody gB)) (succ (pred p)) (pairT p j) := congrAp2 _ hq (.eqRefl _)
  have s3 := sum_succ' (Γ := Γ) (shiftBody gB) (pred p) (pairT p j)
  rw [inst2_shiftBody] at s3
  have t0 : Γ ⊢[PRAAx] inst2 gB zero (pairT p j) ≐ pw j p :=
    (g_at _ _ _).eqTrans ((congrMul (congrMul (gb_zero p) (congrPw (.eqRefl j) (monus_zero p))) bell_zero).eqTrans
      (by apply deriveNat; ipra_simps; ring))
  have tq : Γ ⊢[PRAAx] inst2 gB (succ (pred p)) (pairT p j) ≐ bell p := by
    refine (g_at _ _ _).eqTrans ?_
    have g1 : Γ ⊢[PRAAx] gb p (succ (pred p)) ≐ one := (congrGb (.eqRefl p) hq.eqSymm).eqTrans (gb_self p)
    have g2 : Γ ⊢[PRAAx] pw j (monus p (succ (pred p))) ≐ one :=
      (congrPw (.eqRefl j) ((congrMonus (.eqRefl p) hq.eqSymm).eqTrans (monus_self p))).eqTrans (pw_zero _)
    refine (congrMul (congrMul g1 g2) (congrBell hq.eqSymm)).eqTrans ?_
    apply deriveNat; ipra_simps; ring
  have a := natEq s1; have b := natEq s2; have c := natEq s3; have d := natEq t0; have e := natEq tq
  apply deriveNat; ipra_simps
  linear_combination a + b + c + d + e

/-- `p ∣ Mid(p, j)`: each middle binomial coefficient is divisible by `p`. -/
theorem Mid_dvd {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (j : PTm n) : Γ ⊢[PRAAx] dvd p (Mid p j) := by
  have hq := prime_eq_succ_pred hp
  refine dvd_congr_left hq.eqSymm (dvd_sum _ (.allI (.impI ?_)))
  rw [inst2_shiftBody, shift_pairT2]
  have hp' := (prime_shift hp).wk (ψ := lt (var 0) (Syn.shift (pred p)))
  have hq' := prime_eq_succ_pred hp'
  have e : Syn.shift (pred p) = pred (Syn.shift p) := by simp [Syn.shift]
  have hb := prime_dvd_binom hp' hq' (j := var 0) (q := pred (Syn.shift p)) (by rw [← e]; exact Prf.hyp0)
  have hgb : _ ⊢[PRAAx] dvd (Syn.shift p) (gb (Syn.shift p) (succ (var 0))) :=
    dvd_congr (mul_comm _ _) (dvd_mul' hq' _ hb)
  have ht := dvd_mul' hq' (bell (succ (var 0))) (dvd_mul' hq' (pw (Syn.shift j) (monus (Syn.shift p) (succ (var 0)))) hgb)
  have hq2 := hq'
  rw [← e] at hq2
  exact dvd_congr_left hq2 (dvd_congr (g_at _ _ _).eqSymm ht)

/-! ## The Spivey sum at a prime -/

theorem divmod_p {p : PTm n} (hq : Γ ⊢[PRAAx] p ≐ succ (pred p)) (x : PTm n) :
    Γ ⊢[PRAAx] x ≐ p * quo x p + rem x p := by
  have d := natEq (Prf.andE₁ (div_mod (Γ := Γ) x (pred p)))
  have e1 := natEq (congrAp2 (Γ := Γ) quoF (.eqRefl x) hq.eqSymm)
  have e2 := natEq (congrAp2 (Γ := Γ) remF (.eqRefl x) hq.eqSymm)
  have e3 := natEq hq
  apply deriveNat; ipra_simps
  linear_combination d + e2 + (𝔞 (pred p) + 1) * e1 - 𝔞 (quo x p) * e3

/-- Fermat's little theorem as a witness equation: `j^p + p ⌊j/p⌋ = j + p ⌊j^p/p⌋`. -/
theorem fermat_witness {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (j : PTm n) :
    Γ ⊢[PRAAx] pw j p + p * quo j p ≐ j + p * quo (pw j p) p := by
  have hq := prime_eq_succ_pred hp
  have a := natEq (divmod_p hq (pw j p)); have b := natEq (divmod_p hq j)
  have f := natEq (fermat_at hp j)
  apply deriveNat; ipra_simps
  linear_combination a - b + f

/-- Bodies over `0 = j`, `1 = ⟨n, p⟩`. -/
abbrev aB : PTm 2 := stir (fstT (var 1)) (var 0) * (sndT (var 1) * quo (var 0) (sndT (var 1)))
abbrev cB : PTm 2 := stir (fstT (var 1)) (var 0) * bell (sndT (var 1))
abbrev jB2 : PTm 2 := var 0 * stir (fstT (var 1)) (var 0)
abbrev qB : PTm 2 := stir (fstT (var 1)) (var 0) *
  (sndT (var 1) * quo (pw (var 0) (sndT (var 1))) (sndT (var 1)) + Mid (sndT (var 1)) (var 0))

section At

variable (j N P : PTm n)

theorem aB_at : Γ ⊢[PRAAx] inst2 aB j (pairT N P) ≐ stir N j * (P * quo j P) := by
  have h : inst2 aB j (pairT N P) = stir (fstT (pairT N P)) j * (sndT (pairT N P) * quo j (sndT (pairT N P))) := by
    simp [inst2]
  rw [h]
  exact congrMul (congrStir (fst_pair _ _) (.eqRefl _)) (congrMul (snd_pair _ _) (congrAp2 _ (.eqRefl _) (snd_pair _ _)))

theorem cB_at : Γ ⊢[PRAAx] inst2 cB j (pairT N P) ≐ stir N j * bell P := by
  have h : inst2 cB j (pairT N P) = stir (fstT (pairT N P)) j * bell (sndT (pairT N P)) := by simp [inst2]
  rw [h]
  exact congrMul (congrStir (fst_pair _ _) (.eqRefl _)) (congrBell (snd_pair _ _))

theorem jB2_at : Γ ⊢[PRAAx] inst2 jB2 j (pairT N P) ≐ j * stir N j := by
  have h : inst2 jB2 j (pairT N P) = j * stir (fstT (pairT N P)) j := by simp [inst2]
  rw [h]
  exact congrMul (.eqRefl _) (congrStir (fst_pair _ _) (.eqRefl _))

theorem qB_at : Γ ⊢[PRAAx] inst2 qB j (pairT N P) ≐ stir N j * (P * quo (pw j P) P + Mid P j) := by
  have h : inst2 qB j (pairT N P) = stir (fstT (pairT N P)) j *
      (sndT (pairT N P) * quo (pw j (sndT (pairT N P))) (sndT (pairT N P)) + Mid (sndT (pairT N P)) j) := by
    simp [inst2]
  rw [h]
  have sp := snd_pair (Γ := Γ) N P
  refine congrMul (congrStir (fst_pair _ _) (.eqRefl _))
    (congrAdd (congrMul sp (congrAp2 _ (congrPw (.eqRefl _) sp) sp)) ?_)
  exact congrAp2 _ (congrPred sp) (LeanProofs.IPRA.congrPairT sp (.eqRefl _))

end At

/-- `B_{p+n} + X = ∑_{j ≤ n} j S(n, j) + B_p B_n + Y` with `X = ∑_j S(n, j) p ⌊j/p⌋` and
`Y = ∑_j S(n, j) (p ⌊j^p/p⌋ + Mid(p, j))`, both divisible by `p`. -/
theorem spivey_prime {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (N : PTm n) :
    Γ ⊢[PRAAx] bell (p + N) + ap2 (sumF aB) (succ N) (pairT N p) ≐
      J N + bell p * bell N + ap2 (sumF qB) (succ N) (pairT N p) := by
  have s0 := spivey (Γ := Γ) p N
  have pt : Γ ⊢[PRAAx] ap2 (sumF (addBody fB aB)) (succ N) (pairT N p) ≐
      ap2 (sumF (addBody (addBody jB2 cB) qB)) (succ N) (pairT N p) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_pairT2, inst2_addBody, inst2_addBody, inst2_addBody]
    have hp' := (prime_shift hp).wk (ψ := lt (var 0) (Syn.shift (succ N)))
    have g := natEq (congrMul (.eqRefl (stir (Syn.shift N) (var 0))) (G_split hp' (var 0)))
    have fw := natEq (congrMul (.eqRefl (stir (Syn.shift N) (var 0))) (fermat_witness hp' (var 0)))
    have f1 := natEq (f_at (Γ := lt (var 0) (Syn.shift (succ N)) :: Γ.map Fm.shift) (var 0) (Syn.shift N) (Syn.shift p))
    have a1 := natEq (aB_at (Γ := lt (var 0) (Syn.shift (succ N)) :: Γ.map Fm.shift) (var 0) (Syn.shift N) (Syn.shift p))
    have c1 := natEq (cB_at (Γ := lt (var 0) (Syn.shift (succ N)) :: Γ.map Fm.shift) (var 0) (Syn.shift N) (Syn.shift p))
    have j1 := natEq (jB2_at (Γ := lt (var 0) (Syn.shift (succ N)) :: Γ.map Fm.shift) (var 0) (Syn.shift N) (Syn.shift p))
    have q1 := natEq (qB_at (Γ := lt (var 0) (Syn.shift (succ N)) :: Γ.map Fm.shift) (var 0) (Syn.shift N) (Syn.shift p))
    apply deriveNat; ipra_simps
    linear_combination f1 + a1 - j1 - c1 - q1 + g + fw
  have s1 := sum_add (Γ := Γ) fB aB (succ N) (pairT N p)
  have s2 := sum_add (Γ := Γ) (addBody jB2 cB) qB (succ N) (pairT N p)
  have s3 := sum_add (Γ := Γ) jB2 cB (succ N) (pairT N p)
  have s4 : Γ ⊢[PRAAx] ap2 (sumF jB2) (succ N) (pairT N p) ≐ J N := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_pairT2, inst2_j]
    exact jB2_at _ _ _
  have s5 : Γ ⊢[PRAAx] ap2 (sumF cB) (succ N) (pairT N p) ≐ bell p * ap2 (sumF BellStirling.tB) (succ N) N := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_pairT2, inst2_t]
    have e : Syn.shift (bell p) = bell (Syn.shift p) := by simp [Syn.shift]
    rw [e]
    exact (cB_at _ _ _).eqTrans (mul_comm _ _)
  have s6 : Γ ⊢[PRAAx] ap2 (sumF BellStirling.tB) (succ N) N ≐ bell N := bell_stirling N
  have a := natEq s0; have b := natEq pt; have c := natEq s1; have d := natEq s2; have e := natEq s3
  have f := natEq s4; have g := natEq s5; have h := natEq s6
  apply deriveNat; ipra_simps
  linear_combination -a - c + b + d + e + f + g + 𝔞 (bell p) * h

theorem aB_dvd {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (N : PTm n) :
    Γ ⊢[PRAAx] dvd p (ap2 (sumF aB) (succ N) (pairT N p)) := by
  have hq := prime_eq_succ_pred hp
  refine dvd_congr_left hq.eqSymm (dvd_sum _ (.allI (.impI ?_)))
  rw [shift_pairT2]
  have hq' := prime_eq_succ_pred ((prime_shift hp).wk (ψ := lt (var 0) (Syn.shift (succ N))))
  have hq2 := hq'
  have e : Syn.shift (pred p) = pred (Syn.shift p) := by simp [Syn.shift]
  rw [← e] at hq2
  refine dvd_congr_left hq2 (dvd_of_eq' hq' (w := stir (Syn.shift N) (var 0) * quo (var 0) (Syn.shift p)) ?_)
  refine (aB_at _ _ _).eqTrans ?_
  apply deriveNat; ipra_simps; ring

theorem qB_dvd {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (N : PTm n) :
    Γ ⊢[PRAAx] dvd p (ap2 (sumF qB) (succ N) (pairT N p)) := by
  have hq := prime_eq_succ_pred hp
  refine dvd_congr_left hq.eqSymm (dvd_sum _ (.allI (.impI ?_)))
  rw [shift_pairT2]
  have hp' := (prime_shift hp).wk (ψ := lt (var 0) (Syn.shift (succ N)))
  have hq' := prime_eq_succ_pred hp'
  have hq2 := hq'
  have e : Syn.shift (pred p) = pred (Syn.shift p) := by simp [Syn.shift]
  rw [← e] at hq2
  have m := eq_of_dvd' hq' (Mid_dvd hp' (var 0))
  refine dvd_congr_left hq2 (dvd_of_eq' hq' (w := stir (Syn.shift N) (var 0) *
    (quo (pw (var 0) (Syn.shift p)) (Syn.shift p) + quo (Mid (Syn.shift p) (var 0)) (Syn.shift p))) ?_)
  refine (qB_at _ _ _).eqTrans ?_
  have m' := natEq (congrMul (.eqRefl (stir (Syn.shift N) (var 0))) m)
  apply deriveNat; ipra_simps
  linear_combination m'

/-- Witness form: `B_{p+N} + B_N + p x = B_{N+1} + B_p B_N + p y`. -/
theorem touchard_witness {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (N : PTm n) :
    Γ ⊢[PRAAx] bell (p + N) + bell N + p * quo (ap2 (sumF aB) (succ N) (pairT N p)) p ≐
      bell (succ N) + bell p * bell N + p * quo (ap2 (sumF qB) (succ N) (pairT N p)) p := by
  have hq := prime_eq_succ_pred hp
  have a := natEq (spivey_prime hp N); have w := natEq (weighted_stirling (Γ := Γ) N)
  have x := natEq (eq_of_dvd' hq (aB_dvd hp N)); have y := natEq (eq_of_dvd' hq (qB_dvd hp N))
  apply deriveNat; ipra_simps
  linear_combination a + w - x + y

/-- `B_{p+n} + B_n ≡ B_{n+1} + B_p B_n (mod p)`. -/
theorem touchard_pre {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (N : PTm n) :
    Γ ⊢[PRAAx] rem (bell (p + N) + bell N) p ≐ rem (bell (succ N) + bell p * bell N) p :=
  Foundations.ChineseRemainder.rem_eq_of_eq (prime_eq_succ_pred hp) (touchard_witness hp N)

/-! ## Small Stirling and factorial facts -/

theorem subst_stir {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    Syn.subst σ (stir a b) = stir (Syn.subst σ a) (Syn.subst σ b) := by
  simp [stir]

private theorem s1₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] stir (succ (var 0)) one ≐ one := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, subst_stir, Syn.subst_var, Syn.inst_zero, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ]
    refine (stir_rec zero zero).eqTrans ?_
    have a := natEq (stir_above (Γ := ([] : List (Fm PTm 0))) (le_refl (succ zero)))
    have b := natEq (stir_zero (Γ := ([] : List (Fm PTm 0))))
    apply deriveNat; ipra_simps; linear_combination a + b
  · simp only [Fm.subst_eq, subst_stir, Syn.subst_var, Syn.repl_zero, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ]
    refine (stir_rec (succ (var 0 : PTm 1)) zero).eqTrans ?_
    have a := natEq (Prf.hyp0 : [stir (succ (var 0 : PTm 1)) one ≐ one] ⊢[PRAAx] _)
    have b := natEq (stir_succ_zero (Γ := [stir (succ (var 0 : PTm 1)) one ≐ one]) (var 0))
    apply deriveNat; ipra_simps; linear_combination a + b

/-- `S(n + 1, 1) = 1`. -/
theorem stir_one (N : PTm n) : Γ ⊢[PRAAx] stir (succ N) one ≐ one := by
  have h := inst (Γ := Γ) s1₀ ![N]
  simp only [Fm.subst_eq, subst_stir, Syn.subst_var, Matrix.cons_val_zero, ConciseIPRA.PTm.subst_zero,
    ConciseIPRA.PTm.subst_succ] at h
  exact h

private theorem sd₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] stir (var 0) (var 0) ≐ one := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, subst_stir, Syn.subst_var, Syn.inst_zero, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ]
    exact stir_zero
  · simp only [Fm.subst_eq, subst_stir, Syn.subst_var, Syn.repl_zero, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ]
    refine (stir_rec (var 0 : PTm 1) (var 0)).eqTrans ?_
    have a := natEq (Prf.hyp0 : [stir (var 0 : PTm 1) (var 0) ≐ one] ⊢[PRAAx] _)
    have b := natEq (stir_above (Γ := [stir (var 0 : PTm 1) (var 0) ≐ one]) (le_refl (succ (var 0 : PTm 1))))
    apply deriveNat; ipra_simps; linear_combination a + (𝔞 (var 0 : PTm 1) + 1) * b

/-- `S(n, n) = 1`. -/
theorem stir_diag (N : PTm n) : Γ ⊢[PRAAx] stir N N ≐ one := by
  have h := inst (Γ := Γ) sd₀ ![N]
  simp only [Fm.subst_eq, subst_stir, Syn.subst_var, Matrix.cons_val_zero, ConciseIPRA.PTm.subst_zero,
    ConciseIPRA.PTm.subst_succ] at h
  exact h

/-- A prime does not divide `k!` for `k < p`: the step uses Euclid's lemma on `k! (k + 1)`. -/
theorem not_dvd_fact {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (K : PTm n) (hK : Γ ⊢[PRAAx] lt K p) :
    Γ ⊢[PRAAx] neg (dvd p (ap2 factF K zero)) := by
  have hall : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift p) ⟶ neg (dvd (Syn.shift p) (ap2 factF (var 0) zero))) := by
    refine PRA.qfInd _ ⟨lt_QF _ _, trivial, trivial⟩ ?_ ?_
    · simp only [Fm.subst_imp, subst_lt, subst_neg, Fm.subst_eq, subst_ap2, Syn.subst_var, Syn.inst_zero,
        Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero]
      have h2 : Γ ⊢[PRAAx] le two p := Prf.andE₁ hp
      refine .impI (.impI (.impE (AnalyticNumberTheory.ValuationMul.not_dvd_one h2.wk.wk) ?_))
      exact (congrAp2 remF (fact_zero _).eqSymm (.eqRefl _)).eqTrans Prf.hyp0
    · simp only [Fm.subst_imp, subst_lt, subst_neg, Fm.subst_eq, subst_ap2, Syn.subst_var, Syn.repl_zero,
        Syn.repl_succ, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ, subst_repl_shift]
      have hp' := prime_shift hp
      refine .impI (.impI ?_)
      let φ : Fm PTm (n + 1) := lt (var 0) (Syn.shift p) ⟶ neg (dvd (Syn.shift p) (ap2 factF (var 0) zero))
      let C : List (Fm PTm (n + 1)) := [dvd (Syn.shift p) (ap2 factF (succ (var 0)) zero),
        lt (succ (var 0)) (Syn.shift p), φ] ++ Γ.map Fm.shift
      have hpc : C ⊢[PRAAx] prime (Syn.shift p) := hp'.wk.wk.wk
      have hlt : C ⊢[PRAAx] lt (succ (var 0)) (Syn.shift p) := Prf.hyp1
      have ih : C ⊢[PRAAx] φ := Prf.hyp1.wk
      have d : C ⊢[PRAAx] dvd (Syn.shift p) (ap2 factF (var 0) zero * succ (var 0)) :=
        (congrAp2 remF (fact_succ _ _).eqSymm (.eqRefl _)).eqTrans Prf.hyp0
      refine .orE (euclid_lemma_at hpc d) ?_ ?_
      · exact .impE (.impE ih.wk (le_trans (le_succ_self _) hlt.wk)) Prf.hyp0
      · have l := DiophantineNumberTheory.Coprime.dvd_le' (prime_eq_succ_pred hpc.wk) Prf.hyp0
          (congrSucc (pred_succ (var 0)).eqSymm)
        exact lt_irrefl _ _ (le_trans hlt.wk l)
  have i := Prf.allE K hall
  simp only [Fm.subst_imp, subst_lt, subst_neg, Fm.subst_eq, subst_ap2, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero] at i
  exact .impE i hK

/-! ## `p ∣ S(p, k)` for `2 ≤ k < p` -/

/-- `rem(S(p, i + 2), p)`; variables `0 = i`, `1 = p`. -/
abbrev rvB : PTm 2 := rem (stir (var 1) (succ (succ (var 0)))) (var 1)

theorem inst2_rv (i P : PTm n) : inst2 rvB i P = rem (stir P (succ (succ i))) P := by simp [inst2]

/-- `S(p, k) (k)_j`-bodies at `⟨p, K⟩`. -/
theorem tB_at' (j P K : PTm n) :
    Γ ⊢[PRAAx] inst2 StirlingPowers.tB j (pairT P K) ≐ stir P j * StirlingPowers.ff K j :=
  StirlingPowers.tB_at j P K

/-- The step: if `p ∣ S(p, i + 2)` for all `i < K₂` and `K₂ + 2 < p`, then `p ∣ S(p, K₂ + 2)`. -/
theorem stir_dvd_step {p K2 : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hK : Γ ⊢[PRAAx] lt (succ (succ K2)) p)
    (ih : Γ ⊢[PRAAx] ap2 (sumF rvB) K2 p ≐ zero) : Γ ⊢[PRAAx] dvd p (stir p (succ (succ K2))) := by
  have hq := prime_eq_succ_pred hp
  -- `K^p = ∑_{j ≤ p} S(p, j) (K)_j`, and the terms with `j > K` vanish
  have pw1 := StirlingPowers.stirling_powers (Γ := Γ) p (succ (succ K2))
  have eD : Γ ⊢[PRAAx] succ p ≐ succ (succ (succ K2)) + monus p (succ (succ K2)) := by
    have e := natEq (eq_add_of_le (le_of_lt hK))
    apply deriveNat; ipra_simps; linear_combination e
  have tail : Γ ⊢[PRAAx] ap2 (sumF (offB StirlingPowers.tB)) (monus p (succ (succ K2)))
      (pairT (succ (succ (succ K2))) (pairT p (succ (succ K2)))) ≐ zero := by
    refine (sum_congr_bounded (offB StirlingPowers.tB) Vandermonde.zB
      (pairT (succ (succ (succ K2))) (pairT p (succ (succ K2))))
      (pairT (succ (succ (succ K2))) (pairT p (succ (succ K2)))) _ (.allI (.impI ?_))).eqTrans (Vandermonde.zsum _ _)
    rw [shift_pairT2, shift_pairT2, Vandermonde.inst2_z, inst2_offB]
    refine (congrInst2 _ (congrAdd (fst_pair _ _) (.eqRefl _)) (snd_pair _ _)).eqTrans ((tB_at' _ _ _).eqTrans ?_)
    refine (congrMul (.eqRefl _) (StirlingPowers.ff_zero_above ?_)).eqTrans (mul_zero _)
    have e3 : Syn.shift (succ (succ (succ K2))) = succ (Syn.shift (succ (succ K2))) := by simp [Syn.shift]
    rw [e3]
    exact le_add_right _ _
  have whole : Γ ⊢[PRAAx] ap2 (sumF StirlingPowers.tB) (succ p) (pairT p (succ (succ K2))) ≐
      ap2 (sumF StirlingPowers.tB) (succ (succ (succ K2))) (pairT p (succ (succ K2))) :=
    (congrAp2 _ eD (.eqRefl _)).eqTrans ((sum_split _ _ _ _).eqTrans ((congrAdd (.eqRefl _) tail).eqTrans (add_zero _)))
  -- `∑_{j ≤ K} = term 0 + term 1 + ∑_{i < K₂} term (i + 2) + term K`
  have c1 := sum_shift (Γ := Γ) StirlingPowers.tB (succ (succ K2)) (pairT p (succ (succ K2)))
  have c2 := sum_shift (Γ := Γ) (shiftBody StirlingPowers.tB) (succ K2) (pairT p (succ (succ K2)))
  have c3 := sum_succ' (Γ := Γ) (shiftBody (shiftBody StirlingPowers.tB)) K2 (pairT p (succ (succ K2)))
  rw [inst2_shiftBody] at c2
  rw [inst2_shiftBody, inst2_shiftBody] at c3
  have t0 : Γ ⊢[PRAAx] inst2 StirlingPowers.tB zero (pairT p (succ (succ K2))) ≐ zero :=
    (tB_at' _ _ _).eqTrans ((congrMul ((congrStir hq (.eqRefl _)).eqTrans (stir_succ_zero _)) (.eqRefl _)).eqTrans
      (zero_mul _))
  have t1 : Γ ⊢[PRAAx] inst2 StirlingPowers.tB (succ zero) (pairT p (succ (succ K2))) ≐ succ (succ K2) :=
    (tB_at' _ _ _).eqTrans ((congrMul ((congrStir hq (.eqRefl _)).eqTrans (stir_one _))
      (FallingFactorial.ff_one _)).eqTrans (one_mul _))
  have tK : Γ ⊢[PRAAx] inst2 StirlingPowers.tB (succ (succ K2)) (pairT p (succ (succ K2))) ≐
      stir p (succ (succ K2)) * ap2 factF (succ (succ K2)) zero :=
    (tB_at' _ _ _).eqTrans (congrMul (.eqRefl _) (FallingFactorial.ff_self _))
  -- the middle terms are divisible by `p`
  have ih' : Γ.map Fm.shift ⊢[PRAAx] ap2 (sumF rvB) (Syn.shift K2) (Syn.shift p) ≐ zero := by
    simpa [Fm.shift, Syn.shift] using ih.shift
  have mid : Γ ⊢[PRAAx] dvd p (ap2 (sumF (shiftBody (shiftBody StirlingPowers.tB))) K2 (pairT p (succ (succ K2)))) := by
    refine dvd_congr_left hq.eqSymm (dvd_sum _ (.allI (.impI ?_)))
    rw [inst2_shiftBody, inst2_shiftBody, shift_pairT2]
    have z := sum_zero_elim rvB (ih'.wk (ψ := lt (var 0) (Syn.shift K2))) Prf.hyp0
    rw [inst2_rv] at z
    have hq' := prime_eq_succ_pred ((prime_shift hp).wk (ψ := lt (var 0) (Syn.shift K2)))
    have hq2 := hq'
    have e : Syn.shift (pred p) = pred (Syn.shift p) := by simp [Syn.shift]
    rw [← e] at hq2
    exact dvd_congr_left hq2 (dvd_congr (tB_at' _ _ _).eqSymm (dvd_mul' hq' _ z))
  -- Fermat: `K^p ≡ K`, hence `p ∣ S(p, K) K!`
  have fw := natEq (fermat_witness hp (succ (succ K2)))
  have m := natEq (eq_of_dvd' hq mid)
  have a1 := natEq pw1; have a2 := natEq whole; have a3 := natEq c1; have a4 := natEq c2; have a5 := natEq c3
  have b0 := natEq t0; have b1 := natEq t1; have bK := natEq tK
  have key : Γ ⊢[PRAAx] dvd p (stir p (succ (succ K2)) * ap2 factF (succ (succ K2)) zero +
      (p * quo (ap2 (sumF (shiftBody (shiftBody StirlingPowers.tB))) K2 (pairT p (succ (succ K2)))) p +
        p * quo (succ (succ K2)) p)) := by
    refine dvd_of_eq' hq (w := quo (pw (succ (succ K2)) p) p) ?_
    apply deriveNat; ipra_simps
    linear_combination fw - m - b0 - b1 - bK - a5 - a4 - a3 - a2 + a1
  have hsk : Γ ⊢[PRAAx] dvd p (stir p (succ (succ K2)) * ap2 factF (succ (succ K2)) zero) :=
    dvd_sub' hq key (dvd_add' hq (dvd_of_eq' hq (.eqRefl _)) (dvd_of_eq' hq (.eqRefl _)))
  exact .orE (euclid_lemma_at hp hsk) Prf.hyp0 (.botE _ (.impE (not_dvd_fact hp _ hK).wk Prf.hyp0))

/-- `p ∣ S(p, i + 2)` for all `i < K₂` whenever `K₂ + 2 ≤ p`, by induction on `K₂`. -/
theorem all_viol {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) {K2 : PTm n} (h : Γ ⊢[PRAAx] le (succ (succ K2)) p) :
    Γ ⊢[PRAAx] ap2 (sumF rvB) K2 p ≐ zero := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (succ (succ (var 0))) (Syn.shift p) ⟶
      ap2 (sumF rvB) (var 0) (Syn.shift p) ≐ zero) := by
    refine PRA.qfInd _ ⟨le_QF _ _, trivial⟩ ?_ ?_
    · simp only [Fm.subst_imp, subst_le, Fm.subst_eq, subst_ap2, Syn.subst_var, Syn.inst_zero,
        Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      exact .impI (sum_zero _ _)
    · simp only [Fm.subst_imp, subst_le, Fm.subst_eq, subst_ap2, Syn.subst_var, Syn.repl_zero,
        ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ, subst_repl_shift]
      refine .impI ?_
      let C : List (Fm PTm (n + 1)) := [le (succ (succ (succ (var 0)))) (Syn.shift p),
          le (succ (succ (var 0))) (Syn.shift p) ⟶ ap2 (sumF rvB) (var 0) (Syn.shift p) ≐ zero] ++ Γ.map Fm.shift
      have hp' : C ⊢[PRAAx] prime (Syn.shift p) := (prime_shift hp).wk.wk
      have ih : C ⊢[PRAAx] ap2 (sumF rvB) (var 0) (Syn.shift p) ≐ zero :=
        Prf.impE Prf.hyp1 (le_trans (le_succ_self (succ (succ (var 0)))) Prf.hyp0)
      have st := stir_dvd_step hp' Prf.hyp0 ih
      refine (sum_succ' _ _ _).eqTrans ((congrAdd ih ?_).eqTrans (add_zero _))
      rw [inst2_rv]; exact st
  have i := Prf.allE K2 hall
  simp only [Fm.subst_imp, subst_le, Fm.subst_eq, subst_ap2, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at i
  exact .impE i h

/-! ## `B_p ≡ 2` and Touchard's congruence -/

/-- `B_p = 2 + p w`: in `B_p = ∑_k S(p, k)`, `S(p, 0) = 0`, `S(p, 1) = S(p, p) = 1`, and the other terms are
divisible by `p`. -/
theorem bell_prime {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) :
    Γ ⊢[PRAAx] bell p ≐ two + p * quo (ap2 (sumF (shiftBody (shiftBody BellStirling.tB))) (monus p two) p) p := by
  have hq := prime_eq_succ_pred hp
  have h2 : Γ ⊢[PRAAx] le two p := Prf.andE₁ hp
  have e2 : Γ ⊢[PRAAx] p ≐ succ (succ (monus p two)) := by
    have e := natEq (eq_add_of_le h2)
    apply deriveNat; ipra_simps; linear_combination e
  have b : Γ ⊢[PRAAx] ap2 (sumF BellStirling.tB) (succ p) p ≐ bell p := bell_stirling p
  have cg : Γ ⊢[PRAAx] ap2 (sumF BellStirling.tB) (succ p) p ≐
      ap2 (sumF BellStirling.tB) (succ (succ (succ (monus p two)))) p := congrAp2 _ (congrSucc e2) (.eqRefl _)
  have c1 := sum_shift (Γ := Γ) BellStirling.tB (succ (succ (monus p two))) p
  have c2 := sum_shift (Γ := Γ) (shiftBody BellStirling.tB) (succ (monus p two)) p
  have c3 := sum_succ' (Γ := Γ) (shiftBody (shiftBody BellStirling.tB)) (monus p two) p
  rw [inst2_t] at c1
  rw [inst2_shiftBody, inst2_t] at c2
  rw [inst2_shiftBody, inst2_shiftBody, inst2_t] at c3
  have t0 : Γ ⊢[PRAAx] stir p zero ≐ zero := (congrStir e2 (.eqRefl _)).eqTrans (stir_succ_zero _)
  have t1 : Γ ⊢[PRAAx] stir p (succ zero) ≐ one := (congrStir e2 (.eqRefl _)).eqTrans (stir_one _)
  have tp : Γ ⊢[PRAAx] stir p (succ (succ (monus p two))) ≐ one :=
    (congrStir (.eqRefl _) e2.eqSymm).eqTrans (stir_diag p)
  have viol := all_viol hp (K2 := monus p two) (le_congr e2 (.eqRefl _) (le_refl p))
  have viol' : Γ.map Fm.shift ⊢[PRAAx] ap2 (sumF rvB) (Syn.shift (monus p two)) (Syn.shift p) ≐ zero := by
    simpa [Fm.shift, Syn.shift] using viol.shift
  have mid : Γ ⊢[PRAAx] dvd p (ap2 (sumF (shiftBody (shiftBody BellStirling.tB))) (monus p two) p) := by
    refine dvd_congr_left hq.eqSymm (dvd_sum _ (.allI (.impI ?_)))
    rw [inst2_shiftBody, inst2_shiftBody, inst2_t]
    have z := sum_zero_elim rvB (viol'.wk (ψ := lt (var 0) (Syn.shift (monus p two)))) Prf.hyp0
    rw [inst2_rv] at z
    have hq' := prime_eq_succ_pred ((prime_shift hp).wk (ψ := lt (var 0) (Syn.shift (monus p two))))
    have hq2 := hq'
    have e : Syn.shift (pred p) = pred (Syn.shift p) := by simp [Syn.shift]
    rw [← e] at hq2
    exact dvd_congr_left hq2 z
  have m := natEq (eq_of_dvd' hq mid)
  have a := natEq b; have a0 := natEq cg; have a1 := natEq c1; have a2 := natEq c2; have a3 := natEq c3
  have u0 := natEq t0; have u1 := natEq t1; have up := natEq tp
  apply deriveNat; ipra_simps
  linear_combination -a + a0 + a1 + a2 + a3 + u0 + u1 + up + m

/-- `thm:touchard`: `B_{p+n} ≡ B_{n+1} + B_n (mod p)` for a prime `p`. -/
theorem touchard {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (N : PTm n) :
    Γ ⊢[PRAAx] rem (bell (p + N)) p ≐ rem (bell (succ N) + bell N) p := by
  have hq := prime_eq_succ_pred hp
  refine Foundations.ChineseRemainder.rem_eq_of_eq hq
    (k₁ := quo (ap2 (sumF aB) (succ N) (pairT N p)) p)
    (k₂ := quo (ap2 (sumF qB) (succ N) (pairT N p)) p +
      quo (ap2 (sumF (shiftBody (shiftBody BellStirling.tB))) (monus p two) p) p * bell N) ?_
  have tw := natEq (touchard_witness hp N); have bp := natEq (bell_prime hp)
  apply deriveNat; ipra_simps
  linear_combination tw + 𝔞 (bell N) * bp

/-- `thm:touchard`, in particular `B_p ≡ 2 (mod p)`. -/
theorem bell_prime_two {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) : Γ ⊢[PRAAx] rem (bell p) p ≐ rem two p :=
  Foundations.ChineseRemainder.rem_eq_of_eq (prime_eq_succ_pred hp) (k₁ := zero)
    (k₂ := quo (ap2 (sumF (shiftBody (shiftBody BellStirling.tB))) (monus p two) p) p)
    (by have b := natEq (bell_prime hp); apply deriveNat; ipra_simps; linear_combination b)

end LeanProofs.IPRA.Combinatorics.BellTouchard
