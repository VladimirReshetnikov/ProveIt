import IPRADerivations.Combinatorics.LinearFactorTable
import IPRADerivations.Combinatorics.BellPrimePeriod

/-!
# The period `N_p` of the Bell numbers modulo a prime (`bell_numbers_ipra`, `thm:prime-period`)

Packet: `combinatorics/bell_numbers_ipra`, `paper/04_congruences.tex`, theorem
`thm:prime-period`: "For every prime `p`, let `N_p = 1 + p + ⋯ + p^{p−1} = (p^p − 1)/(p − 1)`.
Then, for all `n ≥ 0`, `B_{n+N_p} ≡ B_n (mod p)`." Proof: "In the same finite quotient ring,
`X^{N_p} = ∏_{r=0}^{p−1} X^{p^r} = ∏_{r=0}^{p−1} (X + r) = X^p − X = 1`."

The derivation follows the same computation on the sequence, with the shift `E` for `X`, in a
form that needs neither Wilson's theorem nor the factorization of `X^p − X`:

1. `tele1`: by `thm:touchard-power`, each shift by `p^{j+1}` is one factor `E + (j + 1)`, so
   `B_{n + (p + p² + ⋯ + p^p)} ≡ ((E + 1)(E + 2) ⋯ (E + p) B)_n`;
2. `tele2`: with `G(m, j) = ∑_k C(m, k) j^{m−k} B_k` of `Combinatorics/BellSpivey` (the falling
   factorial `(E)_j` applied to `B`), `G(m + 1, j) = j G(m, j) + G(m, j + 1)` gives
   `G(m, j + 1) ≡ G(m + 1, j) + (p − j) G(m, j)`: lowering `j` from `p` to `0` produces the
   same factors, so `G(n, p) ≡ ((E + 1) ⋯ (E + p) B)_n`;
3. `G_prime`: `G(n, p) ≡ B_n`, since every other term of the sum has a factor `p`;
4. `B_{m + p^p} ≡ B_{m+1}` (`BellPrimePeriod.shift_pp`) trades the shift `p^p` for the shift
   `1`, turning `p + ⋯ + p^p` into `N_p = 1 + p + ⋯ + p^{p−1}`.

* `bell_period_Np`: `rem B_{N + N_p} p = rem B_N p` for a prime `p`;
  `bell_period_Np_closed`: closed over `p` and `N`.

Not derived: the least period (which divides `N_p`) and `thm:all-moduli-period`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.BellPeriodNp

open_ipra
open LeanProofs.IPRA.Combinatorics.Bell (bell)
open LeanProofs.IPRA.Combinatorics.BellPascalInversion (congrBell)
open LeanProofs.IPRA.Combinatorics.BellSpivey (gB G g_at G_succ G_zero)
open LeanProofs.IPRA.Combinatorics.Vandermonde (gb gb_self)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open LeanProofs.IPRA.Combinatorics.BellTouchardPower (touchard_power cong_add cong_mul cong_of_eq
  monus_of_lt shift_pair shift_succ shift_add shift_mul shift_monus shift_pw)
open LeanProofs.IPRA.Combinatorics.BellPrimePeriod (cong_drop shift_pp)
open LeanProofs.IPRA.Combinatorics.LinearFactorTable (cyc actB par Act act_at act_zero act_cong
  congrAct pair_congr)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (prime)
open LeanProofs.IPRA.AnalyticNumberTheory.Fermat (dvd_sum prime_shift)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (dvd_of_eq' eq_of_dvd')

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The two sequences as bodies -/

/-- `m ↦ B_m`. -/
def bellB : PTm 2 := bell (var 0)

theorem inst2_bellB (m x : PTm n) : inst2 bellB m x = bell m := by simp [inst2, bellB]

/-- `m ↦ G(m, j)`, with the parameter `j`. -/
def gyB : PTm 2 := G (var 0) (var 1)

theorem inst2_gyB (m j : PTm n) : inst2 gyB m j = G m j := by simp [inst2, gyB]

theorem congrG {N N' j j' : PTm n} (hN : Γ ⊢[PRAAx] N ≐ N') (hj : Γ ⊢[PRAAx] j ≐ j') :
    Γ ⊢[PRAAx] G N j ≐ G N' j' :=
  congrAp2 _ (congrSucc hN) (pair_congr hN hj)

theorem shift_zero : Syn.shift (zero : PTm n) = zero := by simp [Syn.shift]

/-! ## `G(N, p) ≡ B_N (mod p)` -/

theorem term_dvd {p N k : PTm n} (hq : Γ ⊢[PRAAx] p ≐ succ (pred p)) (hk : Γ ⊢[PRAAx] lt k N) :
    Γ ⊢[PRAAx] dvd p (inst2 gB k (pairT N p)) := by
  refine dvd_of_eq' hq (w := gb N k * pw p (monus N (succ k)) * bell k) ?_
  refine (g_at k N p).eqTrans ((congrMul (congrMul (.eqRefl _)
    ((congrPw (.eqRefl p) (monus_of_lt hk)).eqTrans (pw_succ p _))) (.eqRefl _)).eqTrans ?_)
  ipra_ring

/-- `G(N, p) ≡ B_N (mod p)`: every term of `∑_k C(N, k) p^{N−k} B_k` with `k < N` has a factor
`p`. -/
theorem G_prime {p : PTm n} (hq : Γ ⊢[PRAAx] p ≐ succ (pred p)) (N : PTm n) :
    Γ ⊢[PRAAx] rem (G N p) p ≐ rem (bell N) p := by
  have s := sum_succ' (Γ := Γ) gB N (pairT N p)
  have last : Γ ⊢[PRAAx] inst2 gB N (pairT N p) ≐ bell N :=
    (g_at N N p).eqTrans ((congrMul (congrMul (gb_self N)
      ((congrPw (.eqRefl p) (monus_self N)).eqTrans (pw_zero p))) (.eqRefl _)).eqTrans
        (by ipra_ring))
  have hd : Γ ⊢[PRAAx] dvd p (ap2 (sumF gB) N (pairT N p)) := by
    refine dvd_congr_left hq.eqSymm (dvd_sum _ (.allI (.impI ?_)))
    rw [shift_pair]
    have hq' : (Γ.map Fm.shift) ⊢[PRAAx] Syn.shift p ≐ succ (pred (Syn.shift p)) := by
      simpa [Fm.shift, Syn.shift] using hq.shift
    have e : Syn.shift (pred p) = pred (Syn.shift p) := by simp [Syn.shift]
    have hq2 := hq'.wk (ψ := lt (var 0) (Syn.shift N))
    rw [← e] at hq2
    exact dvd_congr_left hq2 (term_dvd hq'.wk Prf.hyp0)
  have w := eq_of_dvd' hq hd
  have e : Γ ⊢[PRAAx] G N p ≐ bell N + p * quo (ap2 (sumF gB) N (pairT N p)) p := by
    ipra_lc natEq s + natEq last + natEq w
  exact (cong_of_eq e).eqTrans (cong_drop _ _ hq)

/-! ## The remaining shifts -/

/-- `p^{j + r + 1}`, over `0 = r`, `1 = ⟨p, j⟩`. -/
abbrev hB : PTm 2 := pw (fstT (var 1)) (succ (sndT (var 1) + var 0))

theorem h_at (r p j : PTm n) : Γ ⊢[PRAAx] inst2 hB r (pairT p j) ≐ pw p (succ (j + r)) := by
  have h : inst2 hB r (pairT p j) = pw (fstT (pairT p j)) (succ (sndT (pairT p j) + r)) := by
    simp [inst2]
  rw [h]
  exact congrPw (fst_pair _ _) (congrSucc (congrAdd (snd_pair _ _) (.eqRefl _)))

/-- `H_j = p^{j+1} + p^{j+2} + ⋯ + p^p`: the shifts not yet turned into factors. -/
abbrev Hs (p j : PTm n) : PTm n := ap2 (sumF hB) (monus p j) (pairT p j)

theorem Hs_step {p j : PTm n} (h : Γ ⊢[PRAAx] lt j p) :
    Γ ⊢[PRAAx] Hs p j ≐ pw p (succ j) + Hs p (succ j) := by
  have e₁ : Γ ⊢[PRAAx] Hs p j ≐ ap2 (sumF hB) (succ (monus p (succ j))) (pairT p j) :=
    congrAp2 _ (monus_of_lt h) (.eqRefl _)
  have s := sum_shift (Γ := Γ) hB (monus p (succ j)) (pairT p j)
  have t0 : Γ ⊢[PRAAx] inst2 hB zero (pairT p j) ≐ pw p (succ j) :=
    (h_at zero p j).eqTrans (congrPw (.eqRefl p) (congrSucc (add_zero j)))
  have sh : Γ ⊢[PRAAx] ap2 (sumF (shiftBody hB)) (monus p (succ j)) (pairT p j) ≐
      Hs p (succ j) :=
    sum_congr_bounded (shiftBody hB) hB (pairT p j) (pairT p (succ j)) (monus p (succ j))
      (.allI (.impI (by
        rw [inst2_shiftBody]
        simp only [shift_pair, shift_succ]
        exact (h_at _ _ _).eqTrans ((congrPw (.eqRefl _)
          (congrSucc (by ipra_ring))).eqTrans (h_at _ _ _).eqSymm))))
  exact e₁.eqTrans (s.eqTrans (congrAdd t0 sh))

theorem Hs_end (p : PTm n) : Γ ⊢[PRAAx] Hs p p ≐ zero :=
  (congrAp2 _ (monus_self p) (.eqRefl _)).eqTrans (sum_zero _ _)

/-! ## Shifts become factors -/

/-- One shift by `p^{j+1}` is the factor `E + (j + 1)`. -/
theorem link1 {p j m : PTm n} (hp : Γ ⊢[PRAAx] prime p) :
    Γ ⊢[PRAAx] rem (Act bellB j (m + pw p (succ j)) zero) p ≐
      rem (Act bellB (succ j) m zero) p := by
  have hq := prime_eq_succ_pred hp
  refine act_cong bellB bellB hq (.allI (.impI ?_))
  simp only [inst2_bellB, shift_add, shift_pw, shift_succ]
  exact (cong_of_eq (congrBell (by ipra_ring))).eqTrans
    (touchard_power (prime_shift hp).wk (succ (Syn.shift j)) (Syn.shift m + var 0))

theorem link1' {p j m : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hlt : Γ ⊢[PRAAx] lt j p) :
    Γ ⊢[PRAAx] rem (Act bellB j (m + Hs p j) zero) p ≐
      rem (Act bellB (succ j) (m + Hs p (succ j)) zero) p := by
  have e : Γ ⊢[PRAAx] m + Hs p j ≐ m + Hs p (succ j) + pw p (succ j) := by
    ipra_lc natEq (Hs_step hlt)
  exact (cong_of_eq (congrAct bellB e (.eqRefl zero))).eqTrans (link1 hp)

/-- The induction formula; variable `0` is the number of converted shifts. -/
abbrev tele1F (p N : PTm n) : Fm PTm (n + 1) :=
  le (var 0) (Syn.shift p) ⟶
    (rem (bell (Syn.shift N + Hs (Syn.shift p) zero)) (Syn.shift p) ≐
      rem (Act bellB (var 0) (Syn.shift N + Hs (Syn.shift p) (var 0)) zero) (Syn.shift p))

/-- `B_{N + (p + p² + ⋯ + p^p)} ≡ ((E + 1) ⋯ (E + p) B)_N (mod p)`. -/
theorem tele1 {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (N : PTm n) :
    Γ ⊢[PRAAx] rem (bell (N + Hs p zero)) p ≐ rem (Act bellB p N zero) p := by
  let I : Fm PTm (n + 1) :=
    rem (bell (Syn.shift N + Hs (Syn.shift p) zero)) (Syn.shift p) ≐
      rem (Act bellB (var 0) (Syn.shift N + Hs (Syn.shift p) (var 0)) zero) (Syn.shift p)
  have atBound : Γ ⊢[PRAAx] I.subst (Syn.inst p) := by
    refine qfIndUpTo p trivial ?_ ?_
    · have a0 := act_zero (Γ := Γ) bellB (N + Hs p zero) zero
      rw [inst2_bellB] at a0
      simpa [I] using cong_of_eq (p := p) a0.eqSymm
    · simp [I, subst_repl_shift]
      exact .impI (Prf.eqTrans Prf.hyp1 (link1' (prime_shift hp).wk.wk Prf.hyp0))
  have result : Γ ⊢[PRAAx] rem (bell (N + Hs p zero)) p ≐ rem (Act bellB p (N + Hs p p) zero) p := by
    simpa [I] using atBound
  refine result.eqTrans (cong_of_eq (congrAct bellB ?_ (.eqRefl zero)))
  ipra_lc natEq (Hs_end (Γ := Γ) p)

/-! ## The falling factorials produce the same factors -/

/-- `G(m, p ∸ t) ≡ G(m + 1, p ∸ (t+1)) + (t + 1) G(m, p ∸ (t+1)) (mod p)` for `t < p`. -/
theorem G_cong {p t m : PTm n} (hq : Γ ⊢[PRAAx] p ≐ succ (pred p)) (hlt : Γ ⊢[PRAAx] lt t p) :
    Γ ⊢[PRAAx] rem (G m (monus p t)) p ≐
      rem (G (succ m) (monus p (succ t)) + succ t * G m (monus p (succ t))) p := by
  refine Foundations.ChineseRemainder.rem_eq_of_eq hq
    (k₁ := G m (monus p (succ t))) (k₂ := zero) ?_
  ipra_lc natEq (congrG (Γ := Γ) (.eqRefl m) (monus_of_lt hlt)) - natEq (G_succ (Γ := Γ) m (monus p (succ t))) +
    𝔞 (G m (monus p (succ t))) * natEq (eq_add_of_le hlt)

theorem link2 {p t m : PTm n} (hq : Γ ⊢[PRAAx] p ≐ succ (pred p)) (hlt : Γ ⊢[PRAAx] lt t p) :
    Γ ⊢[PRAAx] rem (Act gyB t m (monus p t)) p ≐
      rem (Act gyB (succ t) m (monus p (succ t))) p := by
  refine act_cong gyB gyB hq (.allI (.impI ?_))
  simp only [inst2_gyB, shift_monus, shift_succ]
  have hq' : (Γ.map Fm.shift) ⊢[PRAAx] Syn.shift p ≐ succ (pred (Syn.shift p)) := by
    simpa [Fm.shift, Syn.shift] using hq.shift
  have hlt' : (Γ.map Fm.shift) ⊢[PRAAx] lt (Syn.shift t) (Syn.shift p) := by
    simpa [Fm.shift, Syn.shift] using hlt.shift
  exact G_cong hq'.wk hlt'.wk

/-- The last chain entry is the product applied to the Bell numbers. -/
theorem act_gy_bell (p N K : PTm n) :
    Γ ⊢[PRAAx] inst2 (actB gyB) K (LinearFactorTable.par p N (monus p p)) ≐ inst2 (actB bellB) K (LinearFactorTable.par p N zero) := by
  have a := act_at (Γ := Γ) gyB K p N (monus p p)
  have b := act_at (Γ := Γ) bellB K p N zero
  rw [inst2_gyB] at a
  rw [inst2_bellB] at b
  exact a.eqTrans ((congrMul (.eqRefl _)
    ((congrG (.eqRefl _) (monus_self p)).eqTrans (G_zero _))).eqTrans b.eqSymm)

/-- The induction formula; variable `0` is the number of factors produced. -/
abbrev tele2F (p N : PTm n) : Fm PTm (n + 1) :=
  le (var 0) (Syn.shift p) ⟶
    (rem (G (Syn.shift N) (Syn.shift p)) (Syn.shift p) ≐
      rem (Act gyB (var 0) (Syn.shift N) (monus (Syn.shift p) (var 0))) (Syn.shift p))

/-- `G(N, p) ≡ ((E + 1) ⋯ (E + p) B)_N (mod p)`, for every modulus `p ≥ 1`. -/
theorem tele2_pos {p : PTm n} (hq : Γ ⊢[PRAAx] p ≐ succ (pred p)) (N : PTm n) :
    Γ ⊢[PRAAx] rem (G N p) p ≐ rem (Act bellB p N zero) p := by
  let I : Fm PTm (n + 1) :=
    rem (G (Syn.shift N) (Syn.shift p)) (Syn.shift p) ≐
      rem (Act gyB (var 0) (Syn.shift N) (monus (Syn.shift p) (var 0))) (Syn.shift p)
  have atBound : Γ ⊢[PRAAx] I.subst (Syn.inst p) := by
    refine qfIndUpTo p trivial ?_ ?_
    · simp [I]
      have a0 := act_zero (Γ := Γ) gyB N (monus p zero)
      rw [inst2_gyB] at a0
      exact cong_of_eq ((congrG (.eqRefl N) (monus_zero p).eqSymm).eqTrans a0.eqSymm)
    · simp [I, subst_repl_shift]
      exact .impI (Prf.eqTrans Prf.hyp1 (link2 (Common.pos_shift hq).wk.wk Prf.hyp0))
  have result : Γ ⊢[PRAAx] rem (G N p) p ≐ rem (Act gyB p N (monus p p)) p := by
    simpa [I] using atBound
  refine result.eqTrans (cong_of_eq ?_)
  refine sum_congr_bounded (actB gyB) (actB bellB) (LinearFactorTable.par p N (monus p p)) (LinearFactorTable.par p N zero) (succ p)
    (.allI (.impI ?_))
  simp only [shift_pair, shift_monus, shift_zero]
  exact act_gy_bell _ _ _

/-- `G(N, p) ≡ ((E + 1) ⋯ (E + p) B)_N (mod p)`. -/
theorem tele2 {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (N : PTm n) :
    Γ ⊢[PRAAx] rem (G N p) p ≐ rem (Act bellB p N zero) p :=
  tele2_pos (prime_eq_succ_pred hp) N

/-! ## The period `N_p` -/

/-- `p^r`, over `0 = r`, `1 = p`. -/
abbrev nB : PTm 2 := pw (var 1) (var 0)

theorem inst2_nB (r p : PTm n) : inst2 nB r p = pw p r := by simp [inst2]

/-- `N_p = 1 + p + ⋯ + p^{p−1}`. -/
abbrev Np (p : PTm n) : PTm n := ap2 (sumF nB) p p

/-- `N_p = 1 + (p + ⋯ + p^{p−1})`. -/
theorem Np_split {p : PTm n} (hq : Γ ⊢[PRAAx] p ≐ succ (pred p)) :
    Γ ⊢[PRAAx] Np p ≐ succ (ap2 (sumF (shiftBody nB)) (pred p) p) := by
  have c : Γ ⊢[PRAAx] Np p ≐ ap2 (sumF nB) (succ (pred p)) p := congrAp2 _ hq (.eqRefl p)
  have s := sum_shift (Γ := Γ) nB (pred p) p
  rw [inst2_nB] at s
  ipra_lc natEq c + natEq s + natEq (pw_zero (Γ := Γ) p)

/-- `(p + ⋯ + p^{p−1}) + p^p = p + p² + ⋯ + p^p`. -/
theorem tail_eq {p : PTm n} (hq : Γ ⊢[PRAAx] p ≐ succ (pred p)) :
    Γ ⊢[PRAAx] ap2 (sumF (shiftBody nB)) (pred p) p + pw p p ≐ Hs p zero := by
  have s := sum_succ' (Γ := Γ) (shiftBody nB) (pred p) p
  rw [inst2_shiftBody, inst2_nB] at s
  have top : Γ ⊢[PRAAx] pw p (succ (pred p)) ≐ pw p p := congrPw (.eqRefl p) hq.eqSymm
  have c : Γ ⊢[PRAAx] ap2 (sumF (shiftBody nB)) (succ (pred p)) p ≐ Hs p zero := by
    refine (sum_congr_bounded (shiftBody nB) hB p (pairT p zero) (succ (pred p))
      (.allI (.impI ?_))).eqTrans (congrAp2 _ (hq.eqSymm.eqTrans (monus_zero p).eqSymm) (.eqRefl _))
    rw [inst2_shiftBody, inst2_nB]
    simp only [shift_pair, shift_zero]
    exact (congrPw (.eqRefl _) (congrSucc (zero_add _).eqSymm)).eqTrans (h_at _ _ _).eqSymm
  ipra_lc -natEq s - natEq top + natEq c

/-- `thm:prime-period`: `B_{N + N_p} ≡ B_N (mod p)` for a prime `p`, with
`N_p = 1 + p + ⋯ + p^{p−1}`. -/
theorem bell_period_Np {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (N : PTm n) :
    Γ ⊢[PRAAx] rem (bell (N + Np p)) p ≐ rem (bell N) p := by
  have hq := prime_eq_succ_pred hp
  have e₁ : Γ ⊢[PRAAx] N + Np p ≐ succ (N + ap2 (sumF (shiftBody nB)) (pred p) p) := by
    have a := natEq (Np_split hq)
    apply deriveNat; ipra_simps
    linear_combination a
  have e₂ : Γ ⊢[PRAAx] N + ap2 (sumF (shiftBody nB)) (pred p) p + pw p p ≐ N + Hs p zero := by
    have a := natEq (tail_eq hq)
    apply deriveNat; ipra_simps
    linear_combination a
  exact (cong_of_eq (congrBell e₁)).eqTrans
    ((shift_pp hp (N + ap2 (sumF (shiftBody nB)) (pred p) p)).eqSymm.eqTrans
      ((cong_of_eq (congrBell e₂)).eqTrans
        ((tele1 hp N).eqTrans ((tele2 hp N).eqSymm.eqTrans (G_prime hq N)))))

/-- `thm:prime-period`, closed over `p` and `N`. -/
theorem bell_period_Np_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 (prime (var 0) ⟶
      (rem (bell (var 1 + Np (var 0))) (var 0) ≐ rem (bell (var 1)) (var 0))) :=
  closeUniv 2 (.impI (bell_period_Np Prf.hyp0 _))

end LeanProofs.IPRA.Combinatorics.BellPeriodNp
