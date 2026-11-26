import IPRADerivations.Combinatorics.BellTouchard
import IPRADerivations.Combinatorics.BinomialTransform
import IPRADerivations.Probability.Lotus
import IPRADerivations.Foundations.BoundedReflection
import IPRADerivations.AnalyticNumberTheory.Valuation

/-!
# The generalized Touchard congruence (`bell_numbers_ipra`, `thm:touchard-power`)

Packet: `combinatorics/bell_numbers_ipra`, `paper/04_congruences.tex`, theorem
`thm:touchard-power`: "For prime `p` and `r, n ≥ 0`, `B_{n+p^r} ≡ B_{n+1} + r B_n (mod p)`."

The packet argues in the quotient ring `𝔽_p[X]/(X^p − X − 1)`: `X^{p^r} = X + r`, by "raising
to the `p`th power replaces `X + r` by `X^p + r = X + (r + 1)`, using the elementary residue
identity `r^p = r`". The derivation here is the same computation on the sequence itself, with
the shift `E` in place of `X`:

* `U j ρ c = ∑_{i ≤ j} C(j, i) ρ^{j−i} B_{c+i}` is `((E + ρ)^j B)_c`; `pascal_U`:
  `U (j+1) ρ c = ρ · U j ρ c + U j ρ (c+1)`;
* `tele_step`: if `B_{m+q} ≡ B_{m+1} + ρ B_m` at the points used, then
  `U j ρ (c + q) ≡ U (j+1) ρ c`: one factor `E^q` is traded for one factor `E + ρ`;
* `top_split`, `top_cong`: `U p ρ c ≡ ρ^p B_c + B_{c+p}` (the middle binomial coefficients are
  divisible by `p`), so by Fermat and `thm:touchard` `U p ρ c ≡ B_{c+1} + (ρ + 1) B_c`;
* the induction on `r` cannot use the statement "for all `n`" as its formula. For a bound `T`
  the level-`r` statement on `{m : m + p^r ≤ T}` is one bit (`Foundations/BoundedReflection`),
  and level `r + 1` at `m` only uses level `r` at points `m'` with `m' + p^r ≤ m + p^{r+1}`;
* `touchard_power`: `rem B_{n+p^r} p = rem (B_{n+1} + r B_n) p`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.BellTouchardPower

open_ipra
open LeanProofs.IPRA.Combinatorics.Binomial
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (binom_zero' binom_self' pascal_at)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrBinom congrPw)
open LeanProofs.IPRA.Combinatorics.BinomialTransform (bgB inst2_bg inst2_bgs pascal_sum)
open LeanProofs.IPRA.Combinatorics.Bell (bell bell_zero)
open LeanProofs.IPRA.Combinatorics.BellPascalInversion (congrBell)
open LeanProofs.IPRA.Combinatorics.BellTouchard (touchard divmod_p)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (prime)
open LeanProofs.IPRA.AnalyticNumberTheory.Fermat (prime_dvd_binom dvd_sum prime_shift fermat_at)
open LeanProofs.IPRA.Probability.Lotus (cmB inst2_cmB sum_const_mul)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Congruences as equations of remainders -/

theorem cong_add {p a a' b b' : PTm n} (hq : Γ ⊢[PRAAx] p ≐ succ (pred p))
    (ha : Γ ⊢[PRAAx] rem a p ≐ rem a' p) (hb : Γ ⊢[PRAAx] rem b p ≐ rem b' p) :
    Γ ⊢[PRAAx] rem (a + b) p ≐ rem (a' + b') p := by
  refine Foundations.ChineseRemainder.rem_eq_of_eq hq
    (k₁ := quo a' p + quo b' p) (k₂ := quo a p + quo b p) ?_
  ipra_lc natEq (divmod_p hq a) - natEq (divmod_p hq a') + natEq (divmod_p hq b) - natEq (divmod_p hq b') + natEq ha +
    natEq hb

theorem cong_mul {p a a' : PTm n} (c : PTm n) (hq : Γ ⊢[PRAAx] p ≐ succ (pred p))
    (ha : Γ ⊢[PRAAx] rem a p ≐ rem a' p) : Γ ⊢[PRAAx] rem (c * a) p ≐ rem (c * a') p := by
  refine Foundations.ChineseRemainder.rem_eq_of_eq hq (k₁ := c * quo a' p) (k₂ := c * quo a p) ?_
  ipra_lc 𝔞 c * natEq (divmod_p hq a) - 𝔞 c * natEq (divmod_p hq a') + 𝔞 c * natEq ha

theorem cong_of_eq {p a a' : PTm n} (h : Γ ⊢[PRAAx] a ≐ a') : Γ ⊢[PRAAx] rem a p ≐ rem a' p :=
  congrAp2 remF h (.eqRefl _)

/-- Sums are congruent when the terms are congruent below the bound. -/
theorem cong_sum (f g : PTm 2) {p x y N : PTm n} (hq : Γ ⊢[PRAAx] p ≐ succ (pred p))
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (rem (inst2 f (var 0) (Syn.shift x)) (Syn.shift p) ≐
        rem (inst2 g (var 0) (Syn.shift y)) (Syn.shift p)))) :
    Γ ⊢[PRAAx] rem (ap2 (sumF f) N x) p ≐ rem (ap2 (sumF g) N y) p := by
  have hq' : (Γ.map Fm.shift) ⊢[PRAAx] Syn.shift p ≐ succ (pred (Syn.shift p)) := by
    simpa [Fm.shift, Syn.shift] using hq.shift
  have hall : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift N) ⟶
      (rem (ap2 (sumF f) (var 0) (Syn.shift x)) (Syn.shift p) ≐
        rem (ap2 (sumF g) (var 0) (Syn.shift y)) (Syn.shift p))) := by
    refine PRA.qfInd _ ⟨le_QF _ _, trivial⟩ ?_ ?_
    · simpa using .impI (cong_of_eq
        ((sum_zero (Γ := le zero N :: Γ) f x).eqTrans (sum_zero _ _).eqSymm))
    · simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap2, Syn.subst_var, Syn.repl_zero,
        subst_repl_shift, ConciseIPRA.PTm.subst_zero]
      refine .impI ?_
      exact ((cong_of_eq (sum_succ' f (var 0) _)).eqTrans
        (cong_add hq'.wk.wk
          (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0))
          (.impE h.allOpen.wk.wk Prf.hyp0))).eqTrans (cong_of_eq (sum_succ' g (var 0) _)).eqSymm
  have h2 := Prf.allE N hall
  simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap2, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero] at h2
  exact .impE h2 (le_refl N)

/-! ## The weighted binomial sum -/

/-- The parameter `⟨⟨J, ρ⟩, c⟩`. -/
abbrev par (J ρ c : PTm n) : PTm n := pairT (pairT J ρ) c

/-- `ρ^{J ∸ i} · B_{c+i}`, over `0 = i`, `1 = ⟨⟨J, ρ⟩, c⟩`. -/
abbrev wB : PTm 2 :=
  pw (sndT (fstT (var 1))) (monus (fstT (fstT (var 1))) (var 0)) * bell (sndT (var 1) + var 0)

theorem w_at (i J ρ c : PTm n) :
    Γ ⊢[PRAAx] inst2 wB i (par J ρ c) ≐ pw ρ (monus J i) * bell (c + i) := by
  have h : inst2 wB i (par J ρ c) = pw (sndT (fstT (par J ρ c)))
      (monus (fstT (fstT (par J ρ c))) i) * bell (sndT (par J ρ c) + i) := by simp [inst2]
  rw [h]
  exact congrMul
    (congrPw (fst_pair _ _).sndE
      (congrMonus (fst_pair _ _).fstE (.eqRefl _)))
    (congrBell (congrAdd (snd_pair _ _) (.eqRefl _)))

/-- `C(j, i) · ρ^{J ∸ i} · B_{c+i}`. -/
theorem bg_at (i j J ρ c : PTm n) :
    Γ ⊢[PRAAx] inst2 (bgB wB) i (pairT j (par J ρ c)) ≐
      binom j i * (pw ρ (monus J i) * bell (c + i)) := by
  rw [inst2_bg]
  exact congrMul (congrBinom (fst_pair _ _) (.eqRefl _))
    ((congrInst2 wB (.eqRefl _) (snd_pair _ _)).eqTrans (w_at _ _ _ _))

theorem bgs_at (i j J ρ c : PTm n) :
    Γ ⊢[PRAAx] inst2 (bgB (shiftBody wB)) i (pairT j (par J ρ c)) ≐
      binom j i * (pw ρ (monus J (succ i)) * bell (c + succ i)) := by
  rw [inst2_bgs]
  exact congrMul (congrBinom (fst_pair _ _) (.eqRefl _))
    ((congrInst2 wB (.eqRefl _) (snd_pair _ _)).eqTrans (w_at _ _ _ _))

/-- `U j ρ c = ∑_{i ≤ j} C(j, i) ρ^{j−i} B_{c+i}`. -/
abbrev U (j ρ c : PTm n) : PTm n := ap2 (sumF (bgB wB)) (succ j) (pairT j (par j ρ c))

theorem shift_pair (a b : PTm n) : Syn.shift (pairT a b) = pairT (Syn.shift a) (Syn.shift b) := by
  simp [Syn.shift]

theorem shift_succ (a : PTm n) : Syn.shift (succ a) = succ (Syn.shift a) := by
  simp [Syn.shift]

alias le_of_lt_succ := Common.le_of_lt_succ

alias succ_monus_of_le := Common.monus_succ_of_le

/-- The first Pascal sum: one more factor `ρ`. -/
theorem pt_scale {i j ρ c : PTm n} (h : Γ ⊢[PRAAx] lt i (succ j)) :
    Γ ⊢[PRAAx] inst2 (bgB wB) i (pairT j (par (succ j) ρ c)) ≐
      inst2 (cmB (bgB wB)) i (pairT ρ (pairT j (par j ρ c))) := by
  rw [inst2_cmB]
  have r : Γ ⊢[PRAAx] fstT (pairT ρ (pairT j (par j ρ c))) *
      inst2 (bgB wB) i (sndT (pairT ρ (pairT j (par j ρ c)))) ≐
      ρ * (binom j i * (pw ρ (monus j i) * bell (c + i))) :=
    congrMul (fst_pair _ _) ((congrInst2 _ (.eqRefl _) (snd_pair _ _)).eqTrans (bg_at _ _ _ _ _))
  refine (bg_at i j (succ j) ρ c).eqTrans (.eqTrans ?_ r.eqSymm)
  ipra_lc 𝔞 (binom j i) * 𝔞 (bell (c + i)) * natEq ((congrPw (.eqRefl ρ) (succ_monus_of_le (le_of_lt_succ h))).eqTrans (pw_succ ρ (monus j i)))

/-- The second Pascal sum: the base moves from `c` to `c + 1`. -/
theorem pt_shift (i j ρ c : PTm n) :
    Γ ⊢[PRAAx] inst2 (bgB (shiftBody wB)) i (pairT j (par (succ j) ρ c)) ≐
      inst2 (bgB wB) i (pairT j (par j ρ (succ c))) := by
  refine (bgs_at i j (succ j) ρ c).eqTrans (.eqTrans ?_ (bg_at i j j ρ (succ c)).eqSymm)
  refine congrMul (.eqRefl _) (congrMul (congrPw (.eqRefl _) (succ_monus_succ _ _))
    (congrBell ?_))
  ipra_ring

/-- `U (j+1) ρ c = ρ · U j ρ c + U j ρ (c+1)`. -/
theorem pascal_U (j ρ c : PTm n) :
    Γ ⊢[PRAAx] U (succ j) ρ c ≐ ρ * U j ρ c + U j ρ (succ c) := by
  refine (pascal_sum wB j (par (succ j) ρ c)).eqTrans (congrAdd ?_ ?_)
  · refine (sum_congr_bounded (bgB wB) (cmB (bgB wB)) (pairT j (par (succ j) ρ c))
      (pairT ρ (pairT j (par j ρ c))) (succ j) (.allI (.impI ?_))).eqTrans
      (sum_const_mul (bgB wB) (succ j) ρ (pairT j (par j ρ c)))
    simp only [shift_pair, shift_succ]
    exact pt_scale (by simpa only [shift_succ] using
      (Prf.hyp0 (Γ := Γ.map Fm.shift) (φ := lt (var 0) (Syn.shift (succ j)))))
  · refine sum_congr_bounded (bgB (shiftBody wB)) (bgB wB) (pairT j (par (succ j) ρ c))
      (pairT j (par j ρ (succ c))) (succ j) (.allI (.impI ?_))
    simp only [shift_pair, shift_succ]
    exact pt_shift _ _ _ _

/-! ## Small evaluations -/

alias pair_congr := Common.congrPairT

/-- `U` respects equality of the base. -/
theorem congrU {j ρ c c' : PTm n} (h : Γ ⊢[PRAAx] c ≐ c') : Γ ⊢[PRAAx] U j ρ c ≐ U j ρ c' :=
  congrAp2 _ (.eqRefl _) (pair_congr (.eqRefl _) (pair_congr (.eqRefl _) h))

/-- `U 0 ρ c = B_c`. -/
theorem U_zero (ρ c : PTm n) : Γ ⊢[PRAAx] U zero ρ c ≐ bell c := by
  have t : Γ ⊢[PRAAx] inst2 (bgB wB) zero (pairT zero (par zero ρ c)) ≐ bell c :=
    (bg_at zero zero zero ρ c).eqTrans
      ((congrMul (binom_zero' zero) (congrMul
        ((congrPw (.eqRefl ρ) (monus_zero zero)).eqTrans (pw_zero ρ))
        (congrBell (add_zero c)))).eqTrans (by ipra_ring))
  ipra_lc natEq (sum_succ' (Γ := Γ) (bgB wB) zero (pairT zero (par zero ρ c))) +
    natEq (sum_zero (Γ := Γ) (bgB wB) (pairT zero (par zero ρ c))) + natEq t

/-! ## The top level `j = p` -/

/-- The middle terms `∑_{0 < i < p} C(p, i) ρ^{p−i} B_{c+i}`. -/
abbrev Mid (p ρ c : PTm n) : PTm n :=
  ap2 (sumF (shiftBody (bgB wB))) (pred p) (pairT p (par p ρ c))

/-- `U p ρ c = B_c ρ^p + Mid + B_{c+p}`. -/
theorem top_split {p : PTm n} (hq : Γ ⊢[PRAAx] p ≐ succ (pred p)) (ρ c : PTm n) :
    Γ ⊢[PRAAx] U p ρ c ≐ bell c * pw ρ p + Mid p ρ c + bell (c + p) := by
  have s1 := sum_shift (Γ := Γ) (bgB wB) p (pairT p (par p ρ c))
  have s2 : Γ ⊢[PRAAx] ap2 (sumF (shiftBody (bgB wB))) p (pairT p (par p ρ c)) ≐
      ap2 (sumF (shiftBody (bgB wB))) (succ (pred p)) (pairT p (par p ρ c)) :=
    congrAp2 _ hq (.eqRefl _)
  have s3 := sum_succ' (Γ := Γ) (shiftBody (bgB wB)) (pred p) (pairT p (par p ρ c))
  rw [inst2_shiftBody] at s3
  have t0 : Γ ⊢[PRAAx] inst2 (bgB wB) zero (pairT p (par p ρ c)) ≐ bell c * pw ρ p :=
    (bg_at zero p p ρ c).eqTrans
      ((congrMul (binom_zero' p) (congrMul (congrPw (.eqRefl ρ) (monus_zero p))
        (congrBell (add_zero c)))).eqTrans (by ipra_ring))
  have tq : Γ ⊢[PRAAx] inst2 (bgB wB) (succ (pred p)) (pairT p (par p ρ c)) ≐ bell (c + p) := by
    refine (bg_at _ p p ρ c).eqTrans ?_
    have g1 : Γ ⊢[PRAAx] binom p (succ (pred p)) ≐ one :=
      (congrBinom (.eqRefl p) hq.eqSymm).eqTrans (binom_self' p)
    have g2 : Γ ⊢[PRAAx] pw ρ (monus p (succ (pred p))) ≐ one :=
      (congrPw (.eqRefl ρ) ((congrMonus (.eqRefl p) hq.eqSymm).eqTrans (monus_self p))).eqTrans
        (pw_zero _)
    refine (congrMul g1 (congrMul g2 (congrBell (congrAdd (.eqRefl c) hq.eqSymm)))).eqTrans ?_
    ipra_ring
  have a := natEq s1; have b := natEq s2; have c' := natEq s3
  have d := natEq t0; have e := natEq tq
  apply deriveNat; ipra_simps
  linear_combination a + b + c' + d + e

/-- `p ∣ Mid`: each middle binomial coefficient is divisible by `p`. -/
theorem mid_dvd {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (ρ c : PTm n) :
    Γ ⊢[PRAAx] dvd p (Mid p ρ c) := by
  have hq := prime_eq_succ_pred hp
  refine dvd_congr_left hq.eqSymm (dvd_sum _ (.allI (.impI ?_)))
  rw [inst2_shiftBody]
  simp only [shift_pair]
  have hp' := (prime_shift hp).wk (ψ := lt (var 0) (Syn.shift (pred p)))
  have hq' := prime_eq_succ_pred hp'
  have e : Syn.shift (pred p) = pred (Syn.shift p) := by simp [Syn.shift]
  have hb := prime_dvd_binom hp' hq' (j := var 0) (q := pred (Syn.shift p))
    (by rw [← e]; exact Prf.hyp0)
  have ht := DiophantineNumberTheory.Coprime.dvd_mul' hq'
    (pw (Syn.shift ρ) (monus (Syn.shift p) (succ (var 0))) * bell (Syn.shift c + succ (var 0))) hb
  have hq2 := hq'
  rw [← e] at hq2
  exact dvd_congr_left hq2 (dvd_congr (bg_at _ _ _ _ _).eqSymm ht)

/-- `U p ρ c ≡ B_{c+1} + (ρ + 1) B_c (mod p)`: Fermat and `thm:touchard`. -/
theorem top_cong {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (ρ c : PTm n) :
    Γ ⊢[PRAAx] rem (U p ρ c) p ≐ rem (bell (succ c) + succ ρ * bell c) p := by
  have hq := prime_eq_succ_pred hp
  have m0 : Γ ⊢[PRAAx] rem (Mid p ρ c) p ≐ rem zero p :=
    (mid_dvd hp ρ c).eqTrans (rem_zero p).eqSymm
  have tc : Γ ⊢[PRAAx] rem (bell (c + p)) p ≐ rem (bell (succ c) + bell c) p :=
    (cong_of_eq (congrBell (add_comm c p))).eqTrans (touchard hp c)
  refine (cong_of_eq (top_split hq ρ c)).eqTrans ?_
  refine (cong_add hq (cong_add hq (cong_mul (bell c) hq (fermat_at hp ρ)) m0) tc).eqTrans ?_
  refine cong_of_eq ?_
  ipra_ring

/-! ## Trading one shift by `q` for one factor `E + ρ` -/

/-- The induction formula of `cong_sum_lin`; variable `0` is the upper limit. -/
abbrev linF (f g h : PTm 2) (p ρ x y z N : PTm n) : Fm PTm (n + 1) :=
  le (var 0) (Syn.shift N) ⟶
    (rem (ap2 (sumF f) (var 0) (Syn.shift x)) (Syn.shift p) ≐
      rem (ap2 (sumF g) (var 0) (Syn.shift y) + Syn.shift ρ * ap2 (sumF h) (var 0) (Syn.shift z))
        (Syn.shift p))

/-- `rem (∑ f) = rem (∑ g + ρ ∑ h)` from the same relation between the terms. -/
theorem cong_sum_lin (f g h : PTm 2) {p ρ x y z N : PTm n} (hq : Γ ⊢[PRAAx] p ≐ succ (pred p))
    (H : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (rem (inst2 f (var 0) (Syn.shift x)) (Syn.shift p) ≐
        rem (inst2 g (var 0) (Syn.shift y) + Syn.shift ρ * inst2 h (var 0) (Syn.shift z))
          (Syn.shift p)))) :
    Γ ⊢[PRAAx] rem (ap2 (sumF f) N x) p ≐ rem (ap2 (sumF g) N y + ρ * ap2 (sumF h) N z) p := by
  have hq' : (Γ.map Fm.shift) ⊢[PRAAx] Syn.shift p ≐ succ (pred (Syn.shift p)) := by
    simpa [Fm.shift, Syn.shift] using hq.shift
  have hall : Γ ⊢[PRAAx] Fm.all (linF f g h p ρ x y z N) := by
    refine PRA.qfInd _ ⟨le_QF _ _, trivial⟩ ?_ ?_
    · have b : (le zero N :: Γ) ⊢[PRAAx] ap2 (sumF f) zero x ≐
          ap2 (sumF g) zero y + ρ * ap2 (sumF h) zero z := by
        have a₁ := natEq (sum_zero (Γ := le zero N :: Γ) f x)
        have a₂ := natEq (sum_zero (Γ := le zero N :: Γ) g y)
        have a₃ := natEq (sum_zero (Γ := le zero N :: Γ) h z)
        apply deriveNat; ipra_simps
        linear_combination a₁ - a₂ - 𝔞 ρ * a₃
      simpa using .impI (cong_of_eq (p := p) b)
    · simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul,
        Syn.subst_var, Syn.repl_zero, subst_repl_shift, ConciseIPRA.PTm.subst_zero]
      refine .impI ?_
      refine ((cong_of_eq (sum_succ' f (var 0) _)).eqTrans
        (cong_add hq'.wk.wk
          (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0))
          (.impE H.allOpen.wk.wk Prf.hyp0))).eqTrans (cong_of_eq ?_)
      have a₂ := natEq (sum_succ' (Γ := le (succ (var 0)) (Syn.shift N) ::
        linF f g h p ρ x y z N :: Γ.map Fm.shift) g (var 0) (Syn.shift y))
      have a₃ := natEq (sum_succ' (Γ := le (succ (var 0)) (Syn.shift N) ::
        linF f g h p ρ x y z N :: Γ.map Fm.shift) h (var 0) (Syn.shift z))
      apply deriveNat; ipra_simps
      linear_combination -a₂ - 𝔞 (Syn.shift ρ) * a₃
  have h2 := Prf.allE N hall
  simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul,
    Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero] at h2
  exact .impE h2 (le_refl N)

/-- One term: `C ρ^{j−i} B_{c+q+i} ≡ C ρ^{j−i} B_{c+1+i} + ρ · C ρ^{j−i} B_{c+i}`. -/
theorem pt_cong {p ρ q c i j : PTm n} (hq : Γ ⊢[PRAAx] p ≐ succ (pred p))
    (h : Γ ⊢[PRAAx] rem (bell (c + i + q)) p ≐ rem (bell (succ (c + i)) + ρ * bell (c + i)) p) :
    Γ ⊢[PRAAx] rem (inst2 (bgB wB) i (pairT j (par j ρ (c + q)))) p ≐
      rem (inst2 (bgB wB) i (pairT j (par j ρ (succ c))) +
        ρ * inst2 (bgB wB) i (pairT j (par j ρ c))) p := by
  have l : Γ ⊢[PRAAx] inst2 (bgB wB) i (pairT j (par j ρ (c + q))) ≐
      binom j i * pw ρ (monus j i) * bell (c + i + q) := by
    refine (bg_at i j j ρ (c + q)).eqTrans ?_
    ipra_lc 𝔞 (binom j i) * 𝔞 (pw ρ (monus j i)) * natEq (congrBell (Γ := Γ) (a := c + q + i) (b := c + i + q) (by ipra_ring))
  have r : Γ ⊢[PRAAx] binom j i * pw ρ (monus j i) * (bell (succ (c + i)) + ρ * bell (c + i)) ≐
      inst2 (bgB wB) i (pairT j (par j ρ (succ c))) +
        ρ * inst2 (bgB wB) i (pairT j (par j ρ c)) := by
    refine .eqTrans ?_ (congrAdd (bg_at i j j ρ (succ c))
      (congrMul (.eqRefl ρ) (bg_at i j j ρ c))).eqSymm
    ipra_lc 𝔞 (binom j i) * 𝔞 (pw ρ (monus j i)) * natEq (congrBell (Γ := Γ) (a := succ (c + i)) (b := succ c + i) (by ipra_ring))
  exact (cong_of_eq l).eqTrans ((cong_mul _ hq h).eqTrans (cong_of_eq r))

theorem shift_add (a b : PTm n) : Syn.shift (a + b) = Syn.shift a + Syn.shift b := by
  simp [Syn.shift]

/-- `U j ρ (c + q) ≡ U (j+1) ρ c`, given `B_{m+q} ≡ B_{m+1} + ρ B_m` at `m = c + i`, `i ≤ j`. -/
theorem tele_step {p ρ q c j : PTm n} (hq : Γ ⊢[PRAAx] p ≐ succ (pred p))
    (H : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift (succ j)) ⟶
      (rem (bell (Syn.shift c + var 0 + Syn.shift q)) (Syn.shift p) ≐
        rem (bell (succ (Syn.shift c + var 0)) + Syn.shift ρ * bell (Syn.shift c + var 0))
          (Syn.shift p)))) :
    Γ ⊢[PRAAx] rem (U j ρ (c + q)) p ≐ rem (U (succ j) ρ c) p := by
  have hq' : (Γ.map Fm.shift) ⊢[PRAAx] Syn.shift p ≐ succ (pred (Syn.shift p)) := by
    simpa [Fm.shift, Syn.shift] using hq.shift
  refine (cong_sum_lin (bgB wB) (bgB wB) (bgB wB) (ρ := ρ) (x := pairT j (par j ρ (c + q)))
    (y := pairT j (par j ρ (succ c))) (z := pairT j (par j ρ c)) hq (.allI (.impI ?_))).eqTrans
    (cong_of_eq ?_)
  · simp only [shift_pair, shift_add]
    rw [shift_succ (a := c)]
    exact pt_cong hq'.wk (.impE H.allOpen.wk Prf.hyp0)
  · ipra_lc -natEq (pascal_U (Γ := Γ) j ρ c)

/-! ## The level bit -/

open LeanProofs.IPRA.Foundations.BoundedReflection (allB all_elim all_intro)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (eq_of_eqb_ne pw_pos')
open LeanProofs.IPRA.AnalyticNumberTheory.Euler (congrEqb)

/-- The parameter `⟨r, ⟨T, p⟩⟩`. -/
abbrev lvP (r T p : PTm n) : PTm n := pairT r (pairT T p)

/-- The bit of `m + p^r ≤ T → B_{m+p^r} ≡ B_{m+1} + r B_m (mod p)`, over `0 = m`,
`1 = ⟨r, ⟨T, p⟩⟩`: nonzero when the bound fails or the congruence holds. -/
abbrev lvB : PTm 2 :=
  monus (var 0 + pw (sndT (sndT (var 1))) (fstT (var 1))) (fstT (sndT (var 1))) +
    eqb (rem (bell (var 0 + pw (sndT (sndT (var 1))) (fstT (var 1)))) (sndT (sndT (var 1))))
      (rem (bell (succ (var 0)) + fstT (var 1) * bell (var 0)) (sndT (sndT (var 1))))

theorem lv_at (m r T p : PTm n) :
    Γ ⊢[PRAAx] inst2 lvB m (lvP r T p) ≐ monus (m + pw p r) T +
      eqb (rem (bell (m + pw p r)) p) (rem (bell (succ m) + r * bell m) p) := by
  have h : inst2 lvB m (lvP r T p) =
      monus (m + pw (sndT (sndT (lvP r T p))) (fstT (lvP r T p))) (fstT (sndT (lvP r T p))) +
        eqb (rem (bell (m + pw (sndT (sndT (lvP r T p))) (fstT (lvP r T p))))
            (sndT (sndT (lvP r T p))))
          (rem (bell (succ m) + fstT (lvP r T p) * bell m) (sndT (sndT (lvP r T p)))) := by
    simp [inst2]
  rw [h]
  have hr : Γ ⊢[PRAAx] fstT (lvP r T p) ≐ r := fst_pair _ _
  have hT : Γ ⊢[PRAAx] fstT (sndT (lvP r T p)) ≐ T := (snd_pair _ _).fstE
  have hp : Γ ⊢[PRAAx] sndT (sndT (lvP r T p)) ≐ p := (snd_pair _ _).sndE
  exact congrAdd (congrMonus (congrAdd (.eqRefl m) (congrPw hp hr)) hT)
    (congrEqb (congrAp2 remF (congrBell (congrAdd (.eqRefl m) (congrPw hp hr))) hp)
      (congrAp2 remF (congrAdd (.eqRefl _) (congrMul hr (.eqRefl _))) hp))

/-- Reading the level bit at a point within the bound. -/
theorem level_at {m r T p : PTm n} (hQ : Γ ⊢[PRAAx] allB lvB (succ T) (lvP r T p) ≐ one)
    (hm : Γ ⊢[PRAAx] le (m + pw p r) T) :
    Γ ⊢[PRAAx] rem (bell (m + pw p r)) p ≐ rem (bell (succ m) + r * bell m) p := by
  have hlt : Γ ⊢[PRAAx] lt m (succ T) :=
    (succ_monus_succ m T).eqTrans (le_trans (le_add_right m _) hm)
  have ne := all_elim lvB hQ hlt
  refine eq_of_eqb_ne (.impI (.impE ne.wk ?_))
  exact (lv_at m r T p).eqTrans ((congrAdd hm.wk Prf.hyp0).eqTrans (add_zero _))

/-- `T < a` gives `a ∸ T = (a ∸ (T + 1)) + 1`. -/
theorem monus_of_lt {a T : PTm n} (h : Γ ⊢[PRAAx] lt T a) :
    Γ ⊢[PRAAx] monus a T ≐ succ (monus a (succ T)) := by
  have w : Γ ⊢[PRAAx] a ≐ T + succ (monus a (succ T)) := by
    ipra_lc natEq (eq_add_of_le h)
  exact (congrMonus w (.eqRefl T)).eqTrans (add_monus' _ T)

theorem lv_ne_gt {m r T p : PTm n} (h : Γ ⊢[PRAAx] lt T (m + pw p r))
    (hz : Γ ⊢[PRAAx] inst2 lvB m (lvP r T p) ≐ zero) : Γ ⊢[PRAAx] Fm.bot := by
  refine succ_ne_zero' _ (a := monus (m + pw p r) (succ T) +
    eqb (rem (bell (m + pw p r)) p) (rem (bell (succ m) + r * bell m) p)) ?_
  ipra_lc natEq hz - natEq (lv_at (Γ := Γ) m r T p) - natEq (monus_of_lt h)

theorem lv_ne_le {m r T p : PTm n}
    (h : Γ ⊢[PRAAx] rem (bell (m + pw p r)) p ≐ rem (bell (succ m) + r * bell m) p)
    (hm : Γ ⊢[PRAAx] le (m + pw p r) T)
    (hz : Γ ⊢[PRAAx] inst2 lvB m (lvP r T p) ≐ zero) : Γ ⊢[PRAAx] Fm.bot :=
  Foundations.BoundedReflection.one_ne_zero _
    (((lv_at m r T p).eqTrans ((congrAdd hm (eqb_of_eq h)).eqTrans (zero_add one))).eqSymm.eqTrans hz)

/-- Writing the level bit at a point: it suffices to prove the congruence under the bound. -/
theorem lv_ne {m r T p : PTm n}
    (h : Γ ⊢[PRAAx] le (m + pw p r) T ⟶
      (rem (bell (m + pw p r)) p ≐ rem (bell (succ m) + r * bell m) p)) :
    Γ ⊢[PRAAx] neg (inst2 lvB m (lvP r T p) ≐ zero) :=
  .impI (.orE (lt_or_le T (m + pw p r)) (lv_ne_gt Prf.hyp0 Prf.hyp1)
    (lv_ne_le (.impE h.wk.wk Prf.hyp0) Prf.hyp0 Prf.hyp1))

/-! ## The telescoping chain -/

/-- The points used by one link stay within the bound. -/
theorem tele_bound {m J j i q T : PTm n} (hq : Γ ⊢[PRAAx] q ≐ succ (pred q))
    (hjJ : Γ ⊢[PRAAx] le (succ j) J) (hi : Γ ⊢[PRAAx] lt i (succ j))
    (hm : Γ ⊢[PRAAx] le (m + J * q) T) :
    Γ ⊢[PRAAx] le (m + monus J (succ j) * q + i + q) T := by
  refine le_trans (le_of_eq_add (d := i * pred q + monus j i * q) ?_) hm
  ipra_lc 𝔞 q * natEq (eq_add_of_le hjJ) + 𝔞 q * natEq (eq_add_of_le (le_of_lt_succ hi)) + 𝔞 i * natEq hq

theorem shift_mul (a b : PTm n) : Syn.shift (a * b) = Syn.shift a * Syn.shift b := by
  simp [Syn.shift]

theorem shift_monus (a b : PTm n) : Syn.shift (monus a b) = monus (Syn.shift a) (Syn.shift b) := by
  simp [Syn.shift]

theorem shift_pw (a b : PTm n) : Syn.shift (pw a b) = pw (Syn.shift a) (Syn.shift b) := by
  simp [Syn.shift]

/-- One link: `U j r (m + (J ∸ j) p^r) ≡ U (j+1) r (m + (J ∸ (j+1)) p^r)`. -/
theorem tele_link {p r T m J j : PTm n} (hq : Γ ⊢[PRAAx] p ≐ succ (pred p))
    (hQ : Γ ⊢[PRAAx] allB lvB (succ T) (lvP r T p) ≐ one) (hjJ : Γ ⊢[PRAAx] le (succ j) J)
    (hm : Γ ⊢[PRAAx] le (m + J * pw p r) T) :
    Γ ⊢[PRAAx] rem (U j r (m + monus J j * pw p r)) p ≐
      rem (U (succ j) r (m + monus J (succ j) * pw p r)) p := by
  have e₀ : Γ ⊢[PRAAx] m + monus J j * pw p r ≐ m + monus J (succ j) * pw p r + pw p r := by
    ipra_lc 𝔞 (pw p r) * natEq (monus_of_lt hjJ)
  refine (cong_of_eq (congrU e₀)).eqTrans (tele_step hq (.allI (.impI ?_)))
  simp only [shift_add, shift_mul, shift_monus, shift_succ, shift_pw]
  have hQ' : (Γ.map Fm.shift) ⊢[PRAAx]
      allB lvB (succ (Syn.shift T)) (lvP (Syn.shift r) (Syn.shift T) (Syn.shift p)) ≐ one := by
    simpa [Fm.shift, Syn.shift] using hQ.shift
  have hq' : (Γ.map Fm.shift) ⊢[PRAAx] Syn.shift p ≐ succ (pred (Syn.shift p)) := by
    simpa [Fm.shift, Syn.shift] using hq.shift
  have hjJ' : (Γ.map Fm.shift) ⊢[PRAAx] le (succ (Syn.shift j)) (Syn.shift J) := by
    simpa [Fm.shift, Syn.shift] using hjJ.shift
  have hm' : (Γ.map Fm.shift) ⊢[PRAAx]
      le (Syn.shift m + Syn.shift J * pw (Syn.shift p) (Syn.shift r)) (Syn.shift T) := by
    simpa [Fm.shift, Syn.shift] using hm.shift
  exact level_at hQ'.wk (tele_bound (pw_pos' hq'.wk _) hjJ'.wk Prf.hyp0 hm'.wk)

/-- The induction formula of the chain; variable `0` is the number of links. -/
abbrev teleF (p r m J : PTm n) : Fm PTm (n + 1) :=
  le (var 0) (Syn.shift J) ⟶
    (rem (bell (Syn.shift m + Syn.shift J * pw (Syn.shift p) (Syn.shift r))) (Syn.shift p) ≐
      rem (U (var 0) (Syn.shift r)
        (Syn.shift m + monus (Syn.shift J) (var 0) * pw (Syn.shift p) (Syn.shift r))) (Syn.shift p))

/-- `B_{m + J p^r} ≡ U J r m`: `J` shifts by `p^r` become `(E + r)^J`. -/
theorem tele {p r T m J : PTm n} (hq : Γ ⊢[PRAAx] p ≐ succ (pred p))
    (hQ : Γ ⊢[PRAAx] allB lvB (succ T) (lvP r T p) ≐ one)
    (hm : Γ ⊢[PRAAx] le (m + J * pw p r) T) :
    Γ ⊢[PRAAx] rem (bell (m + J * pw p r)) p ≐ rem (U J r m) p := by
  have hall : Γ ⊢[PRAAx] Fm.all (teleF p r m J) := by
    refine PRA.qfInd _ ⟨le_QF _ _, trivial⟩ ?_ ?_
    · have b : (le zero J :: Γ) ⊢[PRAAx] rem (bell (m + J * pw p r)) p ≐
          rem (U zero r (m + monus J zero * pw p r)) p :=
        cong_of_eq ((congrBell (congrAdd (.eqRefl m)
          (congrMul (monus_zero J).eqSymm (.eqRefl _)))).eqTrans (U_zero r _).eqSymm)
      simpa using .impI b
    · have hQ' : (Γ.map Fm.shift) ⊢[PRAAx]
          allB lvB (succ (Syn.shift T)) (lvP (Syn.shift r) (Syn.shift T) (Syn.shift p)) ≐ one := by
        simpa [Fm.shift, Syn.shift] using hQ.shift
      have hq' : (Γ.map Fm.shift) ⊢[PRAAx] Syn.shift p ≐ succ (pred (Syn.shift p)) := by
        simpa [Fm.shift, Syn.shift] using hq.shift
      have hm' : (Γ.map Fm.shift) ⊢[PRAAx]
          le (Syn.shift m + Syn.shift J * pw (Syn.shift p) (Syn.shift r)) (Syn.shift T) := by
        simpa [Fm.shift, Syn.shift] using hm.shift
      have st : (teleF p r m J :: Γ.map Fm.shift) ⊢[PRAAx] le (succ (var 0)) (Syn.shift J) ⟶
          (rem (bell (Syn.shift m + Syn.shift J * pw (Syn.shift p) (Syn.shift r))) (Syn.shift p) ≐
            rem (U (succ (var 0)) (Syn.shift r)
              (Syn.shift m + monus (Syn.shift J) (succ (var 0)) * pw (Syn.shift p) (Syn.shift r)))
              (Syn.shift p)) :=
        .impI ((Prf.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)).eqTrans
          (tele_link hq'.wk.wk hQ'.wk.wk Prf.hyp0 hm'.wk.wk))
      simpa [subst_repl_shift, Syn.repl_zero] using st
  have h2 := Prf.allE J hall
  have h3 : Γ ⊢[PRAAx] le J J ⟶ (rem (bell (m + J * pw p r)) p ≐
      rem (U J r (m + monus J J * pw p r)) p) := by
    simpa [Syn.subst_inst_shift, Syn.inst_zero] using h2
  refine (Prf.impE h3 (le_refl J)).eqTrans (cong_of_eq (congrU ?_))
  ipra_lc 𝔞 (pw p r) * natEq (monus_self (Γ := Γ) J)

/-! ## From level `r` to level `r + 1` -/

theorem power_step {p r T m : PTm n} (hp : Γ ⊢[PRAAx] prime p)
    (hQ : Γ ⊢[PRAAx] allB lvB (succ T) (lvP r T p) ≐ one)
    (hm : Γ ⊢[PRAAx] le (m + pw p (succ r)) T) :
    Γ ⊢[PRAAx] rem (bell (m + pw p (succ r))) p ≐ rem (bell (succ m) + succ r * bell m) p := by
  have hq := prime_eq_succ_pred hp
  have e : Γ ⊢[PRAAx] m + pw p (succ r) ≐ m + p * pw p r := by
    ipra_lc natEq (pw_succ (Γ := Γ) p r)
  exact (cong_of_eq (congrBell e)).eqTrans
    ((tele hq hQ (le_congr e (.eqRefl T) hm)).eqTrans (top_cong hp r m))

theorem level_zero (m T p : PTm n) : Γ ⊢[PRAAx] neg (inst2 lvB m (lvP zero T p) ≐ zero) := by
  refine lv_ne (.impI (cong_of_eq ?_))
  have e : (le (m + pw p zero) T :: Γ) ⊢[PRAAx] m + pw p zero ≐ succ m := by
    ipra_lc natEq (pw_zero (Γ := le (m + pw p zero) T :: Γ) p)
  refine (congrBell e).eqTrans ?_
  ipra_ring

theorem level_succ {p r T : PTm n} (hp : Γ ⊢[PRAAx] prime p)
    (hQ : Γ ⊢[PRAAx] allB lvB (succ T) (lvP r T p) ≐ one) :
    Γ ⊢[PRAAx] allB lvB (succ T) (lvP (succ r) T p) ≐ one := by
  refine all_intro lvB (.allI (.impI ?_))
  have e : Syn.shift (lvP (succ r) T p) =
      lvP (succ (Syn.shift r)) (Syn.shift T) (Syn.shift p) := by simp [Syn.shift]
  rw [e]
  have hQ' : (Γ.map Fm.shift) ⊢[PRAAx]
      allB lvB (succ (Syn.shift T)) (lvP (Syn.shift r) (Syn.shift T) (Syn.shift p)) ≐ one := by
    simpa [Fm.shift, Syn.shift] using hQ.shift
  exact lv_ne (.impI (power_step (prime_shift hp).wk.wk hQ'.wk.wk Prf.hyp0))

/-- The induction formula on `r`: the level bit below `T`. -/
abbrev powF (p T : PTm n) : Fm PTm (n + 1) :=
  allB lvB (succ (Syn.shift T)) (lvP (var 0) (Syn.shift T) (Syn.shift p)) ≐ one

/-- Every level holds below every bound. -/
theorem level_all {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (r T : PTm n) :
    Γ ⊢[PRAAx] allB lvB (succ T) (lvP r T p) ≐ one := by
  have hall : Γ ⊢[PRAAx] Fm.all (powF p T) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · have b : Γ ⊢[PRAAx] allB lvB (succ T) (lvP zero T p) ≐ one := by
        refine all_intro lvB (.allI (.impI ?_))
        have e : Syn.shift (lvP zero T p) = lvP zero (Syn.shift T) (Syn.shift p) := by
          simp [Syn.shift]
        rw [e]
        exact level_zero _ _ _
      simpa using b
    · have st : (powF p T :: Γ.map Fm.shift) ⊢[PRAAx]
          allB lvB (succ (Syn.shift T)) (lvP (succ (var 0)) (Syn.shift T) (Syn.shift p)) ≐ one :=
        level_succ (prime_shift hp).wk Prf.hyp0
      simpa [subst_repl_shift, Syn.repl_zero] using st
  have h2 := Prf.allE r hall
  simpa [Syn.subst_inst_shift, Syn.inst_zero] using h2

/-! ## The theorem -/

/-- `thm:touchard-power`: `B_{N+p^r} ≡ B_{N+1} + r B_N (mod p)` for a prime `p`. -/
theorem touchard_power {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (r N : PTm n) :
    Γ ⊢[PRAAx] rem (bell (N + pw p r)) p ≐ rem (bell (succ N) + r * bell N) p :=
  level_at (level_all hp r (N + pw p r)) (le_refl _)

/-- `thm:touchard-power`, closed over `p`, `r`, `N`. -/
theorem touchard_power_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (prime (var 0) ⟶
      (rem (bell (var 2 + pw (var 0) (var 1))) (var 0) ≐
        rem (bell (succ (var 2)) + var 1 * bell (var 2)) (var 0))) :=
  closeUniv 3 (.impI (touchard_power Prf.hyp0 _ _))

end LeanProofs.IPRA.Combinatorics.BellTouchardPower
