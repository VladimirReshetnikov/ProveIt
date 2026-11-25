import IPRADerivations.AnalyticNumberTheory.BrunCounting
import IPRADerivations.AnalyticNumberTheory.PowerResidue
import IPRADerivations.AnalyticNumberTheory.Multiplicative
import IPRADerivations.AnalyticNumberTheory.ConvolutionAssoc
import IPRADerivations.AnalyticNumberTheory.EulerProduct
import IPRADerivations.AnalyticNumberTheory.CoprimeModulus
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.CommonLemmas

/-!
# Counting a progression inside the multiples of `l` (the sieve counting step)

Packet: `analytic-number-theory/prime_distribution_ipra`, `paper/sections/05_sieve.tex`, `eq:crt-count`: "For
`l = [d, e]`, we have `gcd(l, q) = 1`. The simultaneous conditions `n ≡ a (mod q)` and `l ∣ n` select one residue
class modulo `ql`. Counting that class in `1, …, x` gives `#{…} = x/(ql) + r_l`, `|r_l| ≤ 1`."

For `q ≥ 1`, `l ≥ 1`, `gcd(l, q) = 1` and `gcd(a, q) = 1`, with the window `0 ≤ n < X` and

  `C(X) = Σ_{n<X} [n ≡ a (mod q)] [l ∣ n]`,

the two cleared inequalities are `q l · C(X) ≤ X + q l` (`count_le`) and `X ≤ q l · C(X) + q l` (`count_ge`).
For `q ≥ 2` the residue `a` is a unit modulo `q`, so the term `n = 0` is not counted and the window `1 ≤ n ≤ x` is
`X = x + 1`; for `q = 1` every `n` is in the class, the term `n = 0` included.

* `cls_pt`: the summand depends only on `n mod q l` (`Multiplicative.rem_rem_mul`), so `C` is a
  `BrunCounting` sum for the modulus `q l`;
* `ri_pt`, `reindex_eq`, `cM_eq`: over one period the multiples `t = l j` are reindexed by `j < q`;
* `h_pt`: `[l j ≡ a (mod q)] = [j = b]` for `j < q`, where `b = res l q a` is the representative with
  `l b ≡ a` (`PowerResidue.ind_transport`); the Chinese remainder theorem is used only in this explicit form;
* `rho_one`: the class has exactly one element in a period, `ρ = 1` (`Core/Fubini.sum_delta`);
* `count_le`, `count_ge`: `BrunCounting.count_upper`, `count_lower` at `ρ = 1`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.SieveCount

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.BrunCounting (gB g_at A count_upper count_lower)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerResidue (res res_lt ind_transport)
open LeanProofs.IPRA.AnalyticNumberTheory.CoprimeModulus (pos_of_one_le two_le_of_ne)
open LeanProofs.IPRA.AnalyticNumberTheory.SumReindex (riB inst2_riB reindex_eq cM)
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (mulBody count_multiples quo_eq)
open LeanProofs.IPRA.AnalyticNumberTheory.Multiplicative (rem_rem_mul)
open LeanProofs.IPRA.AnalyticNumberTheory.ConvolutionAssoc (pos_of_eq rem_small)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (congrEqb' zero_mul_l one_inst)
open LeanProofs.IPRA.AnalyticNumberTheory.EulerProduct (eqb_comm')
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (eq_of_dvd')
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Bodies -/

/-- `[t ≡ a (mod q)] [l ∣ t]` over `0 = t`, `1 = ⟨q, ⟨l, a⟩⟩`. -/
abbrev fB : PTm 2 :=
  eqb (rem (var 0) (fstT (var 1))) (rem (sndT (sndT (var 1))) (fstT (var 1))) *
    eqb (rem (var 0) (fstT (sndT (var 1)))) zero

theorem inst2_fB (t p : PTm n) : inst2 fB t p =
    eqb (rem t (fstT p)) (rem (sndT (sndT p)) (fstT p)) * eqb (rem t (fstT (sndT p))) zero := by
  simp [inst2]

theorem fB_at (t q l a : PTm n) :
    Γ ⊢[PRAAx] inst2 fB t (pairT q (pairT l a)) ≐ eqb (rem t q) (rem a q) * eqb (rem t l) zero := by
  rw [inst2_fB]
  have f1 := fst_pair (Γ := Γ) q (pairT l a)
  have s1 := snd_pair (Γ := Γ) q (pairT l a)
  have sl : Γ ⊢[PRAAx] fstT (sndT (pairT q (pairT l a))) ≐ l := (congrFst s1).eqTrans (fst_pair l a)
  have sa : Γ ⊢[PRAAx] sndT (sndT (pairT q (pairT l a))) ≐ a := (congrSnd s1).eqTrans (snd_pair l a)
  exact congrMul (congrEqb' (congrAp2 remF (.eqRefl _) f1) (congrAp2 remF sa f1))
    (congrEqb' (congrAp2 remF (.eqRefl _) sl) (.eqRefl _))

/-- `[l j ≡ a (mod q)]` over `0 = j`, `1 = ⟨l, ⟨q, a⟩⟩`. -/
abbrev hB : PTm 2 :=
  eqb (rem (fstT (var 1) * var 0) (fstT (sndT (var 1)))) (rem (sndT (sndT (var 1))) (fstT (sndT (var 1))))

theorem inst2_hB (j x : PTm n) : inst2 hB j x =
    eqb (rem (fstT x * j) (fstT (sndT x))) (rem (sndT (sndT x)) (fstT (sndT x))) := by
  simp [inst2]

theorem hB_at (j l q a : PTm n) :
    Γ ⊢[PRAAx] inst2 hB j (pairT l (pairT q a)) ≐ eqb (rem (l * j) q) (rem a q) := by
  rw [inst2_hB]
  have f1 := fst_pair (Γ := Γ) l (pairT q a)
  have s1 := snd_pair (Γ := Γ) l (pairT q a)
  have sq : Γ ⊢[PRAAx] fstT (sndT (pairT l (pairT q a))) ≐ q := (congrFst s1).eqTrans (fst_pair q a)
  have sa : Γ ⊢[PRAAx] sndT (sndT (pairT l (pairT q a))) ≐ a := (congrSnd s1).eqTrans (snd_pair q a)
  exact congrEqb' (congrAp2 remF (congrMul f1 (.eqRefl _)) sq) (congrAp2 remF sa sq)

/-- The parameter of the count. -/
abbrev par (q l a : PTm n) : PTm n := pairT q (pairT l a)

/-- `C(X) = Σ_{n<X} [n ≡ a (mod q)] [l ∣ n]`, as a `BrunCounting` sum for the modulus `q l`. -/
abbrev cnt (X q l a : PTm n) : PTm n := A fB X (succ (pred (q * l))) (par q l a)

/-! ## Arithmetic helpers -/

alias pos_mul := Common.pos_mul

alias pred_lt := Common.pred_lt

alias mul_one'' := Common.mul_one_right

theorem shift_res0 (l q a : PTm n) : Syn.shift (res l q a) = res (Syn.shift l) (Syn.shift q) (Syn.shift a) := by
  simp only [Syn.shift, PTm.subst_mul, PTm.subst_add, PTm.subst_monus, LeanProofs.IPRA.PTm.subst_pred, subst_eqb,
    subst_ex2, subst_ap2, Bezout.subst_cur, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]

/-- `X R + D R = X + D` for `R = 1`. -/
theorem one_fold {X D R : PTm n} (h : Γ ⊢[PRAAx] R ≐ one) : Γ ⊢[PRAAx] X * R + D * R ≐ X + D := by
  ipra_lc (𝔞 X + 𝔞 D) * natEq h

/-- `D C + D R = D C + D` for `R = 1`. -/
theorem one_fold' {C D R : PTm n} (h : Γ ⊢[PRAAx] R ≐ one) : Γ ⊢[PRAAx] D * C + D * R ≐ D * C + D := by
  ipra_lc 𝔞 D * natEq h

/-! ## The summand -/

/-- The summand of `C` at `t`: it depends only on `t mod q l`. -/
theorem cls_pt {q l a D : PTm n} (hq : Γ ⊢[PRAAx] q ≐ succ (pred q)) (hl : Γ ⊢[PRAAx] l ≐ succ (pred l))
    (hD : Γ ⊢[PRAAx] D ≐ q * l) (t : PTm n) :
    Γ ⊢[PRAAx] inst2 (gB fB) t (pairT D (par q l a)) ≐ eqb (rem t q) (rem a q) * eqb (rem t l) zero := by
  refine (g_at fB t D _).eqTrans ((fB_at _ q l a).eqTrans ?_)
  have rr := rem_rem_mul hq hl t
  have c1 : Γ ⊢[PRAAx] rem (rem t D) q ≐ rem t q :=
    (congrAp2 remF (congrAp2 remF (.eqRefl _) hD) (.eqRefl _)).eqTrans (Prf.andE₁ rr)
  have c2 : Γ ⊢[PRAAx] rem (rem t D) l ≐ rem t l :=
    (congrAp2 remF (congrAp2 remF (.eqRefl _) hD) (.eqRefl _)).eqTrans (Prf.andE₂ rr)
  exact congrMul (congrEqb' c1 (.eqRefl _)) (congrEqb' c2 (.eqRefl _))

/-- The summand in the form `[l ∣ t] h(t / l)`. -/
theorem ri_pt {q l a : PTm n} (hl : Γ ⊢[PRAAx] l ≐ succ (pred l)) (t : PTm n) :
    Γ ⊢[PRAAx] eqb (rem t q) (rem a q) * eqb (rem t l) zero ≐
      inst2 (riB hB) t (pairT l (pairT l (pairT q a))) := by
  rw [inst2_riB]
  have f1 := fst_pair (Γ := Γ) l (pairT l (pairT q a))
  have s1 := snd_pair (Γ := Γ) l (pairT l (pairT q a))
  have eR : Γ ⊢[PRAAx] eqb (rem t (fstT (pairT l (pairT l (pairT q a))))) zero ≐ eqb (rem t l) zero :=
    congrEqb' (congrAp2 remF (.eqRefl _) f1) (.eqRefl _)
  have eH : Γ ⊢[PRAAx] inst2 hB (quo t (fstT (pairT l (pairT l (pairT q a)))))
      (sndT (pairT l (pairT l (pairT q a)))) ≐ eqb (rem (l * quo t l) q) (rem a q) :=
    (congrInst2 hB (congrAp2 quoF (.eqRefl _) f1) s1).eqTrans (hB_at _ l q a)
  refine Prf.eqTrans ?_ (congrMul eR eH).eqSymm
  refine .orE (eq_or_ne (rem t l) zero) ?_ ?_
  · let C : List (Fm PTm n) := (rem t l ≐ zero) :: Γ
    have et := eq_of_dvd' (hl.wk (ψ := rem t l ≐ zero)) (Prf.hyp0 : C ⊢[PRAAx] dvd l t)
    have e1 : C ⊢[PRAAx] eqb (rem t q) (rem a q) ≐ eqb (rem (l * quo t l) q) (rem a q) :=
      congrEqb' (congrAp2 remF et (.eqRefl _)) (.eqRefl _)
    exact (congrMul e1 (.eqRefl _)).eqTrans (mul_comm _ _)
  · have z : (neg (rem t l ≐ zero) :: Γ) ⊢[PRAAx] eqb (rem t l) zero ≐ zero := eqb_of_ne Prf.hyp0
    exact ((congrMul (.eqRefl _) z).eqTrans (mul_zero _)).eqTrans (zero_mul_l z _).eqSymm

/-- There are `q` multiples of `l` below `q l`. -/
theorem cM_eq {q l D : PTm n} (hl : Γ ⊢[PRAAx] l ≐ succ (pred l)) (hD : Γ ⊢[PRAAx] D ≐ q * l) :
    Γ ⊢[PRAAx] cM D l ≐ q := by
  refine (count_multiples hl).eqTrans (quo_eq hl ?_ (pred_lt hl))
  ipra_lc natEq hD

/-- `[l j ≡ a (mod q)] = [j = b]` for `j < q`, with `b = res l q a`. -/
theorem h_pt {q l a j : PTm n} (hq : Γ ⊢[PRAAx] le two q) (hc : Γ ⊢[PRAAx] gcd l q ≐ one)
    (ha : Γ ⊢[PRAAx] gcd a q ≐ one) (hj : Γ ⊢[PRAAx] lt j q) :
    Γ ⊢[PRAAx] inst2 hB j (pairT l (pairT q a)) ≐ inst2 (dB one) j (pairT (res l q a) zero) := by
  refine (hB_at j l q a).eqTrans ((ind_transport hq ha).eqTrans ?_)
  rw [inst2_dB, one_inst]
  have e1 : Γ ⊢[PRAAx] eqb (gcd l q) one ≐ one := eqb_of_eq hc
  have e2 : Γ ⊢[PRAAx] eqb (rem j q) (res l q a) ≐ eqb (fstT (pairT (res l q a) zero)) j :=
    (congrEqb' (rem_small hj) (.eqRefl _)).eqTrans ((eqb_comm' _ _).eqTrans
      (congrEqb' (fst_pair _ _).eqSymm (.eqRefl _)))
  exact (congrMul e1 e2).eqTrans ((one_mul _).eqTrans (mul_one'' _).eqSymm)

/-! ## One element per period -/

/-- One period for `q ≥ 2`: `Σ_{j < q} [l j ≡ a (mod q)] = 1`. -/
theorem period_two {q l a : PTm n} (hq : Γ ⊢[PRAAx] le two q) (hc : Γ ⊢[PRAAx] gcd l q ≐ one)
    (ha : Γ ⊢[PRAAx] gcd a q ≐ one) : Γ ⊢[PRAAx] ap2 (sumF hB) q (pairT l (pairT q a)) ≐ one := by
  -- each `j < q` contributes `[j = b]`
  have s4 : Γ ⊢[PRAAx] ap2 (sumF hB) q (pairT l (pairT q a)) ≐
      ap2 (sumF (dB one)) q (pairT (res l q a) zero) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    have hq' : (Γ.map Fm.shift) ⊢[PRAAx] le two (Syn.shift q) := by
      simpa [Fm.shift, Syn.shift] using hq.shift
    have hc' : (Γ.map Fm.shift) ⊢[PRAAx] gcd (Syn.shift l) (Syn.shift q) ≐ one := by
      have h := hc.shift
      simp only [Fm.shift, Fm.subst_eq, subst_ex2, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at h
      exact h
    have ha' : (Γ.map Fm.shift) ⊢[PRAAx] gcd (Syn.shift a) (Syn.shift q) ≐ one := by
      have h := ha.shift
      simp only [Fm.shift, Fm.subst_eq, subst_ex2, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at h
      exact h
    have sh1 : Syn.shift (pairT l (pairT q a)) = pairT (Syn.shift l) (pairT (Syn.shift q) (Syn.shift a)) := by
      simp [Syn.shift]
    have sh0 : Syn.shift (zero : PTm n) = zero := by simp [Syn.shift]
    have sh2 : Syn.shift (pairT (res l q a) zero) =
        pairT (res (Syn.shift l) (Syn.shift q) (Syn.shift a)) zero := by
      rw [shift_pairT, shift_res0, sh0]
    rw [sh1, sh2]
    exact h_pt hq'.wk hc'.wk ha'.wk Prf.hyp0
  have s5 := sum_delta (Γ := Γ) (one : PTm 2) (N := q) (c := res l q a) (x := zero) (res_lt hq)
  rw [one_inst] at s5
  exact s4.eqTrans s5

/-- One period for `q = 1`: the single term `j = 0`. -/
theorem period_one {q l a : PTm n} (e1 : Γ ⊢[PRAAx] q ≐ one) :
    Γ ⊢[PRAAx] ap2 (sumF hB) q (pairT l (pairT q a)) ≐ one := by
  have ss := sum_succ' (Γ := Γ) hB zero (pairT l (pairT q a))
  have r0 : Γ ⊢[PRAAx] rem (l * zero) q ≐ rem a q :=
    (congrAp2 remF (.eqRefl _) e1).eqTrans ((AnalyticNumberTheory.Euler.rem_one _).eqTrans
      ((AnalyticNumberTheory.Euler.rem_one _).eqSymm.eqTrans (congrAp2 remF (.eqRefl _) e1.eqSymm)))
  have t0 : Γ ⊢[PRAAx] inst2 hB zero (pairT l (pairT q a)) ≐ one :=
    (hB_at zero l q a).eqTrans (eqb_of_eq r0)
  exact (congrAp2 (sumF hB) e1 (.eqRefl _)).eqTrans
    (ss.eqTrans ((congrAdd (sum_zero _ _) t0).eqTrans (zero_add one)))

/-- `ρ = Σ_{t < q l} [t ≡ a (mod q)] [l ∣ t] = 1`. -/
theorem rho_one {q l a : PTm n} (hq : Γ ⊢[PRAAx] le one q) (hl : Γ ⊢[PRAAx] l ≐ succ (pred l))
    (hc : Γ ⊢[PRAAx] gcd l q ≐ one) (ha : Γ ⊢[PRAAx] gcd a q ≐ one) :
    Γ ⊢[PRAAx] cnt (succ (pred (q * l))) q l a ≐ one := by
  have hqp : Γ ⊢[PRAAx] q ≐ succ (pred q) := pos_of_one_le hq
  have hD : Γ ⊢[PRAAx] succ (pred (q * l)) ≐ q * l := (pos_mul hqp hl).eqSymm
  -- the summand as `[l ∣ t] h(t / l)`
  have s1 : Γ ⊢[PRAAx] cnt (succ (pred (q * l))) q l a ≐
      ap2 (sumF (riB hB)) (succ (pred (q * l))) (pairT l (pairT l (pairT q a))) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    have hqp' := MobiusBounds.shift_pos hqp
    have hl' := MobiusBounds.shift_pos hl
    have hD' : (Γ.map Fm.shift) ⊢[PRAAx] succ (pred (Syn.shift q * Syn.shift l)) ≐ Syn.shift q * Syn.shift l :=
      (pos_mul hqp' hl').eqSymm
    have sh1 : Syn.shift (pairT (succ (pred (q * l))) (par q l a)) =
        pairT (succ (pred (Syn.shift q * Syn.shift l))) (par (Syn.shift q) (Syn.shift l) (Syn.shift a)) := by
      simp [Syn.shift]
    have sh2 : Syn.shift (pairT l (pairT l (pairT q a))) =
        pairT (Syn.shift l) (pairT (Syn.shift l) (pairT (Syn.shift q) (Syn.shift a))) := by
      simp [Syn.shift]
    rw [sh1, sh2]
    exact (cls_pt hqp'.wk hl'.wk hD'.wk _).eqTrans (ri_pt hl'.wk _)
  -- reindex the multiples of `l`
  have s2 := reindex_eq (Γ := Γ) hB (x := pairT l (pairT q a)) (succ (pred (q * l))) hl
  have s3 : Γ ⊢[PRAAx] ap2 (sumF hB) (cM (succ (pred (q * l))) l) (pairT l (pairT q a)) ≐
      ap2 (sumF hB) q (pairT l (pairT q a)) := congrAp2 (sumF hB) (cM_eq hl hD) (.eqRefl _)
  -- one period: `q = 1` directly, `q ≥ 2` through the representative `b`
  have s45 : Γ ⊢[PRAAx] ap2 (sumF hB) q (pairT l (pairT q a)) ≐ one := by
    refine .orE (eq_or_ne q one) ?_ ?_
    · exact period_one Prf.hyp0
    · exact period_two (two_le_of_ne (hq.wk (ψ := neg (q ≐ one))) Prf.hyp0) (hc.wk (ψ := neg (q ≐ one)))
        (ha.wk (ψ := neg (q ≐ one)))
  exact s1.eqTrans (s2.eqTrans (s3.eqTrans s45))

/-! ## The count -/

/-- `eq:crt-count`, upper half: `q l · C(X) ≤ X + q l`. -/
theorem count_le {q l a : PTm n} (X : PTm n) (hq : Γ ⊢[PRAAx] le one q) (hl : Γ ⊢[PRAAx] l ≐ succ (pred l))
    (hc : Γ ⊢[PRAAx] gcd l q ≐ one) (ha : Γ ⊢[PRAAx] gcd a q ≐ one) :
    Γ ⊢[PRAAx] le (q * l * cnt X q l a) (X + q * l) := by
  have hD : Γ ⊢[PRAAx] succ (pred (q * l)) ≐ q * l := (pos_mul (pos_of_one_le hq) hl).eqSymm
  have u := count_upper (Γ := Γ) fB X (pred (q * l)) (par q l a)
  have r := rho_one hq hl hc ha
  exact le_congr (congrMul hD (.eqRefl _)) ((one_fold r).eqTrans (congrAdd (.eqRefl _) hD)) u

/-- `eq:crt-count`, lower half: `X ≤ q l · C(X) + q l`. -/
theorem count_ge {q l a : PTm n} (X : PTm n) (hq : Γ ⊢[PRAAx] le one q) (hl : Γ ⊢[PRAAx] l ≐ succ (pred l))
    (hc : Γ ⊢[PRAAx] gcd l q ≐ one) (ha : Γ ⊢[PRAAx] gcd a q ≐ one) :
    Γ ⊢[PRAAx] le X (q * l * cnt X q l a + q * l) := by
  have hD : Γ ⊢[PRAAx] succ (pred (q * l)) ≐ q * l := (pos_mul (pos_of_one_le hq) hl).eqSymm
  have u := count_lower (Γ := Γ) fB X (pred (q * l)) (par q l a)
  have r := rho_one hq hl hc ha
  exact le_congr ((congrMul (.eqRefl _) r).eqTrans (mul_one'' _))
    ((one_fold' r).eqTrans (congrAdd (congrMul hD (.eqRefl _)) hD)) u

/-- The summand of `C(X)` at `t` is `[t ≡ a (mod q)] [l ∣ t]`. -/
theorem cnt_pt {q l a : PTm n} (hq : Γ ⊢[PRAAx] le one q) (hl : Γ ⊢[PRAAx] l ≐ succ (pred l)) (t : PTm n) :
    Γ ⊢[PRAAx] inst2 (gB fB) t (pairT (succ (pred (q * l))) (par q l a)) ≐
      eqb (rem t q) (rem a q) * eqb (rem t l) zero :=
  cls_pt (pos_of_one_le hq) hl (pos_mul (pos_of_one_le hq) hl).eqSymm t

end LeanProofs.IPRA.AnalyticNumberTheory.SieveCount
