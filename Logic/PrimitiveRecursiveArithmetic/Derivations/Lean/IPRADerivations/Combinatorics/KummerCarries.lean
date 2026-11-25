import IPRADerivations.Combinatorics.KummerDigits
import IPRADerivations.AnalyticNumberTheory.FactorialLambda
import IPRADerivations.AnalyticNumberTheory.RSA
import IPRADerivations.Core.SumSplit
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.CertificateTactics

/-!
# Kummer's carry formula

Packet: `diophantine-number-theory/number_theory_ipra_2026-11-22`, `chapters/elementary.tex`, `el:kummer`:

  "For a prime `p` and `0 ≤ k ≤ n`, the exponent of `p` in `C(n, k)` equals the number of carries when adding `k`
  and `n − k` in base `p`."

With `n = a + b`, `k = a`. The carry into position `j` of the base-`p` addition of `a` and `b` is

    c_j = ⌊((a mod p^j) + (b mod p^j)) / p^j⌋                                                    (`cy`),

and this module derives that it is the carry array of the schoolbook addition and counts the valuation:

* `cy_zero`, **`cy_succ`**: `c_0 = 0` and `c_{j+1} = ⌊(a_j + b_j + c_j)/p⌋` with the digits `a_j = ⌊a/p^j⌋ mod p`
  (`rem_digit`: `a mod p^{j+1} = p^j a_j + (a mod p^j)`);
* `cy_le_one`: `c_j ≤ 1`, so `∑_j c_{j+1}` is the number of carries;
* `quo_add_split`: `⌊(a + b)/P⌋ = ⌊a/P⌋ + ⌊b/P⌋ + ⌊((a mod P) + (b mod P))/P⌋`;
* **`kummer_carries`**: `v_p(C(a + b, a)) = ∑_{j < a + b} c_{j+1}` for a prime `p`.

The proof of the last statement is Legendre's formula `v_p(m!) = ∑_{j<m} ⌊m/p^{j+1}⌋` (`LegendreFact`) for
`m = a + b, a, b`, with the two shorter sums extended by zero terms to the common length `a + b` (`Qs_ext`), and
`quo_add_split` summed over `j` (`sum_add3`). The digit-sum form is `KummerDigits.kummer_digits`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.KummerCarries

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (prime fact_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (val pw_pos' lt_pw)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (prime_two)
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusBounds (shift_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.ValuationMul (val_mul val_congr p_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.FactorialLambda (fB sB inst2_fB inst2_sB sum_add2)
open LeanProofs.IPRA.Combinatorics.Binomial (binom pos_mul)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (binom_eq)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open LeanProofs.IPRA.Combinatorics.LegendreDigits (dm dmu pos_mul' quo_quo quo_small qB' qB'_at)
open LeanProofs.IPRA.Combinatorics.LegendreFact (legendre_fact)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (pos_of_eq_mul)
open LeanProofs.IPRA.Foundations.CrossingSearch (monus_of_eq)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Division of a sum -/

/-- `⌊(a + b)/P⌋ = ⌊a/P⌋ + ⌊b/P⌋ + ⌊((a mod P) + (b mod P))/P⌋`. -/
theorem quo_add_split {P : PTm n} (hP : Γ ⊢[PRAAx] P ≐ succ (pred P)) (a b : PTm n) :
    Γ ⊢[PRAAx] quo (a + b) P ≐ quo a P + quo b P + quo (rem a P + rem b P) P := by
  have da := natEq (Prf.andE₁ (dm hP a)); have db := natEq (Prf.andE₁ (dm hP b))
  have s := dm hP (rem a P + rem b P)
  refine Prf.andE₁ (dmu hP (r := rem (rem a P + rem b P) P) ?_ (Prf.andE₂ s))
  ipra_lc da + db + natEq (Prf.andE₁ s)

theorem two_contra {P q r ra rb : PTm n} (la : Γ ⊢[PRAAx] le (succ ra) P) (lb : Γ ⊢[PRAAx] le (succ rb) P)
    (hq : Γ ⊢[PRAAx] le two q) (e : Γ ⊢[PRAAx] ra + rb ≐ P * q + r) : Γ ⊢[PRAAx] le one zero := by
  have x := natEq e
  ipra_le sl la + sl lb + 𝔞 P * sl hq + 𝔞 r + 1 with x

/-- The carry is a bit: `⌊((a mod P) + (b mod P))/P⌋ ≤ 1`. -/
theorem carry_le_one {P : PTm n} (hP : Γ ⊢[PRAAx] P ≐ succ (pred P)) (a b : PTm n) :
    Γ ⊢[PRAAx] le (quo (rem a P + rem b P) P) one := by
  refine .orE (lt_or_le one (quo (rem a P + rem b P) P)) ?_ Prf.hyp0
  have hq : (lt one (quo (rem a P + rem b P) P) :: Γ) ⊢[PRAAx] le two (quo (rem a P + rem b P) P) := Prf.hyp0
  have hP' := hP.wk (ψ := lt one (quo (rem a P + rem b P) P))
  exact lt_zero_absurd _ (two_contra (Prf.andE₂ (dm hP' a)) (Prf.andE₂ (dm hP' b)) hq
    (Prf.andE₁ (dm hP' (rem a P + rem b P))))

/-- `a mod (P p) = P · (⌊a/P⌋ mod p) + (a mod P)`. -/
theorem rem_digit {p P : PTm n} (hP : Γ ⊢[PRAAx] P ≐ succ (pred P)) (hp : Γ ⊢[PRAAx] p ≐ succ (pred p))
    (a : PTm n) : Γ ⊢[PRAAx] rem a (P * p) ≐ P * rem (quo a P) p + rem a P := by
  have d₁ := dm hP a; have d₂ := dm hp (quo a P)
  have e₁ := natEq (Prf.andE₁ d₁); have e₂ := natEq (Prf.andE₁ d₂)
  have hr₁ : Γ ⊢[PRAAx] le (succ (rem a P)) P := Prf.andE₂ d₁
  have hr₂ : Γ ⊢[PRAAx] le (succ (rem (quo a P) p)) p := Prf.andE₂ d₂
  have f₁ := natEq (eq_add_of_le hr₁); have f₂ := natEq (eq_add_of_le hr₂)
  have lt₁ : Γ ⊢[PRAAx] lt (P * rem (quo a P) p + rem a P) (P * p) := by
    refine le_of_eq_add (d := monus P (succ (rem a P)) + P * monus p (succ (rem (quo a P) p))) ?_
    ipra_lc f₁ + 𝔞 P * f₂
  refine Prf.andE₂ (dmu (pos_mul' hP hp) (q := quo (quo a P) p) ?_ lt₁)
  ipra_lc e₁ + 𝔞 P * e₂

/-- The carry out of a position from the two digits and the carry into it. -/
theorem carry_rec {p P : PTm n} (hP : Γ ⊢[PRAAx] P ≐ succ (pred P)) (hp : Γ ⊢[PRAAx] p ≐ succ (pred p))
    (a b : PTm n) :
    Γ ⊢[PRAAx] quo (rem a (P * p) + rem b (P * p)) (P * p) ≐
      quo (rem (quo a P) p + rem (quo b P) p + quo (rem a P + rem b P) P) p := by
  have x₁ := natEq (rem_digit hP hp a); have x₂ := natEq (rem_digit hP hp b)
  have s := dm hP (rem a P + rem b P)
  have q1 : Γ ⊢[PRAAx] quo (rem a (P * p) + rem b (P * p)) P ≐
      rem (quo a P) p + rem (quo b P) p + quo (rem a P + rem b P) P := by
    refine Prf.andE₁ (dmu hP (r := rem (rem a P + rem b P) P) ?_ (Prf.andE₂ s))
    ipra_lc x₁ + x₂ + natEq (Prf.andE₁ s)
  exact (quo_quo hP hp _).eqSymm.eqTrans (congrAp2 quoF q1 (.eqRefl _))

/-! ## The carry array -/

/-- The carry into position `j`: `c_j = ⌊((a mod p^j) + (b mod p^j))/p^j⌋`. -/
abbrev cy (p a b j : PTm n) : PTm n := quo (rem a (pw p j) + rem b (pw p j)) (pw p j)

theorem congr_cy {p a b j M : PTm n} (h : Γ ⊢[PRAAx] pw p j ≐ M) :
    Γ ⊢[PRAAx] cy p a b j ≐ quo (rem a M + rem b M) M :=
  congrAp2 quoF (congrAdd (congrAp2 remF (.eqRefl _) h) (congrAp2 remF (.eqRefl _) h)) h

/-- `c_0 = 0`. -/
theorem cy_zero (p a b : PTm n) : Γ ⊢[PRAAx] cy p a b zero ≐ zero := by
  have r : ∀ x : PTm n, Γ ⊢[PRAAx] rem x one ≐ zero := fun x => AnalyticNumberTheory.Euler.rem_one x
  exact (congr_cy (pw_zero p)).eqTrans ((congrAp2 quoF (congrAdd (r a) (r b)) (.eqRefl _)).eqTrans
    ((AnalyticNumberTheory.RSA.quo_one _).eqTrans (add_zero _)))

/-- **The carry recursion**: `c_{j+1} = ⌊(a_j + b_j + c_j)/p⌋` with the base-`p` digits `a_j`, `b_j`. -/
theorem cy_succ {p : PTm n} (hp : Γ ⊢[PRAAx] p ≐ succ (pred p)) (a b j : PTm n) :
    Γ ⊢[PRAAx] cy p a b (succ j) ≐
      quo (rem (quo a (pw p j)) p + rem (quo b (pw p j)) p + cy p a b j) p :=
  (congr_cy (pw_succ p j)).eqTrans (carry_rec (pw_pos' hp j) hp a b)

/-- `c_j ≤ 1`. -/
theorem cy_le_one {p : PTm n} (hp : Γ ⊢[PRAAx] p ≐ succ (pred p)) (a b j : PTm n) :
    Γ ⊢[PRAAx] le (cy p a b j) one := carry_le_one (pw_pos' hp j) a b

/-- `c_{j+1}`, over `0 = j`, `1 = ⟨p, ⟨a, b⟩⟩`. -/
abbrev cyB : PTm 2 :=
  quo (rem (fstT (sndT (var 1))) (pw (fstT (var 1)) (succ (var 0))) +
    rem (sndT (sndT (var 1))) (pw (fstT (var 1)) (succ (var 0)))) (pw (fstT (var 1)) (succ (var 0)))

theorem inst2_cy (j y : PTm n) :
    inst2 cyB j y = quo (rem (fstT (sndT y)) (pw (fstT y) (succ j)) +
      rem (sndT (sndT y)) (pw (fstT y) (succ j))) (pw (fstT y) (succ j)) := by simp [inst2]

theorem cy_at (j p a b : PTm n) :
    Γ ⊢[PRAAx] inst2 cyB j (pairT p (pairT a b)) ≐ cy p a b (succ j) := by
  rw [inst2_cy]
  have ep : Γ ⊢[PRAAx] pw (fstT (pairT p (pairT a b))) (succ j) ≐ pw p (succ j) :=
    congrPw (fst_pair _ _) (.eqRefl _)
  exact congrAp2 quoF (congrAdd
    (congrAp2 remF ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)) ep)
    (congrAp2 remF ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)) ep)) ep

/-! ## Sums -/

theorem assoc_r (A B C : PTm n) : Γ ⊢[PRAAx] (A + B) + C ≐ A + (B + C) := by
  ipra_ring

/-- `k(j, z) = f(j, x) + g(j, y) + h(j, w)` below the bound gives `∑ k = ∑ f + ∑ g + ∑ h`. -/
theorem sum_add3 (f g h k : PTm 2) {N x y w z : PTm n}
    (hp : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ (inst2 k (var 0) (Syn.shift z) ≐
      inst2 f (var 0) (Syn.shift x) + inst2 g (var 0) (Syn.shift y) + inst2 h (var 0) (Syn.shift w)))) :
    Γ ⊢[PRAAx] ap2 (sumF k) N z ≐ ap2 (sumF f) N x + ap2 (sumF g) N y + ap2 (sumF h) N w := by
  have pt2 : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (inst2 (addBody (fB g) (sB h)) (var 0) (Syn.shift (pairT y w)) ≐
        inst2 g (var 0) (Syn.shift y) + inst2 h (var 0) (Syn.shift w))) := by
    refine .allI (.impI ?_)
    rw [inst2_addBody, inst2_fB, inst2_sB, shift_pairT]
    exact congrAdd (congrInst2 g (.eqRefl _) (fst_pair _ _)) (congrInst2 h (.eqRefl _) (snd_pair _ _))
  have t2 := sum_add2 g h (addBody (fB g) (sB h)) (K := N) (x := y) (x' := w) (z := pairT y w) pt2
  have t1 := sum_add2 f (addBody (fB g) (sB h)) k (K := N) (x := x) (x' := pairT y w) (z := z)
    (.allI (.impI ((Prf.impE hp.allOpen.wk Prf.hyp0).eqTrans ((assoc_r _ _ _).eqTrans
      (congrAdd (.eqRefl _) (Prf.impE pt2.allOpen.wk Prf.hyp0).eqSymm)))))
  exact t1.eqTrans ((congrAdd (.eqRefl _) t2).eqTrans (assoc_r _ _ _).eqSymm)

/-- Legendre's sum for `m` extended by zero terms: `∑_{j < m + K} ⌊m/p^{j+1}⌋ = ∑_{j < m} ⌊m/p^{j+1}⌋`. -/
theorem Qs_ext {p m : PTm n} (hp2 : Γ ⊢[PRAAx] le two p) (K : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF qB') (m + K) (pairT p m) ≐ ap2 (sumF qB') m (pairT p m) := by
  have hp2' : (Γ.map Fm.shift) ⊢[PRAAx] le two (Syn.shift p) := by
    simpa [Fm.shift, Syn.shift] using hp2.shift
  have z : Γ ⊢[PRAAx] ap2 (sumF (offB qB')) K (pairT m (pairT p m)) ≐ zero := by
    refine sum_zero_of_bounded (offB qB') (pairT m (pairT p m)) K (.allI (.impI ?_))
    rw [shift_pairT, shift_pairT, inst2_offB]
    have hp2'' := hp2'.wk (ψ := lt (var 0) (Syn.shift K))
    have l1 := lt_pw hp2'' (succ (Syn.shift m + var 0))
    have l2 : (lt (var 0) (Syn.shift K) :: Γ.map Fm.shift) ⊢[PRAAx]
        le (succ (Syn.shift m)) (succ (succ (Syn.shift m + var 0))) :=
      (succ_monus_succ _ _).eqTrans (le_trans (le_add_right _ _) (le_succ_self _))
    exact (congrInst2 qB' (congrAdd (fst_pair _ _) (.eqRefl _)) (snd_pair _ _)).eqTrans
      ((qB'_at _ _ _).eqTrans (quo_small (pw_pos' (p_pos hp2'') _) (le_trans l2 l1)))
  exact (sum_split qB' m K (pairT p m)).eqTrans ((congrAdd (.eqRefl _) z).eqTrans (add_zero _))

/-! ## Kummer's formula -/

theorem pt_split {p : PTm n} (hp : Γ ⊢[PRAAx] p ≐ succ (pred p)) (j a b : PTm n) :
    Γ ⊢[PRAAx] inst2 qB' j (pairT p (a + b)) ≐
      inst2 qB' j (pairT p a) + inst2 qB' j (pairT p b) + inst2 cyB j (pairT p (pairT a b)) :=
  (qB'_at j p (a + b)).eqTrans ((quo_add_split (pw_pos' hp (succ j)) a b).eqTrans
    (congrAdd (congrAdd (qB'_at j p a).eqSymm (qB'_at j p b).eqSymm) (cy_at j p a b).eqSymm))

theorem fin_alg {Vn Va Vb Vc Sa Sb Sn C : PTm n} (vn : Γ ⊢[PRAAx] Vn ≐ (Va + Vb) + Vc)
    (La : Γ ⊢[PRAAx] Va ≐ Sa) (Lb : Γ ⊢[PRAAx] Vb ≐ Sb) (Ln : Γ ⊢[PRAAx] Vn ≐ Sn)
    (S3 : Γ ⊢[PRAAx] Sn ≐ Sa + Sb + C) : Γ ⊢[PRAAx] Vc ≐ C := by
  ipra_lc -natEq vn + natEq Ln - natEq La - natEq Lb + natEq S3

/-- **Kummer's carry formula**: for a prime `p`, `v_p(C(a + b, a)) = ∑_{j < a + b} c_{j+1}`, the number of carries
in the base-`p` addition of `a` and `b`. -/
theorem kummer_carries {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (a b : PTm n) :
    Γ ⊢[PRAAx] val p (binom (a + b) a) ≐ ap2 (sumF cyB) (a + b) (pairT p (pairT a b)) := by
  have h2 := prime_two hp
  have ppos := p_pos h2
  have hle : Γ ⊢[PRAAx] le a (a + b) := le_add_right a b
  have mb : Γ ⊢[PRAAx] monus (a + b) a ≐ b := monus_of_eq (.eqRefl _)
  have e1 : Γ ⊢[PRAAx] fact (a + b) ≐ (fact a * fact b) * binom (a + b) a :=
    (binom_eq hle).eqTrans (congrMul (congrMul (.eqRefl _) (congrAp2 factF mb (.eqRefl _))) (.eqRefl _))
  have fab := pos_mul (fact_pos (Γ := Γ) a) (fact_pos b)
  have bpos := pos_of_eq_mul (fact_pos (Γ := Γ) (a + b)) e1
  have vn : Γ ⊢[PRAAx] val p (fact (a + b)) ≐ (val p (fact a) + val p (fact b)) + val p (binom (a + b) a) :=
    (val_congr p e1).eqTrans ((val_mul hp fab bpos).eqTrans
      (congrAdd (val_mul hp (fact_pos a) (fact_pos b)) (.eqRefl _)))
  have La : Γ ⊢[PRAAx] val p (fact a) ≐ ap2 (sumF qB') (a + b) (pairT p a) :=
    (legendre_fact hp a).eqTrans (Qs_ext h2 b).eqSymm
  have Lb : Γ ⊢[PRAAx] val p (fact b) ≐ ap2 (sumF qB') (a + b) (pairT p b) :=
    (legendre_fact hp b).eqTrans ((Qs_ext h2 a).eqSymm.eqTrans
      (congrAp2 (sumF qB') (add_comm b a) (.eqRefl _)))
  have Ln : Γ ⊢[PRAAx] val p (fact (a + b)) ≐ ap2 (sumF qB') (a + b) (pairT p (a + b)) :=
    legendre_fact hp (a + b)
  have S3 : Γ ⊢[PRAAx] ap2 (sumF qB') (a + b) (pairT p (a + b)) ≐
      ap2 (sumF qB') (a + b) (pairT p a) + ap2 (sumF qB') (a + b) (pairT p b) +
        ap2 (sumF cyB) (a + b) (pairT p (pairT a b)) := by
    refine sum_add3 qB' qB' cyB qB' (.allI (.impI ?_))
    have s1 : Syn.shift (pairT p (a + b)) = pairT (Syn.shift p) (Syn.shift a + Syn.shift b) := by
      simp [Syn.shift]
    have s2 : Syn.shift (pairT p a) = pairT (Syn.shift p) (Syn.shift a) := by simp [Syn.shift]
    have s3 : Syn.shift (pairT p b) = pairT (Syn.shift p) (Syn.shift b) := by simp [Syn.shift]
    have s4 : Syn.shift (pairT p (pairT a b)) = pairT (Syn.shift p) (pairT (Syn.shift a) (Syn.shift b)) := by
      simp [Syn.shift]
    rw [s1, s2, s3, s4]
    exact pt_split (shift_pos ppos).wk _ _ _
  exact fin_alg vn La Lb Ln S3

end LeanProofs.IPRA.Combinatorics.KummerCarries
