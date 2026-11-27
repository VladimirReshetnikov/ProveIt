import IPRADerivations.AnalyticNumberTheory.DenominatorSquarefree
import IPRADerivations.AnalyticNumberTheory.FiniteSieve

/-!
# The denominator bound `G_q(z) ≥ (φ(q)/q) H_z` and the second sieve inequality

Packet: `analytic-number-theory/prime_distribution_ipra`, `paper/sections/05_sieve.tex`, `eq:sieve-denominator`
and the second inequality of `eq:finite-sieve` (`thm:finite-sieve`):

  "`H_z ≤ H_q(z) ∏_{p ∣ q} p/(p − 1) = (q/φ(q)) H_q(z)`. … Thus `G_q(z) ≥ (φ(q)/q) H_z`. This proves the
  second inequality of `eq:finite-sieve`."

With `H^{(a)}(N) = ∑_{1 ≤ m < N} [gcd(m, a) = 1] ⌊F/m⌋` (`DenominatorSmooth.Hq`):

* `pt_step`, **`harm_step`**: for a prime `p`, `p · H^{(a)}(N) ≤ p · H^{(ap)}(N) + H^{(a)}(N)`. The terms with
  `p ∣ m` are reindexed by `m = p k` (`SumReindex.reindex_le`), and `p ⌊F/(pk)⌋ ≤ ⌊F/k⌋` (`quo_scale`);
* `step_dvd`, `step_coprime`: the step from `m` to `ℓ m` for a prime `ℓ`, with `φ(ℓ m) = ℓ φ(m)` when `ℓ ∣ m`
  and `φ(ℓ m) = (ℓ − 1) φ(m)` otherwise;
* **`harm_factor`**: `φ(q) · H^{(1)}(N) ≤ q · H^{(q)}(N)` for `q ≥ 1`, by strong induction on `q` through its least
  prime factor. The paper's product of finite geometric sums over the primes of `q` is not used;
* `Hz`, `Hq_one`: `H^{(1)}(N) = ∑_{1 ≤ m < N} ⌊F/m⌋`;
* **`sieve_denominator`**: `φ(q) · ∑_{1 ≤ m ≤ z} ⌊z!/m⌋ ≤ q · z! G_q(z)` for `q ≥ 1`, that is
  `G_q(z) ≥ (φ(q)/q) H_z` (`eq:sieve-denominator`);
* **`finite_sieve_second`**: for `q ≥ 1`, `gcd(a, q) = 1`, `z ≥ 1`, with `H = ∑_{1 ≤ m ≤ z} ⌊z!/m⌋ = z! H_z`,

    `φ(q) H · π(X; q, a) ≤ X z! + φ(q) H (z² + z)`,

  that is `π(X; q, a) ≤ X/(φ(q) H_z) + z² + z`.

The modulus is any `q ≥ 1`, as in the first inequality `FiniteSieve.finite_sieve`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.DenominatorBound

open_ipra exports
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (phi totBody)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (congrSg congrEqb' zero_mul_l)
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusBounds (shift_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.SumPhi (shift_mul')
open LeanProofs.IPRA.AnalyticNumberTheory.PhiPower (pow_point phi_mul_pow_at)
open LeanProofs.IPRA.AnalyticNumberTheory.Smooth (lpf_two K_split cof_pos cof_lt)
open LeanProofs.IPRA.AnalyticNumberTheory.SumReindex (riB inst2_riB reindex_le le_quo_of_mul_le)
open LeanProofs.IPRA.AnalyticNumberTheory.FactorialLambda (fB sB inst2_fB inst2_sB sum_add2)
open LeanProofs.IPRA.AnalyticNumberTheory.EulerDomination (le_zero_of)
open LeanProofs.IPRA.AnalyticNumberTheory.FiniteSieve (finite_sieve)
open LeanProofs.IPRA.AnalyticNumberTheory.DenominatorRange (P3 P3_L P3_z)
open LeanProofs.IPRA.AnalyticNumberTheory.DenominatorSmooth (sum_le2 two_alg hqB hq_at Hq)
open LeanProofs.IPRA.AnalyticNumberTheory.DenominatorSquarefree (Hq_le_Asum)
open LeanProofs.IPRA.Probability.Lotus (cmB sum_const_mul)
open LeanProofs.IPRA.Probability.Independence (cm_pt)
open LeanProofs.IPRA.DiophantineNumberTheory.QuarticStep (congrGcd)
open LeanProofs.IPRA.DiophantineNumberTheory.Hurwitz (add_le_add)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## A sum bounded by two sums -/

/-- `f(j, x) ≤ g(j, y) + h(j, w)` below the bound gives `∑ f ≤ ∑ g + ∑ h`. -/
theorem sum_le3 (f g h : PTm 2) (x y w N : PTm n)
    (hp : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (inst2 f (var 0) (Syn.shift x)) (inst2 g (var 0) (Syn.shift y) + inst2 h (var 0) (Syn.shift w)))) :
    Γ ⊢[PRAAx] le (ap2 (sumF f) N x) (ap2 (sumF g) N y + ap2 (sumF h) N w) := by
  have pt : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (inst2 (addBody (fB g) (sB h)) (var 0) (Syn.shift (pairT y w)) ≐
        inst2 g (var 0) (Syn.shift y) + inst2 h (var 0) (Syn.shift w))) := by
    refine .allI (.impI ?_)
    rw [inst2_addBody, inst2_fB, inst2_sB, shift_pairT]
    exact congrAdd (congrInst2 g (.eqRefl _) (fst_pair _ _)) (congrInst2 h (.eqRefl _) (snd_pair _ _))
  refine le_congr (.eqRefl _)
    (sum_add2 g h (addBody (fB g) (sB h)) (K := N) (x := y) (x' := w) (z := pairT y w) pt) ?_
  refine sum_le2 f (addBody (fB g) (sB h)) x (pairT y w) N (.allI (.impI ?_))
  exact le_congr (.eqRefl _) (Prf.impE pt.allOpen.wk Prf.hyp0).eqSymm (.impE hp.allOpen.wk Prf.hyp0)

/-! ## The term at a multiple of `p` -/

/-- The term `[m ≥ 1][gcd(m, q) = 1] ⌊F/m⌋` of `H^{(q)}`. -/
abbrev hT (q F m : PTm n) : PTm n := sg m * (eqb (gcd m q) one * quo F m)

/-- `m ⌊F/m⌋ ≤ F` for `m ≥ 1`. -/
theorem quo_mul_le {m : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (F : PTm n) :
    Γ ⊢[PRAAx] le (m * quo F m) F := Division.mul_quo_le hm

theorem scale_alg {p k m Q : PTm n} (e : Γ ⊢[PRAAx] m ≐ p * k) : Γ ⊢[PRAAx] m * Q ≐ k * (p * Q) := by
  ipra_lc 𝔞 Q * natEq e

/-- `p ⌊F/(pk)⌋ ≤ ⌊F/k⌋` for `k ≥ 1`. -/
theorem quo_scale {p k m : PTm n} (F : PTm n) (hk : Γ ⊢[PRAAx] k ≐ succ (pred k))
    (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (e : Γ ⊢[PRAAx] m ≐ p * k) :
    Γ ⊢[PRAAx] le (p * quo F m) (quo F k) :=
  le_quo_of_mul_le hk (le_congr (scale_alg e) (.eqRefl _) (quo_mul_le hm F))

theorem bits1 {s b X : PTm n} (hs : Γ ⊢[PRAAx] s ≐ one) (hb : Γ ⊢[PRAAx] b ≐ one) :
    Γ ⊢[PRAAx] s * (b * X) ≐ X := by
  ipra_lc 𝔞 b * 𝔞 X * natEq hs + 𝔞 X * natEq hb

theorem bits2 {c s b X : PTm n} (hc : Γ ⊢[PRAAx] c ≐ one) (hs : Γ ⊢[PRAAx] s ≐ one)
    (hb : Γ ⊢[PRAAx] b ≐ one) : Γ ⊢[PRAAx] c * (s * (b * X)) ≐ X := by
  ipra_lc 𝔞 s * 𝔞 b * 𝔞 X * natEq hc + 𝔞 b * 𝔞 X * natEq hs + 𝔞 X * natEq hb

theorem comm_alg (P R : PTm n) : Γ ⊢[PRAAx] P + R ≐ R + P := by ipra_ring

/-- The term at `m`: `p · t_a(m) ≤ p · t_{ap}(m) + [p ∣ m] t_a(m/p)`. -/
theorem pt_step {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (a F m : PTm n) :
    Γ ⊢[PRAAx] le (p * hT a F m) (p * hT (a * p) F m + eqb (rem m p) zero * hT a F (quo m p)) := by
  have ppos := prime_eq_succ_pred hp
  refine .orE (zero_or_succ m) ?_ ?_
  · exact le_zero_of ((congrMul (.eqRefl _) (zero_mul_l ((congrSg Prf.hyp0).eqTrans sg_zero) _)).eqTrans
      (mul_zero _))
  · let C : List (Fm PTm n) := (m ≐ succ (pred m)) :: Γ
    have hm : C ⊢[PRAAx] m ≐ succ (pred m) := Prf.hyp0
    refine .orE (eqb_cases (gcd m a) one) ?_ ?_
    · exact le_zero_of ((congrMul (.eqRefl _)
        ((congrMul (.eqRefl _) (zero_mul_l Prf.hyp0 _)).eqTrans (mul_zero _))).eqTrans (mul_zero _))
    · let D : List (Fm PTm n) := (eqb (gcd m a) one ≐ one) :: C
      have b1 : D ⊢[PRAAx] eqb (gcd m a) one ≐ one := Prf.hyp0
      have g1 : D ⊢[PRAAx] gcd m a ≐ one := eq_of_eqb b1
      refine .orE (eq_or_ne (rem m p) zero) ?_ ?_
      · -- `p ∣ m`
        let E : List (Fm PTm n) := (rem m p ≐ zero) :: D
        have hr : E ⊢[PRAAx] rem m p ≐ zero := Prf.hyp0
        have em : E ⊢[PRAAx] m ≐ p * quo m p := eq_of_dvd' ppos.wk.wk.wk hr
        have kpos : E ⊢[PRAAx] quo m p ≐ succ (pred (quo m p)) := pos_of_eq_mul hm.wk.wk em
        have dk : E ⊢[PRAAx] dvd (quo m p) m := dvd_of_eq' kpos (em.eqTrans (mul_comm _ _))
        have gk : E ⊢[PRAAx] gcd (quo m p) a ≐ one := coprime_dvd_left kpos dk g1.wk
        have hs := quo_scale F kpos hm.wk.wk em
        have eL : E ⊢[PRAAx] p * hT a F m ≐ p * quo F m :=
          congrMul (.eqRefl _) (bits1 ((congrSg hm.wk.wk).eqTrans (sg_succ _)) b1.wk)
        have eR : E ⊢[PRAAx] eqb (rem m p) zero * hT a F (quo m p) ≐ quo F (quo m p) :=
          bits2 (eqb_of_eq hr) ((congrSg kpos).eqTrans (sg_succ _)) (eqb_of_eq gk)
        exact le_trans (le_congr eL.eqSymm eR.eqSymm hs)
          (le_of_eq_add (d := p * hT (a * p) F m) (comm_alg _ _))
      · -- `p ∤ m`
        let E : List (Fm PTm n) := neg (rem m p ≐ zero) :: D
        have hn : E ⊢[PRAAx] neg (dvd p m) := Prf.hyp0
        have gp : E ⊢[PRAAx] gcd p m ≐ one := gcd_prime hp.wk.wk.wk hn
        have gm : E ⊢[PRAAx] gcd m p ≐ one := gcd_comm_one hm.wk.wk gp
        have gap : E ⊢[PRAAx] gcd m (a * p) ≐ one := coprime_mul hm.wk.wk g1.wk gm
        have e : E ⊢[PRAAx] p * hT (a * p) F m ≐ p * hT a F m :=
          congrMul (.eqRefl _) (congrMul (.eqRefl _)
            (congrMul ((eqb_of_eq gap).eqTrans b1.wk.eqSymm) (.eqRefl _)))
        exact le_of_eq_add (d := eqb (rem m p) zero * hT a F (quo m p)) (congrAdd e (.eqRefl _))

/-! ## The prime step for the coprime harmonic sums -/

theorem cm_at (p q F m : PTm n) :
    Γ ⊢[PRAAx] inst2 (cmB hqB) m (pairT p (pairT q F)) ≐ p * hT q F m :=
  (cm_pt hqB m p (pairT q F)).eqTrans (congrMul (.eqRefl _) (hq_at m q F))

theorem ri_at (p q F m : PTm n) :
    Γ ⊢[PRAAx] inst2 (riB hqB) m (pairT p (pairT q F)) ≐ eqb (rem m p) zero * hT q F (quo m p) := by
  rw [inst2_riB]
  exact congrMul (congrEqb' (congrAp2 remF (.eqRefl _) (fst_pair _ _)) (.eqRefl _))
    ((congrInst2 hqB (congrAp2 quoF (.eqRefl _) (fst_pair _ _)) (snd_pair _ _)).eqTrans (hq_at _ _ _))

/-- **The prime step**: `p · H^{(a)}(N) ≤ p · H^{(ap)}(N) + H^{(a)}(N)` for a prime `p`. -/
theorem harm_step {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (a F N : PTm n) :
    Γ ⊢[PRAAx] le (p * Hq a F N) (p * Hq (a * p) F N + Hq a F N) := by
  have ppos := prime_eq_succ_pred hp
  have hp' := AnalyticNumberTheory.Fermat.prime_shift hp
  have h3 : Γ ⊢[PRAAx] le (ap2 (sumF (cmB hqB)) N (pairT p (pairT a F)))
      (ap2 (sumF (cmB hqB)) N (pairT p (pairT (a * p) F)) +
        ap2 (sumF (riB hqB)) N (pairT p (pairT a F))) := by
    refine sum_le3 (cmB hqB) (cmB hqB) (riB hqB) _ _ _ N (.allI (.impI ?_))
    simp only [shift_pairT, shift_mul']
    exact le_congr (cm_at _ _ _ _).eqSymm (congrAdd (cm_at _ _ _ _).eqSymm (ri_at _ _ _ _).eqSymm)
      (pt_step hp'.wk _ _ _)
  exact le_trans
    (le_congr (sum_const_mul hqB N p (pairT a F))
      (congrAdd (sum_const_mul hqB N p (pairT (a * p) F)) (.eqRefl _)) h3)
    (add_le_add (le_refl _) (reindex_le hqB N ppos))

/-- `H^{(aM)} = H^{(a)}` when every prime of `M` divides `a` (`M ∣ a^t`). -/
theorem Hq_pow {a M t : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (hd : Γ ⊢[PRAAx] dvd M (pw a t)) (F N : PTm n) : Γ ⊢[PRAAx] Hq (a * M) F N ≐ Hq a F N := by
  have hd' : Γ.map Fm.shift ⊢[PRAAx] dvd (Syn.shift M) (pw (Syn.shift a) (Syn.shift t)) := by
    simpa only [Syn.shift, subst_ap2] using Gcd.shift_dvd hd
  refine sum_congr_bounded hqB hqB (pairT (a * M) F) (pairT a F) N (.allI (.impI ?_))
  simp only [shift_pairT, shift_mul']
  exact (hq_at _ _ _).eqTrans ((congrMul (.eqRefl _)
    (congrMul (pow_point (shift_pos ha).wk (shift_pos hM).wk hd'.wk _) (.eqRefl _))).eqTrans
    (hq_at _ _ _).eqSymm)

/-! ## The step from `m` to `ℓ m` -/

theorem algA {l m f fK H1 Hm HK : PTm n} (eφ : Γ ⊢[PRAAx] fK ≐ l * f) (eH : Γ ⊢[PRAAx] HK ≐ Hm)
    (ih : Γ ⊢[PRAAx] le (f * H1) (m * Hm)) : Γ ⊢[PRAAx] le (fK * H1) ((l * m) * HK) := by
  have x := natEq eφ; have y := natEq eH
  ipra_le 𝔞 l * sl ih with 𝔞 l * 𝔞 m * y - 𝔞 H1 * x

theorem algB {l m f fl fK H1 Hm HmL HK : PTm n} (e1 : Γ ⊢[PRAAx] fK ≐ fl * f)
    (e0 : Γ ⊢[PRAAx] fl + one ≐ l) (eH : Γ ⊢[PRAAx] HK ≐ HmL)
    (hs : Γ ⊢[PRAAx] le (l * Hm) (l * HmL + Hm)) (ih : Γ ⊢[PRAAx] le (f * H1) (m * Hm)) :
    Γ ⊢[PRAAx] le (fK * H1) ((l * m) * HK) := by
  have x1 := natEq e1; have x0 := natEq e0; have y := natEq eH
  ipra_le 𝔞 fl * sl ih + 𝔞 m * sl hs with 𝔞 l * 𝔞 m * y - 𝔞 H1 * x1 - 𝔞 m * 𝔞 Hm * x0

theorem phi_comm (l m : PTm n) : Γ ⊢[PRAAx] phi (l * m) ≐ phi (m * l) :=
  congrAp2 (sumF totBody) (mul_comm _ _) (mul_comm _ _)

theorem Hq_comm (l m F N : PTm n) : Γ ⊢[PRAAx] Hq (l * m) F N ≐ Hq (m * l) F N :=
  congrAp2 (sumF hqB) (.eqRefl _) (congrPairT (mul_comm _ _) (.eqRefl _))

/-- The step for a prime `ℓ ∣ m`: `φ(ℓ m) = ℓ φ(m)` and `H^{(ℓ m)} = H^{(m)}`. -/
theorem step_dvd {l m F N : PTm n} (hp : Γ ⊢[PRAAx] prime l) (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (hd : Γ ⊢[PRAAx] dvd l m) (ih : Γ ⊢[PRAAx] le (phi m * Hq one F N) (m * Hq m F N)) :
    Γ ⊢[PRAAx] le (phi (l * m) * Hq one F N) ((l * m) * Hq (l * m) F N) := by
  have ppos := prime_eq_succ_pred hp
  have hd1 : Γ ⊢[PRAAx] dvd l (pw m one) := dvd_congr (pw_one m).eqSymm hd
  exact algA ((phi_comm l m).eqTrans (phi_mul_pow_at hm ppos hd1))
    ((Hq_comm l m F N).eqTrans (Hq_pow hm ppos hd1 F N)) ih

/-- The step for a prime `ℓ ∤ m`: `φ(ℓ m) = (ℓ − 1) φ(m)` and the prime step for the sums. -/
theorem step_coprime {l m F N : PTm n} (hp : Γ ⊢[PRAAx] prime l) (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (hn : Γ ⊢[PRAAx] neg (dvd l m)) (ih : Γ ⊢[PRAAx] le (phi m * Hq one F N) (m * Hq m F N)) :
    Γ ⊢[PRAAx] le (phi (l * m) * Hq one F N) ((l * m) * Hq (l * m) F N) := by
  have ppos := prime_eq_succ_pred hp
  have gp : Γ ⊢[PRAAx] gcd l m ≐ one := gcd_prime hp hn
  exact algB (phi_mul_at ppos hm gp) (AnalyticNumberTheory.GoldbachPhi.phi_prime hp) (Hq_comm l m F N)
    (harm_step hp m F N) ih

/-! ## The strong induction on the modulus -/

/-- The violation `[q ≥ 1][φ(q) H^{(1)}(N) > q H^{(q)}(N)]`, over `0 = q`, `1 = ⟨F, N⟩`. -/
abbrev wB : PTm 2 :=
  sg (var 0) * sg (monus
    (ap2 (sumF totBody) (var 0) (var 0) * ap2 (sumF hqB) (sndT (var 1)) (pairT one (fstT (var 1))))
    (var 0 * ap2 (sumF hqB) (sndT (var 1)) (pairT (var 0) (fstT (var 1)))))

theorem inst2_w (q y : PTm n) :
    inst2 wB q y =
      sg q * sg (monus (phi q * Hq one (fstT y) (sndT y)) (q * Hq q (fstT y) (sndT y))) := by
  simp only [inst2, PTm.subst_mul, PTm.subst_monus, subst_ap2, subst_pairT, subst_fstT, subst_sndT, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]

theorem viol_of {K A B : PTm n} (h : Γ ⊢[PRAAx] le A B) : Γ ⊢[PRAAx] sg K * sg (monus A B) ≐ zero :=
  (congrMul (.eqRefl _) ((congrSg h).eqTrans sg_zero)).eqTrans (mul_zero _)

theorem one_fac {s X : PTm n} (hs : Γ ⊢[PRAAx] s ≐ one) (h : Γ ⊢[PRAAx] s * X ≐ zero) :
    Γ ⊢[PRAAx] X ≐ zero := by
  ipra_lc natEq h - 𝔞 X * natEq hs

theorem of_viol {K A B : PTm n} (hK : Γ ⊢[PRAAx] K ≐ succ (pred K))
    (h : Γ ⊢[PRAAx] sg K * sg (monus A B) ≐ zero) : Γ ⊢[PRAAx] le A B :=
  sg_zero_inv (one_fac ((congrSg hK).eqTrans (sg_succ _)) h)

theorem fac_step {K y : PTm n} (ih : Γ ⊢[PRAAx] ap2 (sumF wB) K y ≐ zero) :
    Γ ⊢[PRAAx] sg K * sg (monus (phi K * Hq one (fstT y) (sndT y)) (K * Hq K (fstT y) (sndT y))) ≐ zero := by
  refine .orE (zero_or_succ K) ?_ ?_
  · exact zero_mul_l ((congrSg Prf.hyp0).eqTrans sg_zero) _
  · let C : List (Fm PTm n) := (K ≐ succ (pred K)) :: Γ
    have hKp : C ⊢[PRAAx] K ≐ succ (pred K) := Prf.hyp0
    refine .orE (zero_or_succ (pred K)) ?_ ?_
    · -- `K = 1`
      have e1 : ((pred K ≐ zero) :: C) ⊢[PRAAx] K ≐ one := hKp.wk.eqTrans (congrSucc Prf.hyp0)
      refine viol_of (le_congr ?_ ?_ (le_refl (one * Hq one (fstT y) (sndT y))))
      · exact congrMul (phi_one.eqSymm.eqTrans (congrAp2 (sumF totBody) e1.eqSymm e1.eqSymm)) (.eqRefl _)
      · exact congrMul e1.eqSymm (congrAp2 (sumF hqB) (.eqRefl _) (congrPairT e1.eqSymm (.eqRefl _)))
    · -- `K ≥ 2`
      let E : List (Fm PTm n) := (pred K ≐ succ (pred (pred K))) :: C
      have hK : E ⊢[PRAAx] le two K := le_of_eq_add (two_alg hKp.wk Prf.hyp0)
      have hp := Prf.andE₁ (lpf_two hK)
      have mpos := cof_pos hK
      have z := sum_zero_elim wB ih.wk.wk (cof_lt hK)
      rw [inst2_w] at z
      have ihm := of_viol mpos z
      have eK := K_split hK
      have core : E ⊢[PRAAx] le (phi (lpf K * quo K (lpf K)) * Hq one (fstT y) (sndT y))
          ((lpf K * quo K (lpf K)) * Hq (lpf K * quo K (lpf K)) (fstT y) (sndT y)) := by
        refine .orE (eq_or_ne (rem (quo K (lpf K)) (lpf K)) zero) ?_ ?_
        · exact step_dvd hp.wk mpos.wk Prf.hyp0 ihm.wk
        · exact step_coprime hp.wk mpos.wk Prf.hyp0 ihm.wk
      exact viol_of (le_congr (congrMul (congrAp2 (sumF totBody) eK.eqSymm eK.eqSymm) (.eqRefl _))
        (congrMul eK.eqSymm (congrAp2 (sumF hqB) (.eqRefl _) (congrPairT eK.eqSymm (.eqRefl _)))) core)

theorem Hq_proj (a F N : PTm n) :
    Γ ⊢[PRAAx] Hq a (fstT (pairT F N)) (sndT (pairT F N)) ≐ Hq a F N :=
  congrAp2 (sumF hqB) (snd_pair _ _) (congrPairT (.eqRefl _) (fst_pair _ _))

/-- **`φ(q) · H^{(1)}(N) ≤ q · H^{(q)}(N)`** for `q ≥ 1`: `H_z ≤ (q/φ(q)) H_q(z)`. -/
theorem harm_factor {q : PTm n} (hq : Γ ⊢[PRAAx] q ≐ succ (pred q)) (F N : PTm n) :
    Γ ⊢[PRAAx] le (phi q * Hq one F N) (q * Hq q F N) := by
  have h := strong_ind (Γ := Γ) wB (fun N x hS => by rw [inst2_w]; exact fac_step hS) q (pairT F N)
  rw [inst2_w] at h
  exact le_congr (congrMul (.eqRefl _) (Hq_proj one F N)) (congrMul (.eqRefl _) (Hq_proj q F N))
    (of_viol hq h)

/-! ## The harmonic sum -/

/-- `[m ≥ 1] ⌊F/m⌋`, over `0 = m`, `1 = F`. -/
abbrev hzB : PTm 2 := sg (var 0) * quo (var 1) (var 0)

theorem inst2_hz (m F : PTm n) : inst2 hzB m F = sg m * quo F m := by
  simp only [inst2, PTm.subst_mul, PTm.subst_monus, subst_ap2, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]

/-- `∑_{1 ≤ m < N} ⌊F/m⌋`; at `F = z!`, `N = z + 1` it is `z! H_z`. -/
abbrev Hz (F N : PTm n) : PTm n := ap2 (sumF hzB) N F

theorem one_term (m F : PTm n) : Γ ⊢[PRAAx] hT one F m ≐ sg m * quo F m := by
  refine .orE (zero_or_succ m) ?_ ?_
  · have s0 : ((m ≐ zero) :: Γ) ⊢[PRAAx] sg m ≐ zero := (congrSg Prf.hyp0).eqTrans sg_zero
    exact (zero_mul_l s0 _).eqTrans (zero_mul_l s0 _).eqSymm
  · have hm : ((m ≐ succ (pred m)) :: Γ) ⊢[PRAAx] m ≐ succ (pred m) := Prf.hyp0
    have g : ((m ≐ succ (pred m)) :: Γ) ⊢[PRAAx] gcd m one ≐ one :=
      eq_one_of_dvd_one (gcd_pos hm) (Prf.andE₂ (gcd_dvd' (b := one) hm))
    exact congrMul (.eqRefl _) ((congrMul (eqb_of_eq g) (.eqRefl _)).eqTrans (one_mul _))

/-- `H^{(1)}(N) = ∑_{1 ≤ m < N} ⌊F/m⌋`. -/
theorem Hq_one (F N : PTm n) : Γ ⊢[PRAAx] Hq one F N ≐ Hz F N := by
  refine sum_congr_bounded hqB hzB (pairT one F) F N (.allI (.impI ?_))
  have s1 : Syn.shift (pairT (one : PTm n) F) = pairT one (Syn.shift F) := by simp [Syn.shift]
  rw [s1, inst2_hz]
  exact (hq_at _ _ _).eqTrans (one_term _ _)

/-! ## The denominator bound and the second inequality -/

/-- **`eq:sieve-denominator`**: `φ(q) · ∑_{1 ≤ m ≤ z} ⌊z!/m⌋ ≤ q · z! G_q(z)` for `q ≥ 1`, that is
`G_q(z) ≥ (φ(q)/q) H_z`. -/
theorem sieve_denominator {q : PTm n} (hq : Γ ⊢[PRAAx] q ≐ succ (pred q)) (a z : PTm n) :
    Γ ⊢[PRAAx] le (phi q * Hz (fact z) (succ z)) (q * Asum (P3 q a z)) :=
  le_trans (le_congr (congrMul (.eqRefl _) (Hq_one _ _)) (.eqRefl _) (harm_factor hq (fact z) (succ z)))
    (le_mul_mono (le_refl q) (Hq_le_Asum hq a z))

theorem transfer_gt {c c' t B R d : PTm n} (h1 : Γ ⊢[PRAAx] le c' c)
    (h2 : Γ ⊢[PRAAx] le (c * t) (R + c * B)) (e : Γ ⊢[PRAAx] t ≐ B + d) :
    Γ ⊢[PRAAx] le (c' * t) (R + c' * B) := by
  have x := natEq e
  ipra_le sl h2 + 𝔞 d * sl h1 with (𝔞 c - 𝔞 c') * x

theorem transfer_le {c' t B : PTm n} (R : PTm n) (h3 : Γ ⊢[PRAAx] le t B) :
    Γ ⊢[PRAAx] le (c' * t) (R + c' * B) := by
  ipra_le 𝔞 c' * sl h3 + 𝔞 R

/-- A smaller denominator: `c′ ≤ c` and `c t ≤ R + c B` give `c′ t ≤ R + c′ B`. -/
theorem transfer {c c' t B R : PTm n} (h1 : Γ ⊢[PRAAx] le c' c)
    (h2 : Γ ⊢[PRAAx] le (c * t) (R + c * B)) : Γ ⊢[PRAAx] le (c' * t) (R + c' * B) := by
  refine .orE (lt_or_le B t) ?_ ?_
  · have hlt : (lt B t :: Γ) ⊢[PRAAx] le (succ B) t := Prf.hyp0
    exact transfer_gt h1.wk h2.wk (eq_add_of_le (le_trans (le_succ_self B) hlt))
  · exact transfer_le R Prf.hyp0

theorem assoc_alg (a b c : PTm n) : Γ ⊢[PRAAx] a * (b * c) ≐ (a * b) * c := by
  ipra_ring

/-- **`thm:finite-sieve`, second inequality**, for `q ≥ 1`: with `H = ∑_{1 ≤ m ≤ z} ⌊z!/m⌋ = z! H_z`,
`φ(q) H · π(X; q, a) ≤ X z! + φ(q) H (z² + z)`. -/
theorem finite_sieve_second {X q a z : PTm n} (hq : Γ ⊢[PRAAx] le one q)
    (ha : Γ ⊢[PRAAx] gcd a q ≐ one) (hz : Γ ⊢[PRAAx] le one z) :
    Γ ⊢[PRAAx] le
      ((phi q * Hz (fact z) (succ z)) *
        ap2 (sumF piB) X (pairT (succ z) (pairT (succ z) (P3 q a z))))
      (X * fact z + (phi q * Hz (fact z) (succ z)) * (z * z + z)) := by
  have eq : Γ ⊢[PRAAx] fstT (P3 q a z) ≐ q := fst_pair _ _
  have ez : Γ ⊢[PRAAx] sndT (sndT (P3 q a z)) ≐ z := P3_z q a z
  have fs := finite_sieve (X := X) (P := P3 q a z) (le_congr (.eqRefl _) eq.eqSymm hq)
    ((congrGcd (P3_L q a z) eq).eqTrans ha) (le_congr (.eqRefl _) ez.eqSymm hz)
  have eπ : Γ ⊢[PRAAx] ap2 (sumF piB) X (pairT (succ (sndT (sndT (P3 q a z))))
        (pairT (succ (sndT (sndT (P3 q a z)))) (P3 q a z))) ≐
      ap2 (sumF piB) X (pairT (succ z) (pairT (succ z) (P3 q a z))) :=
    congrAp2 (sumF piB) (.eqRefl _) (congrPairT (congrSucc ez) (congrPairT (congrSucc ez) (.eqRefl _)))
  have fs' : Γ ⊢[PRAAx] le
      ((q * Asum (P3 q a z)) * ap2 (sumF piB) X (pairT (succ z) (pairT (succ z) (P3 q a z))))
      (X * fact z + (q * Asum (P3 q a z)) * (z * z + z)) :=
    le_congr ((congrMul eq (congrMul (.eqRefl _) eπ)).eqTrans (assoc_alg _ _ _))
      (congrAdd (congrMul (.eqRefl _) (congrAp2 factF ez (.eqRefl _)))
        ((congrMul eq (congrMul (.eqRefl _) (congrAdd (congrMul ez ez) ez))).eqTrans (assoc_alg _ _ _))) fs
  have qpos : Γ ⊢[PRAAx] q ≐ succ (pred q) :=
    AnalyticNumberTheory.CoprimeModulus.pos_of_one_le hq
  exact transfer (sieve_denominator qpos a z) fs'

end LeanProofs.IPRA.AnalyticNumberTheory.DenominatorBound
