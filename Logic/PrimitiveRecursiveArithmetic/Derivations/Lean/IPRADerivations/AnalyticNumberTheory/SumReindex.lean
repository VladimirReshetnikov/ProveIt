import IPRADerivations.AnalyticNumberTheory.PowerCleared

/-!
# Summing over multiples

Reusable tools for the Euler-product comparison of `prime_reciprocal_ipra_2026-11-15`
(Lemma `lem:euler-domination`):

* `sum_le_bound`: `a ≤ b → ∑_{i<a} f(i) ≤ ∑_{i<b} f(i)`;
* `le_quo_of_mul_le`: `k t ≤ F → t ≤ ⌊F/k⌋` for `k ≥ 1`;
* `reindex_eq`: `∑_{m<N} [p ∣ m] h(m/p) = ∑_{k<c(N)} h(k)`, where `c(N) = #{m < N : p ∣ m}`;
* `reindex_le`: `∑_{m<N} [p ∣ m] h(m/p) ≤ ∑_{k<N} h(k)` — the multiples `kp` of `p` below `N` are
  sent injectively to `k`.

The reindexed body `riB h` reads its parameter as the pair `⟨p, x⟩`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.SumReindex

open_ipra exports
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime
open LeanProofs.IPRA.DiophantineNumberTheory.FermatQuartic (zo_eqb eq_of_eqb congrPair)
open LeanProofs.IPRA.AnalyticNumberTheory.Euler (congrEqb)
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (quo_eq mulBody inst2_mul count_multiples)
open LeanProofs.IPRA.AnalyticNumberTheory.SumPhi (sum_ones)
open LeanProofs.IPRA.Analysis.PowerSums (sum_le)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Monotonicity in the bound -/

/-- Variables: `0 = d`, `1 = a`, `2 = x`. -/
private abbrev boundF (f : PTm 2) : Fm PTm 3 :=
  le (ap2 (sumF f) (var 1) (var 2)) (ap2 (sumF f) (var 1 + var 0) (var 2))

private theorem bound₀ (f : PTm 2) : ([] : List (Fm PTm 3)) ⊢[PRAAx] boundF f := by
  ipra_ind (le_QF _ _) [subst_le, subst_ap2]
  · exact le_congr (.eqRefl _) (congrAp2 (sumF f) (add_zero _) (.eqRefl _)).eqSymm (le_refl _)
  · exact le_trans Prf.hyp0 (le_of_eq_add (d := inst2 f (var 1 + var 0) (var 2))
      ((congrAp2 (sumF f) (add_succ _ _) (.eqRefl _)).eqTrans (sum_succ' f _ _)))

/-- `a ≤ b → ∑_{i<a} f(i, x) ≤ ∑_{i<b} f(i, x)`. -/
theorem sum_le_bound (f : PTm 2) {a b x : PTm n} (h : Γ ⊢[PRAAx] le a b) :
    Γ ⊢[PRAAx] le (ap2 (sumF f) a x) (ap2 (sumF f) b x) := by
  have i := inst (Γ := Γ) (bound₀ f) (![monus b a, a, x] : Fin 3 → PTm n)
  simp at i
  exact le_congr (.eqRefl _) (congrAp2 (sumF f) (eq_add_of_le h).eqSymm (.eqRefl _)) i

/-! ## A floor bound -/

/-- `k t ≤ F → t ≤ ⌊F/k⌋` for `k ≥ 1`. -/
theorem le_quo_of_mul_le {k t F : PTm n} (hk : Γ ⊢[PRAAx] k ≐ succ (pred k)) (h : Γ ⊢[PRAAx] le (k * t) F) :
    Γ ⊢[PRAAx] le t (quo F k) :=
  Division.le_quo_of_mul_le hk h

/-! ## Reindexing the multiples of `p` -/

/-- `[fst y ∣ m] · h(m / fst y, snd y)`. -/
def riB (h : PTm 2) : PTm 2 :=
  eqb (rem (var 0) (fstT (var 1))) zero * Syn.subst ![quo (var 0) (fstT (var 1)), sndT (var 1)] h

theorem inst2_riB (h : PTm 2) (m y : PTm n) :
    inst2 (riB h) m y = eqb (rem m (fstT y)) zero * inst2 h (quo m (fstT y)) (sndT y) := by
  simp only [inst2, riB, PTm.subst_mul, Syn.subst_subst]
  congr 1
  · simp
  · congr 1; funext j; fin_cases j <;> simp

/-- The number of multiples of `p` below `N`. -/
abbrev cM (N p : PTm n) : PTm n := ap2 (sumF mulBody) N p

theorem cM_le (N p : PTm n) : Γ ⊢[PRAAx] le (cM N p) N := by
  refine le_congr (.eqRefl _) (sum_ones N p) (sum_le mulBody one p N (.allI (.impI ?_)))
  have e : inst2 (one : PTm 2) (var 0 : PTm (n + 1)) (Syn.shift p) = one := by simp [inst2]
  rw [inst2_mul, e]
  exact eqb_le_one _ _

theorem reindex_step (h : PTm 2) {p N x : PTm n} (hp : Γ ⊢[PRAAx] p ≐ succ (pred p))
    (ih : Γ ⊢[PRAAx] ap2 (sumF (riB h)) N (pairT p x) ≐ ap2 (sumF h) (cM N p) x) :
    Γ ⊢[PRAAx] ap2 (sumF (riB h)) (succ N) (pairT p x) ≐ ap2 (sumF h) (cM (succ N) p) x := by
  have eL := sum_succ' (Γ := Γ) (riB h) N (pairT p x)
  rw [inst2_riB] at eL
  have tE : Γ ⊢[PRAAx] eqb (rem N (fstT (pairT p x))) zero *
      inst2 h (quo N (fstT (pairT p x))) (sndT (pairT p x)) ≐ eqb (rem N p) zero * inst2 h (quo N p) x :=
    congrMul (congrEqb (congrAp2 remF (.eqRefl _) (fst_pair _ _)) (.eqRefl _))
      (congrInst2 h (congrAp2 quoF (.eqRefl _) (fst_pair _ _)) (snd_pair _ _))
  have eC := sum_succ' (Γ := Γ) mulBody N p
  rw [inst2_mul] at eC
  refine .orE (zo_eqb (rem N p) zero) ?_ ?_
  · have h0 : ((eqb (rem N p) zero ≐ zero) :: Γ) ⊢[PRAAx] eqb (rem N p) zero ≐ zero := Prf.hyp0
    refine (eL.wk.eqTrans (congrAdd ih.wk (tE.wk.eqTrans ((congrMul h0 (.eqRefl _)).eqTrans (zero_mul _))))).eqTrans
      ((add_zero _).eqTrans ?_)
    exact (congrAp2 (sumF h) (eC.wk.eqTrans ((congrAdd (.eqRefl _) h0).eqTrans (add_zero _))) (.eqRefl _)).eqSymm
  · have h1 : ((eqb (rem N p) zero ≐ one) :: Γ) ⊢[PRAAx] eqb (rem N p) zero ≐ one := Prf.hyp0
    have hd := eq_of_eqb h1
    have hz : ((eqb (rem N p) zero ≐ one) :: Γ) ⊢[PRAAx] N + pred p ≐ p * quo N p + pred p :=
      congrAdd (eq_of_dvd' hp.wk hd) (.eqRefl _)
    have hlt : ((eqb (rem N p) zero ≐ one) :: Γ) ⊢[PRAAx] lt (pred p) p :=
      le_congr (.eqRefl _) hp.wk.eqSymm (le_refl _)
    have hq : ((eqb (rem N p) zero ≐ one) :: Γ) ⊢[PRAAx] quo N p ≐ cM N p :=
      (quo_eq hp.wk hz hlt).eqSymm.eqTrans (count_multiples hp.wk).eqSymm
    refine (eL.wk.eqTrans (congrAdd ih.wk (tE.wk.eqTrans ((congrMul h1 (congrInst2 h hq (.eqRefl _))).eqTrans
      (one_mul _))))).eqTrans ?_
    refine (sum_succ' h (cM N p) x).eqSymm.eqTrans (congrAp2 (sumF h) ?_ (.eqRefl _))
    exact ((succ_eq_add_one _).eqTrans (congrAdd (.eqRefl _) h1.eqSymm)).eqTrans eC.wk.eqSymm

/-- Variables: `0 = N`, `1 = p − 1`, `2 = x`. -/
private abbrev riF (h : PTm 2) : Fm PTm 3 :=
  ap2 (sumF (riB h)) (var 0) (pairT (succ (var 1)) (var 2)) ≐ ap2 (sumF h) (cM (var 0) (succ (var 1))) (var 2)

private theorem reindex₀ (h : PTm 2) : ([] : List (Fm PTm 3)) ⊢[PRAAx] riF h := by
  ipra_ind [subst_ap2, subst_pairT]
  · exact (sum_zero _ _).eqTrans ((congrAp2 (sumF h) (sum_zero _ _) (.eqRefl _)).eqTrans (sum_zero _ _)).eqSymm
  · exact reindex_step h (congrSucc (pred_succ _).eqSymm) Prf.hyp0

/-- `∑_{m<N} [p ∣ m] h(m/p, x) = ∑_{k<c(N)} h(k, x)`. -/
theorem reindex_eq (h : PTm 2) {p x : PTm n} (N : PTm n) (hp : Γ ⊢[PRAAx] p ≐ succ (pred p)) :
    Γ ⊢[PRAAx] ap2 (sumF (riB h)) N (pairT p x) ≐ ap2 (sumF h) (cM N p) x := by
  have i := inst (Γ := Γ) (reindex₀ h) (![N, pred p, x] : Fin 3 → PTm n)
  simp at i
  exact (congrAp2 (sumF (riB h)) (.eqRefl _) (congrPair hp (.eqRefl _))).eqTrans
    (i.eqTrans (congrAp2 (sumF h) (congrAp2 (sumF mulBody) (.eqRefl _) hp.eqSymm) (.eqRefl _)))

/-- `∑_{m<N} [p ∣ m] h(m/p, x) ≤ ∑_{k<N} h(k, x)`. -/
theorem reindex_le (h : PTm 2) {p x : PTm n} (N : PTm n) (hp : Γ ⊢[PRAAx] p ≐ succ (pred p)) :
    Γ ⊢[PRAAx] le (ap2 (sumF (riB h)) N (pairT p x)) (ap2 (sumF h) N x) :=
  le_congr (reindex_eq h N hp).eqSymm (.eqRefl _) (sum_le_bound h (cM_le N p))

end LeanProofs.IPRA.AnalyticNumberTheory.SumReindex

export_ipra AnalyticNumberTheory.SumReindex (inst2_riB le_quo_of_mul_le reindex_eq reindex_le sum_le_bound)
