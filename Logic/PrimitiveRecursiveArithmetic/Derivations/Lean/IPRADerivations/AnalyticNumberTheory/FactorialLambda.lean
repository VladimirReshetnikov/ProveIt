import IPRADerivations.AnalyticNumberTheory.WeightedMangoldt
import IPRADerivations.AnalyticNumberTheory.SummatoryPhi

/-!
# The factorial identity for the weighted von Mangoldt function

Packet: `analytic-number-theory/von_mangoldt_totient_ipra_2026-11-15`, Theorem `thm:factorial-lambda`:
`L_w(N!) = ∑_{d ≤ N} Λ_w(d) ⌊N/d⌋` for every weight `w` (for `w = log`, `log N! = ∑ Λ(d) ⌊N/d⌋`).

* `lw_mul`: complete additivity `L_w(a b) = L_w(a) + L_w(b)` for `a, b ≥ 1`, from
  `v_q(a b) = v_q(a) + v_q(b)` after extending the three prime ranges to `a b` (`MobiusBounds.sum_ext`);
* `lam_zero`: `Λ_w(0) = 0`;
* `factorial_lambda`: by induction on `N`. Since `⌊(N+1)/d⌋ = ⌊N/d⌋ + [d ∣ N+1]`
  (`SummatoryPhi.quo_succ`), the right side grows by `∑_{d ∣ N+1} Λ_w(d) = L_w(N+1)`
  (`WeightedMangoldt.lambda_divsum`), and `L_w((N+1)!) = L_w(N!) + L_w(N+1)` by additivity.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.FactorialLambda

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusBounds (sum_ext shift_pos val_big)
open LeanProofs.IPRA.AnalyticNumberTheory.WeightedMangoldt
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (val isP isP_01 prime_of_isP)
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (fact_pos)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Sums with different parameters -/

/-- `f(q, fst z)`. -/
def fB (f : PTm 2) : PTm 2 := Syn.subst ![var 0, fstT (var 1)] f
/-- `g(q, snd z)`. -/
def sB (g : PTm 2) : PTm 2 := Syn.subst ![var 0, sndT (var 1)] g

theorem inst2_fB (f : PTm 2) (q z : PTm n) : inst2 (fB f) q z = inst2 f q (fstT z) := by
  simp only [inst2, fB, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
theorem inst2_sB (g : PTm 2) (q z : PTm n) : inst2 (sB g) q z = inst2 g q (sndT z) := by
  simp only [inst2, sB, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp

/-- `∑ h(q, z) = ∑ f(q, x) + ∑ g(q, x')` when `h(q, z) = f(q, x) + g(q, x')` below the bound. -/
theorem sum_add2 (f g h : PTm 2) {K x x' z : PTm n}
    (hp : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift K) ⟶ (inst2 h (var 0) (Syn.shift z) ≐
      inst2 f (var 0) (Syn.shift x) + inst2 g (var 0) (Syn.shift x')))) :
    Γ ⊢[PRAAx] ap2 (sumF h) K z ≐ ap2 (sumF f) K x + ap2 (sumF g) K x' := by
  have c : Γ ⊢[PRAAx] ap2 (sumF h) K z ≐ ap2 (sumF (addBody (fB f) (sB g))) K (pairT x x') := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_addBody, inst2_fB, inst2_sB, shift_pairT]
    exact (Prf.impE hp.allOpen.wk Prf.hyp0).eqTrans
      (congrAdd (congrInst2 f (.eqRefl _) (fst_pair _ _).eqSymm) (congrInst2 g (.eqRefl _) (snd_pair _ _).eqSymm))
  have a := sum_add (Γ := Γ) (fB f) (sB g) K (pairT x x')
  have e₁ : Γ ⊢[PRAAx] ap2 (sumF (fB f)) K (pairT x x') ≐ ap2 (sumF f) K x := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_fB, shift_pairT]; exact congrInst2 f (.eqRefl _) (fst_pair _ _)
  have e₂ : Γ ⊢[PRAAx] ap2 (sumF (sB g)) K (pairT x x') ≐ ap2 (sumF g) K x' := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_sB, shift_pairT]; exact congrInst2 g (.eqRefl _) (snd_pair _ _)
  exact c.eqTrans (a.eqTrans (congrAdd e₁ e₂))

section Additive

variable (w : PTm 2)

theorem ell_at (q m y : PTm n) :
    Γ ⊢[PRAAx] inst2 (ellB w) q (pairT m y) ≐ (isP q * val q m) * inst2 w q y := by
  rw [inst2_ell]
  exact congrMul (congrMul (.eqRefl _) (congrVal (.eqRefl _) (fst_pair _ _))) (congrInst2 w (.eqRefl _) (snd_pair _ _))

/-- `L_w(m)` may be summed over any prime range `N > m`, for `m ≥ 1`. -/
theorem lw_ext {m y N : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (hN : Γ ⊢[PRAAx] le (succ m) N) :
    Γ ⊢[PRAAx] ap2 (sumF (ellB w)) N (pairT m y) ≐ Lw w m y := by
  have hm' := shift_pos hm
  refine sum_ext (ellB w) (fun Δ a hs hl => ?_) hN
  rw [shift_pairT]
  refine (ell_at w _ _ _).eqTrans ?_
  exact zero_mul_l ((congrMul (.eqRefl _) (val_big (hm'.weaken hs) hl)).eqTrans (mul_zero _)) _

/-- `[q prime] v_q(a b) w(q) = [q prime] v_q(a) w(q) + [q prime] v_q(b) w(q)` for `a, b ≥ 1`. -/
theorem ell_mul_pt {q a b y : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (hb : Γ ⊢[PRAAx] b ≐ succ (pred b)) :
    Γ ⊢[PRAAx] (isP q * val q (a * b)) * inst2 w q y ≐ (isP q * val q a) * inst2 w q y + (isP q * val q b) * inst2 w q y := by
  refine .orE (isP_01 q) ?_ ?_
  · have h0 : ((isP q ≐ zero) :: Γ) ⊢[PRAAx] isP q ≐ zero := Prf.hyp0
    exact (zero_mul_l (zero_mul_l h0 _) _).eqTrans ((congrAdd (zero_mul_l (zero_mul_l h0 _) _)
      (zero_mul_l (zero_mul_l h0 _) _)).eqTrans (add_zero _)).eqSymm
  · have h1 : ((isP q ≐ one) :: Γ) ⊢[PRAAx] isP q ≐ one := Prf.hyp0
    exact (congrMul (congrMul (.eqRefl _) (val_mul (prime_of_isP h1) ha.wk hb.wk)) (.eqRefl _)).eqTrans
      (by ipra_ring)

/-- Complete additivity: `L_w(a b) = L_w(a) + L_w(b)` for `a, b ≥ 1`. -/
theorem lw_mul {a b y : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (hb : Γ ⊢[PRAAx] b ≐ succ (pred b)) :
    Γ ⊢[PRAAx] Lw w (a * b) y ≐ Lw w a y + Lw w b y := by
  have wa := natEq ha; have wb := natEq hb
  have la : Γ ⊢[PRAAx] le (succ a) (succ (a * b)) :=
    (succ_monus_succ _ _).eqTrans (le_of_eq_add (d := a * pred b) (by ipra_lc 𝔞 a * wb))
  have lb : Γ ⊢[PRAAx] le (succ b) (succ (a * b)) :=
    (succ_monus_succ _ _).eqTrans (le_of_eq_add (d := pred a * b) (by ipra_lc 𝔞 b * wa))
  have ha' := shift_pos ha; have hb' := shift_pos hb
  refine (sum_add2 (ellB w) (ellB w) (ellB w) (x := pairT a y) (x' := pairT b y) (.allI (.impI ?_))).eqTrans
    (congrAdd (lw_ext w ha la) (lw_ext w hb lb))
  simp only [shift_pairT]
  have hm : Syn.shift (a * b) = Syn.shift a * Syn.shift b := by simp [Syn.shift]
  rw [hm]
  exact (ell_at w _ _ _).eqTrans ((ell_mul_pt w ha'.wk hb'.wk).eqTrans
    (congrAdd (ell_at w _ _ _).eqSymm (ell_at w _ _ _).eqSymm))

end Additive

/-! ## The factorial identity -/

section Factorial

variable (w : PTm 2)

/-- `Λ_w(d) ⌊N/d⌋`, over `0 = d`, `1 = ⟨N, y⟩`. -/
abbrev FLB : PTm 2 := ap2 (sumF (lamB w)) (succ (var 0)) (pairT (var 0) (sndT (var 1))) * quo (fstT (var 1)) (var 0)

theorem FL_at (d N y : PTm n) : Γ ⊢[PRAAx] inst2 (FLB w) d (pairT N y) ≐ Lam w d y * quo N d := by
  have e : inst2 (FLB w) d (pairT N y) = Lam w d (sndT (pairT N y)) * quo (fstT (pairT N y)) d := by simp [inst2]
  rw [e]
  exact congrMul (congrAp2 (sumF (lamB w)) (.eqRefl _) (congrPairT (.eqRefl _) (snd_pair _ _)))
    (congrAp2 quoF (fst_pair _ _) (.eqRefl _))

theorem DB_at (d m y : PTm n) :
    Γ ⊢[PRAAx] inst2 (DB w) d (pairT m y) ≐ (sg d * eqb (rem m d) zero) * Lam w d y := by
  rw [inst2_DB]
  exact congrMul (congrMul (.eqRefl _) (congrEqb' (congrAp2 remF (fst_pair _ _) (.eqRefl _)) (.eqRefl _)))
    (congrAp2 (sumF (lamB w)) (.eqRefl _) (congrPairT (.eqRefl _) (snd_pair _ _)))

/-- `Λ_w(0) = 0`. -/
theorem lam_zero (y : PTm n) : Γ ⊢[PRAAx] Lam w zero y ≐ zero := by
  refine (sum_succ' _ _ _).eqTrans ((congrAdd (sum_zero _ _) ?_).eqTrans (add_zero _))
  rw [inst2_lam]
  exact zero_mul_l (zero_mul_l isP_zero _) _

theorem congrLw {m m' : PTm n} (y : PTm n) (h : Γ ⊢[PRAAx] m ≐ m') : Γ ⊢[PRAAx] Lw w m y ≐ Lw w m' y :=
  congrAp2 (sumF (ellB w)) (congrSucc h) (congrPairT h (.eqRefl y))

/-- The pointwise step `Λ_w(d) ⌊(N+1)/d⌋ = Λ_w(d) ⌊N/d⌋ + [d ∣ N+1] Λ_w(d)`. -/
theorem fl_pt (d N y : PTm n) :
    Γ ⊢[PRAAx] inst2 (FLB w) d (pairT (succ N) y) ≐ inst2 (FLB w) d (pairT N y) + inst2 (DB w) d (pairT (succ N) y) := by
  refine (FL_at w _ _ _).eqTrans (.eqTrans ?_ (congrAdd (FL_at w _ _ _) (DB_at w _ _ _)).eqSymm)
  refine .orE (zero_or_succ d) ?_ ?_
  · have h0 : ((d ≐ zero) :: Γ) ⊢[PRAAx] d ≐ zero := Prf.hyp0
    have l0 : ((d ≐ zero) :: Γ) ⊢[PRAAx] Lam w d y ≐ zero :=
      (congrAp2 (sumF (lamB w)) (congrSucc h0) (congrPairT h0 (.eqRefl _))).eqTrans (lam_zero w y)
    exact (zero_mul_l l0 _).eqTrans ((congrAdd (zero_mul_l l0 _)
      (zero_mul_l (zero_mul_l ((congrSg h0).eqTrans sg_zero) _) _)).eqTrans (add_zero _)).eqSymm
  · have hd : ((d ≐ succ (pred d)) :: Γ) ⊢[PRAAx] d ≐ succ (pred d) := Prf.hyp0
    ipra_lc 𝔞 (Lam w d y) * natEq (SummatoryPhi.quo_succ (N := N) hd) -
      𝔞 (eqb (rem (succ N) d) zero) * 𝔞 (Lam w d y) * natEq ((congrSg hd).eqTrans (sg_succ _))

/-- `∑_{d ≤ N+1} Λ_w(d) ⌊(N+1)/d⌋ = ∑_{d ≤ N} Λ_w(d) ⌊N/d⌋ + L_w(N + 1)`. -/
theorem fl_step (N y : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (FLB w)) (succ (succ N)) (pairT (succ N) y) ≐
      ap2 (sumF (FLB w)) (succ N) (pairT N y) + Lw w (succ N) y := by
  have a := sum_add2 (Γ := Γ) (FLB w) (DB w) (FLB w) (K := succ (succ N)) (x := pairT N y)
    (x' := pairT (succ N) y) (z := pairT (succ N) y) (.allI (.impI (by
      simp only [shift_pairT]
      have hs : Syn.shift (succ N) = succ (Syn.shift N) := by simp [Syn.shift]
      rw [hs]
      exact fl_pt w _ _ _)))
  have b := sum_succ' (Γ := Γ) (FLB w) (succ N) (pairT N y)
  have c : Γ ⊢[PRAAx] inst2 (FLB w) (succ N) (pairT N y) ≐ zero :=
    (FL_at w _ _ _).eqTrans ((congrMul (.eqRefl _) (SummatoryPhi.quo_lt_self N)).eqTrans (mul_zero _))
  have d := lambda_divsum (Γ := Γ) w (m := succ N) (y := y) (congrSucc (pred_succ _).eqSymm)
  ipra_lc natEq a + natEq b + natEq c + natEq d

/-- Variables: `0 = N`, `1 = y`. -/
private abbrev flF : Fm PTm 2 :=
  Lw w (fact (var 0)) (var 1) ≐ ap2 (sumF (FLB w)) (succ (var 0)) (pairT (var 0) (var 1))

theorem fl_base (y : PTm n) :
    Γ ⊢[PRAAx] Lw w (fact zero) y ≐ ap2 (sumF (FLB w)) (succ zero) (pairT zero y) := by
  have l1 : Γ ⊢[PRAAx] Lw w (fact zero) y ≐ zero := by
    refine (congrLw w y (fact_zero zero)).eqTrans ?_
    refine (sum_succ' _ _ _).eqTrans ((congrAdd ((sum_succ' _ _ _).eqTrans ((congrAdd (sum_zero _ _) ?_).eqTrans
      (zero_add _))) ?_).eqTrans (add_zero _))
    · rw [inst2_ell]; exact zero_mul_l (zero_mul_l isP_zero _) _
    · rw [inst2_ell]; exact zero_mul_l (zero_mul_l isP_one _) _
  have r0 : Γ ⊢[PRAAx] ap2 (sumF (FLB w)) (succ zero) (pairT zero y) ≐ zero :=
    (sum_succ' _ _ _).eqTrans ((congrAdd (sum_zero _ _) ((FL_at w _ _ _).eqTrans
      (zero_mul_l (lam_zero w y) _))).eqTrans (add_zero _))
  exact l1.eqTrans r0.eqSymm

private theorem fl₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] flF w := by
  ipra_ind [subst_ap2, subst_pairT]
  · exact fl_base w _
  · refine (congrLw w _ (fact_succ _ _)).eqTrans ?_
    refine (lw_mul w (fact_pos _) (congrSucc (pred_succ _).eqSymm)).eqTrans ?_
    exact (congrAdd Prf.hyp0 (.eqRefl _)).eqTrans (fl_step w _ _).eqSymm

/-- `thm:factorial-lambda`: `L_w(N!) = ∑_{d ≤ N} Λ_w(d) ⌊N/d⌋` for every weight `w`. -/
theorem factorial_lambda (N y : PTm n) :
    Γ ⊢[PRAAx] Lw w (fact N) y ≐ ap2 (sumF (FLB w)) (succ N) (pairT N y) := by
  have i := inst (Γ := Γ) (fl₀ w) (![N, y] : Fin 2 → PTm n)
  simpa using i

end Factorial

end LeanProofs.IPRA.AnalyticNumberTheory.FactorialLambda

export_ipra AnalyticNumberTheory.FactorialLambda (FLB FL_at congrLw factorial_lambda inst2_fB lam_zero lw_mul
  sum_add2)
