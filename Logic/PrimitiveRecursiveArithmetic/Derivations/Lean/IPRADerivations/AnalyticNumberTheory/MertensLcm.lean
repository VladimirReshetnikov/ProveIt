import IPRADerivations.AnalyticNumberTheory.ValuationExt
import IPRADerivations.AnalyticNumberTheory.MertensChebyshev
import IPRADerivations.Foundations.MixedRadix

/-!
# The product form of the Chebyshev identity for the Mertens function

Packet: `analytic-number-theory/mertens-ipra`, `identities.tex`, `thm:totient-chebyshev`:

  "Its multiplicative form in positive rationals is `∏_{a=1}^{N} a^{M(q_N(a))} = lcm(1, …, N)` … Move negative
  powers to the other side to obtain a natural-number equality."

With `M = M⁺ − M⁻` (`MobiusFloor.MP`, `MN`) and `P^±(N) = ∏_{a=1}^{N} a^{M^±(⌊N/a⌋)}` the natural-number equality is

    P⁺(N) = lcm(1, …, N) · P⁻(N)                                              (**`mertens_lcm_product`**).

* `pmB`, `Pp`, `Pp_pos`: the products and their positivity;
* `lw_prod`: `L_w(∏_{i < K} (i+1)^{e_i}) = ∑_{i < K} e_i L_w(i+1)` for every weight `w` (`ValuationExt.lw_pow`,
  `FactorialLambda.lw_mul`), by induction on `K` in the given context;
* `rowsum`: the sums of `MertensChebyshev.chebyshev_mertens` in this form;
* `lw_product`: `L_w(P⁺(N)) = L_w(lcm(1, …, N) · P⁻(N))` for every weight `w`, from `chebyshev_mertens` and
  `LcmUpto.psi_lcm` (`ψ_w(N) = L_w(lcm(1, …, N))`);
* `val_product`: at the weight `[q = p]` this is `v_p(P⁺(N)) = v_p(lcm(1, …, N) · P⁻(N))` for every prime `p`
  (`ValuationExt.lw_delta`), which is the packet's comparison of the coefficients of `log p`;
* the equality follows by `ValuationExt.val_ext`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.MertensLcm

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (val isP prime_of_isP pw_pos')
open LeanProofs.IPRA.AnalyticNumberTheory.ConvSummatory (Bs bS inst2_bS RB)
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusSummatory (gS inst2_gS)
open LeanProofs.IPRA.AnalyticNumberTheory.WeightedMangoldt (Lw Lam ellB lamB)
open LeanProofs.IPRA.AnalyticNumberTheory.MuLambda (lw_one)
open LeanProofs.IPRA.AnalyticNumberTheory.MertensChebyshev (LwB chebyshev_mertens mertens_term)
open LeanProofs.IPRA.AnalyticNumberTheory.ValuationExt (val_ext dW lw_delta lw_pow)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## The products -/

/-- `(i + 1)^{B_b(⌊N/(i+1)⌋)}` with `B_b(m) = ∑_{k ≤ m} b(k)`, over `0 = i`, `1 = N`. -/
def pmB (b : PTm 2) : PTm 2 := pw (succ (var 0)) (ap2 (sumF (bS b)) (quo (var 1) (succ (var 0))) zero)

theorem inst2_pm (b : PTm 2) (i N : PTm n) :
    inst2 (pmB b) i N = pw (succ i) (Bs b (quo N (succ i)) zero) := by simp [inst2, pmB]

/-- `∏_{i < K} (i + 1)^{B_b(⌊N/(i+1)⌋)}`; at `K = N`, `b = μ^±` it is `∏_{a=1}^{N} a^{M^±(⌊N/a⌋)}`. -/
abbrev Pp (b : PTm 2) (K N : PTm n) : PTm n := ap2 (prodF (pmB b)) K N

alias succ_pos := Common.succ_pos

theorem Pp_pos (b : PTm 2) (K N : PTm n) : Γ ⊢[PRAAx] Pp b K N ≐ succ (pred (Pp b K N)) := by
  refine prod_pos_bounded (pmB b) N K (.allI (.impI ?_))
  rw [inst2_pm]
  exact pw_pos' (succ_pos _) _

/-! ## The weight of the product -/

/-- `B_b(⌊N/(i+1)⌋) · L_w(i + 1)`, over `0 = i`, `1 = ⟨N, y⟩`. -/
def tB (b w : PTm 2) : PTm 2 :=
  ap2 (sumF (bS b)) (quo (fstT (var 1)) (succ (var 0))) zero *
    ap2 (sumF (ellB w)) (succ (succ (var 0))) (pairT (succ (var 0)) (sndT (var 1)))

theorem inst2_t (b w : PTm 2) (i z : PTm n) :
    inst2 (tB b w) i z = Bs b (quo (fstT z) (succ i)) zero * Lw w (succ i) (sndT z) := by
  simp [inst2, tB]

theorem t_at (b w : PTm 2) (i N y : PTm n) :
    Γ ⊢[PRAAx] inst2 (tB b w) i (pairT N y) ≐ Bs b (quo N (succ i)) zero * Lw w (succ i) y := by
  rw [inst2_t]
  exact congrMul (congrAp2 (sumF (bS b)) (congrAp2 quoF (fst_pair _ _) (.eqRefl _)) (.eqRefl _))
    (congrAp2 (sumF (ellB w)) (.eqRefl _) (congrPairT (.eqRefl _) (snd_pair _ _)))

theorem step_alg {L LP LE S S' E Lw1 : PTm n} (h1 : Γ ⊢[PRAAx] L ≐ LP + LE) (h2 : Γ ⊢[PRAAx] LE ≐ E * Lw1)
    (ih : Γ ⊢[PRAAx] LP ≐ S) (h3 : Γ ⊢[PRAAx] S' ≐ S + E * Lw1) : Γ ⊢[PRAAx] L ≐ S' := by
  ipra_lc natEq h1 + natEq h2 + natEq ih - natEq h3

/-- `L_w(∏_{i < K} (i+1)^{e_i}) = ∑_{i < K} e_i · L_w(i + 1)`. -/
theorem lw_prod (b w : PTm 2) (N y K : PTm n) :
    Γ ⊢[PRAAx] Lw w (Pp b K N) y ≐ ap2 (sumF (tB b w)) K (pairT N y) := by
  have hall : Γ ⊢[PRAAx] Fm.all (Lw w (ap2 (prodF (pmB b)) (var 0) (Syn.shift N)) (Syn.shift y) ≐
      ap2 (sumF (tB b w)) (var 0) (pairT (Syn.shift N) (Syn.shift y))) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq, subst_ap2, subst_pairT, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
        ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      exact (congrLw w _ (prod_zero (pmB b) _)).eqTrans ((lw_one w _).eqTrans (sum_zero _ _).eqSymm)
    · simp only [Fm.subst_eq, subst_ap2, subst_pairT, Syn.subst_var, Syn.repl_zero, subst_repl_shift,
        ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      have ps := Foundations.MixedRadix.prod_succ' (Γ := (Lw w (ap2 (prodF (pmB b)) (var 0) (Syn.shift N))
        (Syn.shift y) ≐ ap2 (sumF (tB b w)) (var 0) (pairT (Syn.shift N) (Syn.shift y))) :: Γ.map Fm.shift)
        (pmB b) (var 0) (Syn.shift N)
      rw [inst2_pm] at ps
      have h1 := (congrLw w (Syn.shift y) ps).eqTrans
        (lw_mul w (y := Syn.shift y) (Pp_pos b (var 0) (Syn.shift N)) (pw_pos' (succ_pos (var 0)) _))
      exact step_alg h1 (lw_pow w (succ_pos (var 0)) (Bs b (quo (Syn.shift N) (succ (var 0))) zero) (Syn.shift y))
        Prf.hyp0 ((sum_succ' (tB b w) (var 0) (pairT (Syn.shift N) (Syn.shift y))).eqTrans
          (congrAdd (.eqRefl _) (t_at b w (var 0) (Syn.shift N) (Syn.shift y))))
  have h2 := Prf.allE K hall
  simp only [Fm.subst_eq, subst_ap2, subst_pairT, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at h2
  exact h2

/-! ## The sums of the Chebyshev identity -/

theorem Bs_aP (m y : PTm n) : Γ ⊢[PRAAx] Bs aPB m y ≐ Bs aPB m zero := by
  refine sum_congr_bounded (bS aPB) (bS aPB) y zero m (.allI (.impI ?_))
  rw [inst2_bS, inst2_bS, inst2_aP, inst2_aP]
  exact .eqRefl _

theorem Bs_aN (m y : PTm n) : Γ ⊢[PRAAx] Bs aNB m y ≐ Bs aNB m zero := by
  refine sum_congr_bounded (bS aNB) (bS aNB) y zero m (.allI (.impI ?_))
  rw [inst2_bS, inst2_bS, inst2_aN, inst2_aN]
  exact .eqRefl _

theorem row_alg {s L B B' : PTm n} (hs : Γ ⊢[PRAAx] s ≐ one) (hB : Γ ⊢[PRAAx] B ≐ B') :
    Γ ⊢[PRAAx] (s * L) * B ≐ B' * L := by
  ipra_lc 𝔞 L * 𝔞 B * natEq hs + 𝔞 L * natEq hB

/-- `∑_{a ≤ N} [a ≥ 1] L_w(a) B_b(⌊N/a⌋) = ∑_{i < N} B_b(⌊N/(i+1)⌋) L_w(i + 1)` for a body `b` whose summatory
function does not depend on the parameter. -/
theorem rowsum (b w : PTm 2)
    (hb : ∀ {k : ℕ} {Δ : List (Fm PTm k)} (m y : PTm k), Δ ⊢[PRAAx] Bs b m y ≐ Bs b m zero) (N y : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (RB (LwB w) b)) (succ N) (pairT N y) ≐ ap2 (sumF (tB b w)) N (pairT N y) := by
  have z0 : Γ ⊢[PRAAx] inst2 (RB (LwB w) b) zero (pairT N y) ≐ zero :=
    (mertens_term w b zero N y).eqTrans (zero_mul_l (zero_mul_l sg_zero _) _)
  have sh : Γ ⊢[PRAAx] ap2 (sumF (shiftBody (RB (LwB w) b))) N (pairT N y) ≐
      ap2 (sumF (tB b w)) N (pairT N y) := by
    refine sum_congr_bounded (shiftBody (RB (LwB w) b)) (tB b w) (pairT N y) (pairT N y) N (.allI (.impI ?_))
    rw [inst2_shiftBody, shift_pairT]
    exact (mertens_term w b (succ (var 0)) (Syn.shift N) (Syn.shift y)).eqTrans
      ((row_alg (sg_succ _) (hb _ _)).eqTrans (t_at b w _ _ _).eqSymm)
  exact (sum_shift (RB (LwB w) b) N (pairT N y)).eqTrans ((congrAdd z0 sh).eqTrans (zero_add _))

/-- `∑_{n ≤ N} [n ≥ 1] Λ_w(n) = L_w(lcm(1, …, N))`. -/
theorem psi_sg (w : PTm 2) (N y : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (gS (LamB w))) (succ N) y ≐ Lw w (lcmu N) y := by
  refine Prf.eqTrans ?_ (psi_lcm w N y)
  refine sum_congr_bounded (gS (LamB w)) (LamB w) y y (succ N) (.allI (.impI ?_))
  rw [inst2_gS, inst2_LamB]
  refine .orE (zero_or_succ (var 0)) ?_ ?_
  · have e : ((var 0 ≐ zero) :: lt (var 0) (Syn.shift (succ N)) :: Γ.map Fm.shift) ⊢[PRAAx]
        (var 0 : PTm (n + 1)) ≐ zero := Prf.hyp0
    have hz : ((var 0 ≐ zero) :: lt (var 0) (Syn.shift (succ N)) :: Γ.map Fm.shift) ⊢[PRAAx]
        Lam w (var 0) (Syn.shift y) ≐ zero :=
      (congrAp2 (sumF (lamB w)) (congrSucc e) (congrPairT e (.eqRefl _))).eqTrans (lam_zero w _)
    exact ((congrMul (.eqRefl _) hz).eqTrans (mul_zero _)).eqTrans hz.eqSymm
  · exact (congrMul ((congrSg Prf.hyp0).eqTrans (sg_succ _)) (.eqRefl _)).eqTrans (one_mul _)

/-! ## The product form -/

/-- `L_w(P⁺(N)) = L_w(lcm(1, …, N) · P⁻(N))` for every weight `w`. -/
theorem lw_product (w : PTm 2) (N y : PTm n) :
    Γ ⊢[PRAAx] Lw w (Pp aPB N N) y ≐ Lw w (lcmu N * Pp aNB N N) y := by
  have cm := chebyshev_mertens (Γ := Γ) w N y
  have rP := rowsum (Γ := Γ) aPB w (fun m y => Bs_aP m y) N y
  have rN := rowsum (Γ := Γ) aNB w (fun m y => Bs_aN m y) N y
  have e1 : Γ ⊢[PRAAx] Lw w (Pp aPB N N) y ≐ Lw w (lcmu N) y + Lw w (Pp aNB N N) y :=
    (lw_prod aPB w N y N).eqTrans (rP.eqSymm.eqTrans (cm.eqTrans
      (congrAdd (psi_sg w N y) (rN.eqTrans (lw_prod aNB w N y N).eqSymm))))
  exact e1.eqTrans (lw_mul w (lcmu_pos N) (Pp_pos aNB N N)).eqSymm

/-- `v_p(P⁺(N)) = v_p(lcm(1, …, N) · P⁻(N))` for every prime `p`. -/
theorem val_product {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (N : PTm n) :
    Γ ⊢[PRAAx] val p (Pp aPB N N) ≐ val p (lcmu N * Pp aNB N N) :=
  (lw_delta hp (Pp_pos aPB N N)).eqSymm.eqTrans ((lw_product dW N p).eqTrans
    (lw_delta hp (Combinatorics.Binomial.pos_mul (lcmu_pos N) (Pp_pos aNB N N))))

/-- **`thm:totient-chebyshev`, product form**: `∏_{a=1}^{N} a^{M⁺(⌊N/a⌋)} = lcm(1, …, N) · ∏_{a=1}^{N} a^{M⁻(⌊N/a⌋)}`,
that is `∏_{a=1}^{N} a^{M(⌊N/a⌋)} = lcm(1, …, N)`. -/
theorem mertens_lcm_product (N : PTm n) : Γ ⊢[PRAAx] Pp aPB N N ≐ lcmu N * Pp aNB N N := by
  refine val_ext (Pp_pos aPB N N) (Combinatorics.Binomial.pos_mul (lcmu_pos N) (Pp_pos aNB N N)) (.allI (.impI ?_))
  have sA : Syn.shift (Pp aPB N N) = Pp aPB (Syn.shift N) (Syn.shift N) := by simp [Syn.shift]
  have sB : Syn.shift (lcmu N * Pp aNB N N) = lcmu (Syn.shift N) * Pp aNB (Syn.shift N) (Syn.shift N) := by
    simp [Syn.shift]
  rw [sA, sB]
  exact val_product (prime_of_isP Prf.hyp0) _

end LeanProofs.IPRA.AnalyticNumberTheory.MertensLcm
