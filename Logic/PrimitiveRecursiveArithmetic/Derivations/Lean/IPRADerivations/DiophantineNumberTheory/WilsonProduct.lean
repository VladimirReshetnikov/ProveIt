import IPRADerivations.DiophantineNumberTheory.PairProduct
import IPRADerivations.DiophantineNumberTheory.ResidueFacts

/-!
# Wilson's product

Packet: `diophantine-number-theory/quadratic_reciprocity_ipra`, `quadratic_reciprocity.tex`, §"A square test from
an involution", "Wilson's product":

  "Take `a = 1`. From `(x − 1)(x + 1) ≡ 0`, the roots are precisely `1` and `p − 1`. They are distinct since
  `p ≥ 3`. Their product is `−1`, and all other pairs have product `1`. Thus `F ≡ −1`."

For an odd prime `p`:

  `(p − 1)! ≡ p − 1 (mod p)`                                                              (`wilson`).

It is `PairProduct.pair_congr` at `a = 1`: the factor `1^c` is `1`, and the product over the fixed points of
`σ(i) = (i + 1)⁻¹ − 1` is evaluated. For `i < p − 1`, with `M = p − 1`,

  `[σ(i) = i] = [i = 0] + [i = M − 1]`                                                      (`fixed_pt`),

by `ResidueFacts.sq_one` (a fixed point is a square root of `1`) and by `1 · 1 ≡ 1`, `(p − 1)² ≡ 1`
(`T_one`, `T_neg`); so the product is `(0 + 1) · (M − 1 + 1) = p − 1` by two delta products
(`Foundations/ProductPowers.prod_delta`).
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.WilsonProduct

open_ipra exports
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (prime_two inst2_mulB congrEqb')
open LeanProofs.IPRA.AnalyticNumberTheory.ConvolutionAssoc (rem_small)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open LeanProofs.IPRA.DiophantineNumberTheory.UnitInvolution (sB s_at unit_of_lt fixed_sq succ_lt_of)
open LeanProofs.IPRA.DiophantineNumberTheory.ResidueFacts (neg_sq sq_one)
open LeanProofs.IPRA.DiophantineNumberTheory.PairProduct (idB inst2_idB pair_congr)
open LeanProofs.IPRA.Foundations.InvolutionPairing (EB inst2_EB inst2_pw)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## The two fixed points -/

theorem one_one : Γ ⊢[PRAAx] (one : PTm n) * one ≐ one := by ipra_ring

/-- `T(1) = 1` for `a = 1`. -/
theorem T_one {p : PTm n} (hq : Γ ⊢[PRAAx] le two p) : Γ ⊢[PRAAx] res one p one ≐ one :=
  (res_unique hq (gcd_one_left p) hq (congrAp2 remF one_one (.eqRefl _))).eqSymm

/-- `p − 1 < p` for `p ≥ 1`. -/
alias pred_lt := Common.pred_lt

/-- `p − 1 ≥ 1` for `p ≥ 2`. -/
theorem pred_pos {p : PTm n} (hq : Γ ⊢[PRAAx] le two p) : Γ ⊢[PRAAx] pred p ≐ succ (pred (pred p)) := by
  refine pos_of_eq_succ (c := monus p two) ?_
  ipra_lc natEq (eq_add_of_le hq) - natEq (p_pos hq)

/-- `T(p − 1) = p − 1` for `a = 1`, for a prime `p`. -/
theorem T_neg {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) : Γ ⊢[PRAAx] res (pred p) p one ≐ pred p := by
  have hq := prime_two hp
  have hp1 := p_pos hq
  have hu := unit_of_lt hp (pred_pos hq) (pred_lt hp1)
  exact (res_unique hq hu (pred_lt hp1) (neg_sq hq)).eqSymm

/-! ## The fixed-point indicator -/

theorem v10 {e0 e1 : PTm n} (h0 : Γ ⊢[PRAAx] e0 ≐ one) (h1 : Γ ⊢[PRAAx] e1 ≐ zero) :
    Γ ⊢[PRAAx] (one : PTm n) ≐ e0 + e1 := by
  ipra_lc -natEq h0 - natEq h1

theorem v01 {e0 e1 : PTm n} (h0 : Γ ⊢[PRAAx] e0 ≐ zero) (h1 : Γ ⊢[PRAAx] e1 ≐ one) :
    Γ ⊢[PRAAx] (one : PTm n) ≐ e0 + e1 := by
  ipra_lc -natEq h0 - natEq h1

theorem v00 {e0 e1 : PTm n} (h0 : Γ ⊢[PRAAx] e0 ≐ zero) (h1 : Γ ⊢[PRAAx] e1 ≐ zero) :
    Γ ⊢[PRAAx] (zero : PTm n) ≐ e0 + e1 := by
  ipra_lc -natEq h0 - natEq h1

/-- `[σ(i) = i] = [i = 0] + [i = M − 1]` for `i < M = p − 1`, `a = 1` and a prime `p ≥ 3`. -/
theorem fixed_pt {p i : PTm n} (hp : Γ ⊢[PRAAx] prime p)
    (hM : Γ ⊢[PRAAx] pred (pred p) ≐ succ (pred (pred (pred p)))) (hi : Γ ⊢[PRAAx] lt i (pred p)) :
    Γ ⊢[PRAAx] eqb i (pred (res (succ i) p one)) ≐ eqb zero i + eqb (pred (pred p)) i := by
  have hq := prime_two hp
  have hp1 := p_pos hq
  have hc : Γ ⊢[PRAAx] gcd p one ≐ one := gcd_comm_one hp1 (gcd_one_left p)
  refine .orE (eq_or_ne i zero) ?_ ?_
  · -- `i = 0`
    let C : List (Fm PTm n) := (i ≐ zero) :: Γ
    have e : C ⊢[PRAAx] i ≐ zero := Prf.hyp0
    have s : C ⊢[PRAAx] pred (res (succ i) p one) ≐ zero :=
      (congrPred ((UnitInvolution.congrRes (congrSucc e) (.eqRefl _) (.eqRefl _)).eqTrans (T_one hq.wk))).eqTrans
        (pred_succ _)
    have l : C ⊢[PRAAx] eqb i (pred (res (succ i) p one)) ≐ one := eqb_of_eq (e.eqTrans s.eqSymm)
    have r0 : C ⊢[PRAAx] eqb zero i ≐ one := eqb_of_eq e.eqSymm
    have r1 : C ⊢[PRAAx] eqb (pred (pred p)) i ≐ zero :=
      eqb_of_ne (.impI (succ_ne_zero' _ (hM.wk.wk.eqSymm.eqTrans (Prf.hyp0.eqTrans e.wk))))
    exact l.eqTrans (v10 r0 r1)
  · refine .orE (eq_or_ne i (pred (pred p))) ?_ ?_
    · -- `i = M − 1`
      let C : List (Fm PTm n) := (i ≐ pred (pred p)) :: neg (i ≐ zero) :: Γ
      have e : C ⊢[PRAAx] i ≐ pred (pred p) := Prf.hyp0
      have n0 : C ⊢[PRAAx] neg (i ≐ zero) := Prf.hyp1
      have sx : C ⊢[PRAAx] succ i ≐ pred p := (congrSucc e).eqTrans (pred_pos hq.wk.wk).eqSymm
      have s : C ⊢[PRAAx] pred (res (succ i) p one) ≐ pred (pred p) :=
        congrPred ((UnitInvolution.congrRes sx (.eqRefl _) (.eqRefl _)).eqTrans (T_neg hp.wk.wk))
      have l : C ⊢[PRAAx] eqb i (pred (res (succ i) p one)) ≐ one := eqb_of_eq (e.eqTrans s.eqSymm)
      have r0 : C ⊢[PRAAx] eqb zero i ≐ zero :=
        eqb_of_ne (.impI (.impE n0.wk (Prf.hyp0 : ((zero ≐ i) :: C) ⊢[PRAAx] zero ≐ i).eqSymm))
      have r1 : C ⊢[PRAAx] eqb (pred (pred p)) i ≐ one := eqb_of_eq e.eqSymm
      exact l.eqTrans (v01 r0 r1)
    · -- neither: no fixed point
      let C : List (Fm PTm n) := neg (i ≐ pred (pred p)) :: neg (i ≐ zero) :: Γ
      have n1 : C ⊢[PRAAx] neg (i ≐ pred (pred p)) := Prf.hyp0
      have n0 : C ⊢[PRAAx] neg (i ≐ zero) := Prf.hyp1
      have l : C ⊢[PRAAx] eqb i (pred (res (succ i) p one)) ≐ zero := by
        refine eqb_of_ne (.impI ?_)
        let D : List (Fm PTm n) := (i ≐ pred (res (succ i) p one)) :: C
        have fs := fixed_sq (Γ := D) hp.wk.wk.wk hc.wk.wk.wk hi.wk.wk.wk Prf.hyp0
        have so := sq_one (Γ := D) hp.wk.wk.wk (congrSucc (pred_succ _).eqSymm)
          (succ_lt_of hp1.wk.wk.wk hi.wk.wk.wk) fs
        refine .orE so ?_ ?_
        · have i0 : ((succ i ≐ one) :: D) ⊢[PRAAx] i ≐ zero :=
            (pred_succ i).eqSymm.eqTrans ((congrPred Prf.hyp0).eqTrans (pred_succ _))
          exact .impE n0.wk.wk i0
        · have i1 : ((succ i ≐ pred p) :: D) ⊢[PRAAx] i ≐ pred (pred p) :=
            (pred_succ i).eqSymm.eqTrans (congrPred Prf.hyp0)
          exact .impE n1.wk.wk i1
      have r0 : C ⊢[PRAAx] eqb zero i ≐ zero :=
        eqb_of_ne (.impI (.impE n0.wk (Prf.hyp0 : ((zero ≐ i) :: C) ⊢[PRAAx] zero ≐ i).eqSymm))
      have r1 : C ⊢[PRAAx] eqb (pred (pred p)) i ≐ zero :=
        eqb_of_ne (.impI (.impE n1.wk
          (Prf.hyp0 : ((pred (pred p) ≐ i) :: C) ⊢[PRAAx] pred (pred p) ≐ i).eqSymm))
      exact l.eqTrans (v00 r0 r1)

/-! ## The product over the fixed points -/

/-- `(i + 1)^{[i = 0]}` over `0 = i`. -/
abbrev d0B : PTm 2 := pw idB (eqb zero (var 0))
/-- `(i + 1)^{[i = p − 2]}` over `0 = i`, `1 = ⟨p, a⟩`. -/
abbrev d1B : PTm 2 := pw idB (eqb (pred (pred (fstT (var 1)))) (var 0))

theorem inst2_d0B (i y : PTm n) : inst2 d0B i y = pw (succ i) (eqb zero i) := by simp [inst2]
theorem inst2_d1B (i y : PTm n) : inst2 d1B i y = pw (succ i) (eqb (pred (pred (fstT y))) i) := by simp [inst2]

/-- `∏_{i<M} (i + 1)^{[i = c]} = c + 1` for `c < M`, for a body `D` with these factors. -/
theorem delta_id (D : PTm 2) {M c y : PTm n} (hc : Γ ⊢[PRAAx] lt c M)
    (hD : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift M) ⟶
      (inst2 D (var 0) (Syn.shift y) ≐ pw (succ (var 0)) (eqb (Syn.shift c) (var 0))))) :
    Γ ⊢[PRAAx] ap2 (prodF D) M y ≐ succ c := by
  have pd := prod_delta (Γ := Γ) idB (x := y) hc
  rw [inst2_idB] at pd
  refine (prod_congr_bounded D (pdB idB) y (pairT c y) M (.allI (.impI ?_))).eqTrans pd
  rw [shift_pairT, inst2_pdB, inst2_idB]
  exact (Prf.impE hD.allOpen.wk Prf.hyp0).eqTrans (congrPw (.eqRefl _) (congrEqb' (fst_pair _ _).eqSymm (.eqRefl _)))

theorem one_mul_succ {M : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) :
    Γ ⊢[PRAAx] succ zero * succ (pred M) ≐ M := by
  ipra_lc -natEq hM

/-- `∏_{i<p−1} (i + 1)^{[σ(i) = i]} = p − 1` for `a = 1` and a prime `p ≥ 3`. -/
theorem fixed_prod {p : PTm n} (hp : Γ ⊢[PRAAx] prime p)
    (hM : Γ ⊢[PRAAx] pred (pred p) ≐ succ (pred (pred (pred p)))) :
    Γ ⊢[PRAAx] ap2 (prodF (pw idB (EB sB))) (pred p) (pairT p one) ≐ pred p := by
  have hq := prime_two hp
  have hp' : (Γ.map Fm.shift) ⊢[PRAAx] prime (Syn.shift p) := by simpa [Fm.shift, Syn.shift] using hp.shift
  have hM' : (Γ.map Fm.shift) ⊢[PRAAx] pred (pred (Syn.shift p)) ≐ succ (pred (pred (pred (Syn.shift p)))) := by
    simpa [Fm.shift, Syn.shift] using hM.shift
  have sM : Syn.shift (pred p) = pred (Syn.shift p) := by simp [Syn.shift]
  have sMM : Syn.shift (pred (pred p)) = pred (pred (Syn.shift p)) := by simp [Syn.shift]
  have s1 : Syn.shift (pairT p one) = pairT (Syn.shift p) one := by simp [Syn.shift]
  have hMp : Γ ⊢[PRAAx] pred p ≐ succ (pred (pred p)) := pred_pos hq
  -- the product splits into the two delta products
  have sp : Γ ⊢[PRAAx] ap2 (prodF (pw idB (EB sB))) (pred p) (pairT p one) ≐
      ap2 (prodF (d0B * d1B)) (pred p) (pairT p one) := by
    refine prod_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [s1, sM, inst2_pw, inst2_idB, inst2_EB, inst2_mulB, inst2_d0B, inst2_d1B]
    have f := fixed_pt (Γ := lt (var 0) (pred (Syn.shift p)) :: Γ.map Fm.shift) hp'.wk hM'.wk Prf.hyp0
    exact (congrPw (.eqRefl _) ((congrEqb' (.eqRefl _) (s_at _ _ _)).eqTrans
      (f.eqTrans (congrAdd (.eqRefl _) (congrEqb' (congrPred (congrPred (fst_pair _ _))).eqSymm (.eqRefl _)))))).eqTrans
      (pw_add _ _ _)
  have p0 : Γ ⊢[PRAAx] ap2 (prodF d0B) (pred p) (pairT p one) ≐ succ zero := by
    refine delta_id d0B (c := zero) (Order.zero_lt_of_eq_succ hMp) (.allI (.impI ?_))
    have sz : Syn.shift (zero : PTm n) = zero := by simp [Syn.shift]
    rw [sz, inst2_d0B]
    exact .eqRefl _
  have p1 : Γ ⊢[PRAAx] ap2 (prodF d1B) (pred p) (pairT p one) ≐ succ (pred (pred p)) := by
    refine delta_id d1B (c := pred (pred p)) (le_congr (.eqRefl _) hMp.eqSymm (le_refl _)) (.allI (.impI ?_))
    rw [s1, sMM, inst2_d1B]
    exact congrPw (.eqRefl _) (congrEqb' (congrPred (congrPred (fst_pair _ _))) (.eqRefl _))
  exact sp.eqTrans ((prod_mul d0B d1B (pred p) (pairT p one)).eqTrans
    ((congrMul p0 p1).eqTrans (one_mul_succ hMp)))

/-! ## Wilson's product -/

theorem one_mul_r (t : PTm n) : Γ ⊢[PRAAx] one * t ≐ t := one_mul t

/-- `(p − 1)! ≡ p − 1 (mod p)` for an odd prime `p`. -/
theorem wilson {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hodd : Γ ⊢[PRAAx] par p ≐ one) :
    Γ ⊢[PRAAx] rem (fact (pred p)) p ≐ pred p := by
  have hq := prime_two hp
  have hp1 := p_pos hq
  have hc : Γ ⊢[PRAAx] gcd p one ≐ one := gcd_comm_one hp1 (gcd_one_left p)
  have ha : Γ ⊢[PRAAx] gcd one p ≐ one := gcd_one_left p
  -- `p − 2 ≥ 1`: otherwise `p = 2`, which is even
  have hM : Γ ⊢[PRAAx] pred (pred p) ≐ succ (pred (pred (pred p))) := by
    refine .orE (zero_or_succ (pred (pred p))) ?_ Prf.hyp0
    have e2 : ((pred (pred p) ≐ zero) :: Γ) ⊢[PRAAx] p ≐ two :=
      hp1.wk.eqTrans (congrSucc ((pred_pos hq.wk).eqTrans (congrSucc Prf.hyp0)))
    have pe : ((pred (pred p) ≐ zero) :: Γ) ⊢[PRAAx] par p ≐ zero :=
      (congrAp1 parF e2).eqTrans ((par_succ _).eqTrans ((congrMonus (.eqRefl _)
        ((par_succ _).eqTrans ((congrMonus (.eqRefl _) par_zero).eqTrans (monus_zero _)))).eqTrans (monus_self _)))
    exact Foundations.BoundedReflection.one_ne_zero _ (hodd.wk.eqSymm.eqTrans pe)
  have pc := pair_congr hp hc ha
  have fp := fixed_prod hp hM
  exact pc.eqTrans ((congrAp2 remF ((congrMul (pw_one_base _) fp).eqTrans (one_mul _)) (.eqRefl _)).eqTrans
    (rem_small (pred_lt hp1)))

end LeanProofs.IPRA.DiophantineNumberTheory.WilsonProduct
