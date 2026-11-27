import IPRADerivations.AnalyticNumberTheory.BlockMass
import IPRADerivations.Core.Header
import IPRADerivations.Core.SumOrder

/-!
# The three case sums of the block deficit (`pnt_ipra_constructive_2026-11-14`, `con:deficit`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `contraction.tex`, proof of Lemma `con:deficit`.
On a block of divisors `D₁ < d ≤ D₂` with values `P = ψ(⌊x/d⌋)`, `Q = F⌊x/d⌋`, the deficit term is
`g = AQ ∸ D|P − Q|` (`a = A/D`, body `gzB`). Summing `PointDeficit` over the block:

* `case_lo_sum` ("`b_i < a/4` … `r(t) < a/2`; `a − |z| ≥ (a + z)/3`"): if `D|P − Q| ≤ AQ` and `2D(P ∸ Q) ≤ AQ`
  on the block, then `A ΣQ + D ΣP ≤ 3 Σg + D ΣQ`;
* `case_hi_sum` (the second half, `r > −a/2`): `A ΣQ + D ΣQ ≤ 3 Σg + D ΣP`;
* `case_mid_sum` (between the crossing samples, `|r| < a/2`): `A ΣQ ≤ 2 Σg`.

The block hypotheses are iPRA formulas `∀d < x + 1. D₁ < d → d ≤ D₂ → …` read at `d = var 0` with `allOpen`.
`sum_le_two` sums a pointwise inequality with two bodies on each side.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.BlockDeficit

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicChebyshev (wt)
open LeanProofs.IPRA.AnalyticNumberTheory.SummatoryCompose (hRB)
open LeanProofs.IPRA.AnalyticNumberTheory.PointDeficit (dg def_lo def_hi def_mid)
open LeanProofs.IPRA.AnalyticNumberTheory.BlockSums (Y biB pzB fzB bi_at pz_at fz_at ind0 ind1)
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.Signum (sg sg_succ)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Summing a two-body inequality -/

/-- `a₁ f₁ + a₂ f₂ ≤ c₁ g₁ + c₂ g₂` pointwise for `i < N` gives the same for the sums. -/
theorem sum_le_two (f1 f2 g1 g2 : PTm 2) (a1 a2 c1 c2 x N : PTm n)
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (Syn.shift a1 * inst2 f1 (var 0) (Syn.shift x) + Syn.shift a2 * inst2 f2 (var 0) (Syn.shift x))
        (Syn.shift c1 * inst2 g1 (var 0) (Syn.shift x) + Syn.shift c2 * inst2 g2 (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] le (a1 * ap2 (sumF f1) N x + a2 * ap2 (sumF f2) N x)
      (c1 * ap2 (sumF g1) N x + c2 * ap2 (sumF g2) N x) := by
  exact sum_weighted_pair_le f1 f2 g1 g2 a1 a2 c1 c2 x x x x N h

/-! ## The deficit body -/

abbrev AwB : PTm 2 := fstT (fstT (sndT (sndT (var 1))))
abbrev DwB : PTm 2 := sndT (fstT (sndT (sndT (var 1))))
/-- `AQ ∸ D|P − Q|` at `m`, read from the layout. -/
abbrev gzB : PTm 2 := monus (AwB * fzB) (DwB * absd pzB fzB)

theorem aw_at (m D₁ D₂ A Ds z : PTm n) : Γ ⊢[PRAAx] inst2 AwB m (BlockSums.Y D₁ D₂ (pairT A Ds) z) ≐ A := by
  rw [show inst2 AwB m (BlockSums.Y D₁ D₂ (pairT A Ds) z) = fstT (fstT (sndT (sndT (BlockSums.Y D₁ D₂ (pairT A Ds) z)))) by simp [inst2]]
  exact (congrFst ((congrFst ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _))).eqTrans
    (fst_pair _ _)

theorem dw_at (m D₁ D₂ A Ds z : PTm n) : Γ ⊢[PRAAx] inst2 DwB m (BlockSums.Y D₁ D₂ (pairT A Ds) z) ≐ Ds := by
  rw [show inst2 DwB m (BlockSums.Y D₁ D₂ (pairT A Ds) z) = sndT (fstT (sndT (sndT (BlockSums.Y D₁ D₂ (pairT A Ds) z)))) by simp [inst2]]
  exact (congrSnd ((congrFst ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _))).eqTrans
    (snd_pair _ _)

theorem gz_at (m D₁ D₂ A Ds K F : PTm n) :
    Γ ⊢[PRAAx] inst2 gzB m (BlockSums.Y D₁ D₂ (pairT A Ds) (pairT K F)) ≐ dg A Ds (Psi wt m (pairT K F)) (F * m) := by
  have raw : inst2 gzB m (BlockSums.Y D₁ D₂ (pairT A Ds) (pairT K F)) =
      monus (inst2 AwB m (BlockSums.Y D₁ D₂ (pairT A Ds) (pairT K F)) * inst2 fzB m (BlockSums.Y D₁ D₂ (pairT A Ds) (pairT K F)))
        (inst2 DwB m (BlockSums.Y D₁ D₂ (pairT A Ds) (pairT K F)) *
          (monus (inst2 pzB m (BlockSums.Y D₁ D₂ (pairT A Ds) (pairT K F))) (inst2 fzB m (BlockSums.Y D₁ D₂ (pairT A Ds) (pairT K F))) +
            monus (inst2 fzB m (BlockSums.Y D₁ D₂ (pairT A Ds) (pairT K F))) (inst2 pzB m (BlockSums.Y D₁ D₂ (pairT A Ds) (pairT K F))))) := by
    simp only [inst2, gzB, absd, PTm.subst_monus, PTm.subst_mul, PTm.subst_add]
  rw [raw]
  have ep := pz_at (Γ := Γ) m D₁ D₂ (pairT A Ds) K F
  have ef := fz_at (Γ := Γ) m D₁ D₂ (pairT A Ds) K F
  exact congrMonus (congrMul (aw_at _ _ _ _ _ _) ef)
    (congrMul (dw_at _ _ _ _ _ _) (congrAdd (congrMonus ep ef) (congrMonus ef ep)))

/-! ## The indicator in the three positions -/

abbrev bv (d D₁ D₂ : PTm n) : PTm n := monus (monus one (monus d D₂)) (monus one (monus d D₁))

theorem bv_below {d D₁ D₂ : PTm n} (h12 : Γ ⊢[PRAAx] le D₁ D₂) (h : Γ ⊢[PRAAx] le d D₁) :
    Γ ⊢[PRAAx] bv d D₁ D₂ ≐ zero :=
  (congrMonus (ind1 (le_trans h h12)) (ind1 h)).eqTrans (monus_self _)

theorem bv_above {d D₁ D₂ : PTm n} (h12 : Γ ⊢[PRAAx] le D₁ D₂) (h : Γ ⊢[PRAAx] lt D₂ d) :
    Γ ⊢[PRAAx] bv d D₁ D₂ ≐ zero :=
  (congrMonus (ind0 h) (ind0 (lt_of_le_of_lt h12 h))).eqTrans (zero_monus _)

theorem bv_in {d D₁ D₂ : PTm n} (h1 : Γ ⊢[PRAAx] lt D₁ d) (h2 : Γ ⊢[PRAAx] le d D₂) :
    Γ ⊢[PRAAx] bv d D₁ D₂ ≐ one :=
  (congrMonus (ind1 h2) (ind0 h1)).eqTrans (monus_zero _)

/-- The block weight `[d ≥ 1][D₁ < d ≤ D₂]`. -/
abbrev tw (d D₁ D₂ : PTm n) : PTm n := sg d * bv d D₁ D₂

theorem term_at (h : PTm 2) (d X D₁ D₂ w z : PTm n) :
    Γ ⊢[PRAAx] inst2 (hRB h biB) d (pairT X (BlockSums.Y D₁ D₂ w z)) ≐ tw d D₁ D₂ * inst2 h (quo X d) (BlockSums.Y D₁ D₂ w z) :=
  (hRB_at _ _ _ _ _).eqTrans (congrMul (congrMul (.eqRefl _) (bi_at _ _ _ _ _)) (.eqRefl _))

/-- Outside the block the weight vanishes; inside it is one and `d ≥ 1`. -/
theorem tw_cases {d D₁ D₂ : PTm n} (h12 : Γ ⊢[PRAAx] le D₁ D₂) (φ : Fm PTm n)
    (h0 : ((tw d D₁ D₂ ≐ zero) :: Γ) ⊢[PRAAx] φ)
    (h1 : ((tw d D₁ D₂ ≐ one) :: (le d D₂) :: (lt D₁ d) :: Γ) ⊢[PRAAx] φ) : Γ ⊢[PRAAx] φ := by
  refine .orE (lt_or_le D₁ d) ?_ ?_
  · refine .orE (lt_or_le D₂ d) ?_ ?_
    · have z := bv_above (h12.wk.wk) (Prf.hyp0 : ((lt D₂ d) :: (lt D₁ d) :: Γ) ⊢[PRAAx] lt D₂ d)
      have t : ((lt D₂ d) :: (lt D₁ d) :: Γ) ⊢[PRAAx] tw d D₁ D₂ ≐ zero :=
        (congrMul (.eqRefl _) z).eqTrans (by ipra_ring)
      exact Prf.impE (Prf.impI h0).wk.wk t
    · have hd : ((le d D₂) :: (lt D₁ d) :: Γ) ⊢[PRAAx] d ≐ succ (pred d) :=
        LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep.pos_of_one_le
          (le_trans ((succ_monus_succ _ _).eqTrans (zero_le _)) Prf.hyp1)
      have o := bv_in (Prf.hyp1 : ((le d D₂) :: (lt D₁ d) :: Γ) ⊢[PRAAx] lt D₁ d) Prf.hyp0
      have s := (congrSg hd).eqTrans (sg_succ _)
      have t : ((le d D₂) :: (lt D₁ d) :: Γ) ⊢[PRAAx] tw d D₁ D₂ ≐ one :=
        (congrMul s o).eqTrans (by ipra_ring)
      exact Prf.impE (Prf.impI h1) t
  · have z := bv_below h12.wk (Prf.hyp0 : ((le d D₁) :: Γ) ⊢[PRAAx] le d D₁)
    have t : ((le d D₁) :: Γ) ⊢[PRAAx] tw d D₁ D₂ ≐ zero :=
      (congrMul (.eqRefl _) z).eqTrans (by ipra_ring)
    exact Prf.impE (Prf.impI h0).wk t

/-! ## The case sums -/

section Cases

variable {x D₁ D₂ A Ds K L : PTm n}

/-- The block value `ψ(⌊x/d⌋)` at `d = var 0`, shifted. -/
abbrev Pm (x K L : PTm n) : PTm (n + 1) :=
  Psi wt (quo (Syn.shift x) (var 0)) (pairT (Syn.shift K) (fact (Syn.shift L)))
/-- The block value `F⌊x/d⌋` at `d = var 0`, shifted. -/
abbrev Qm (x L : PTm n) : PTm (n + 1) := fact (Syn.shift L) * quo (Syn.shift x) (var 0)

/-- The stage bound `D|P − Q| ≤ AQ` at `d = var 0`. -/
abbrev stg (x A Ds K L : PTm n) : Fm PTm (n + 1) :=
  le (Syn.shift Ds * absd (Pm x K L) (Qm x L)) (Syn.shift A * Qm x L)

/-- `∀d < x + 1. D₁ < d → d ≤ D₂ → φ(d)`. -/
abbrev OnBlock (x D₁ D₂ : PTm n) (φ : Fm PTm (n + 1)) : Fm PTm n :=
  Fm.all (lt (var 0) (Syn.shift (succ x)) ⟶ (lt (Syn.shift D₁) (var 0) ⟶ (le (var 0) (Syn.shift D₂) ⟶ φ)))

abbrev Ctx (x : PTm n) (Γ : List (Fm PTm n)) : List (Fm PTm (n + 1)) :=
  lt (var 0) (Syn.shift (succ x)) :: Γ.map Fm.shift

theorem on_block {φ : Fm PTm (n + 1)} (hb : Γ ⊢[PRAAx] OnBlock x D₁ D₂ φ) {ψ : Fm PTm (n + 1)} :
    (ψ :: le (var 0) (Syn.shift D₂) :: lt (Syn.shift D₁) (var 0) :: Ctx x Γ) ⊢[PRAAx] φ :=
  Prf.impE (Prf.impE (Prf.impE hb.allOpen.wk.wk.wk.wk (.hyp (by simp))) (.hyp (by simp))) (.hyp (by simp))

abbrev Ys (x D₁ D₂ A Ds K L : PTm n) : PTm (n + 1) :=
  pairT (Syn.shift x) (BlockSums.Y (Syn.shift D₁) (Syn.shift D₂) (pairT (Syn.shift A) (Syn.shift Ds))
    (pairT (Syn.shift K) (fact (Syn.shift L))))

theorem term_f {Δ : List (Fm PTm (n + 1))} :
    Δ ⊢[PRAAx] inst2 (hRB fzB biB) (var 0) (pairT (Syn.shift x) (pairT (Syn.shift D₁) (pairT (Syn.shift D₂) (pairT (pairT (Syn.shift A) (Syn.shift Ds)) (pairT (Syn.shift K) (fact (Syn.shift L))))))) ≐
      tw (var 0) (Syn.shift D₁) (Syn.shift D₂) * Qm x L :=
  (term_at _ _ _ _ _ _ _).eqTrans (congrMul (.eqRefl _) (fz_at _ _ _ _ _ _))

theorem term_p {Δ : List (Fm PTm (n + 1))} :
    Δ ⊢[PRAAx] inst2 (hRB pzB biB) (var 0) (pairT (Syn.shift x) (pairT (Syn.shift D₁) (pairT (Syn.shift D₂) (pairT (pairT (Syn.shift A) (Syn.shift Ds)) (pairT (Syn.shift K) (fact (Syn.shift L))))))) ≐
      tw (var 0) (Syn.shift D₁) (Syn.shift D₂) * Pm x K L :=
  (term_at _ _ _ _ _ _ _).eqTrans (congrMul (.eqRefl _) (pz_at _ _ _ _ _ _))

theorem term_g {Δ : List (Fm PTm (n + 1))} :
    Δ ⊢[PRAAx] inst2 (hRB gzB biB) (var 0) (pairT (Syn.shift x) (pairT (Syn.shift D₁) (pairT (Syn.shift D₂) (pairT (pairT (Syn.shift A) (Syn.shift Ds)) (pairT (Syn.shift K) (fact (Syn.shift L))))))) ≐
      tw (var 0) (Syn.shift D₁) (Syn.shift D₂) * dg (Syn.shift A) (Syn.shift Ds) (Pm x K L) (Qm x L) :=
  (term_at _ _ _ _ _ _ _).eqTrans (congrMul (.eqRefl _) (gz_at _ _ _ _ _ _ _))

abbrev Bs' (h : PTm 2) (x D₁ D₂ A Ds K L : PTm n) : PTm n :=
  ap2 (sumF (hRB h biB)) (succ x) (pairT x (BlockSums.Y D₁ D₂ (pairT A Ds) (pairT K (fact L))))

abbrev TW (D₁ D₂ : PTm n) : PTm (n + 1) := tw (var 0) (Syn.shift D₁) (Syn.shift D₂)

/-- Case 1: `A ΣQ + D ΣP ≤ 3 Σg + D ΣQ` on a block where `r ≤ a/2`. -/
theorem case_lo_sum (h12 : Γ ⊢[PRAAx] le D₁ D₂)
    (hb : Γ ⊢[PRAAx] OnBlock x D₁ D₂ (stg x A Ds K L ⋏
      le (two * (Syn.shift Ds * monus (Pm x K L) (Qm x L))) (Syn.shift A * Qm x L))) :
    Γ ⊢[PRAAx] le (A * Bs' fzB x D₁ D₂ A Ds K L + Ds * Bs' pzB x D₁ D₂ A Ds K L)
      (num 3 * Bs' gzB x D₁ D₂ A Ds K L + Ds * Bs' fzB x D₁ D₂ A Ds K L) := by
  have h12' := LeanProofs.IPRA.Order.shift_le h12
  refine sum_le_two _ _ _ _ _ _ _ _ _ _ (.allI (.impI ?_))
  simp only [shift_pairT, shift_fact', show Syn.shift (num 3 : PTm n) = num 3 by simp [Syn.shift, PTm.subst_num]]
  refine tw_cases (d := var 0) h12'.wk _ ?_ ?_
  · have et := natEq (Prf.hyp0 : ((TW D₁ D₂ ≐ zero) :: Ctx x Γ) ⊢[PRAAx] _)
    have ef := natEq (term_f (Δ := (TW D₁ D₂ ≐ zero) :: Ctx x Γ) (x := x) (D₁ := D₁) (D₂ := D₂) (A := A) (Ds := Ds) (K := K) (L := L))
    have ep := natEq (term_p (Δ := (TW D₁ D₂ ≐ zero) :: Ctx x Γ) (x := x) (D₁ := D₁) (D₂ := D₂) (A := A) (Ds := Ds) (K := K) (L := L))
    have eg := natEq (term_g (Δ := (TW D₁ D₂ ≐ zero) :: Ctx x Γ) (x := x) (D₁ := D₁) (D₂ := D₂) (A := A) (Ds := Ds) (K := K) (L := L))
    ipra_le 0 with 3 * eg + (𝔞 (Syn.shift Ds) - 𝔞 (Syn.shift A)) * ef - 𝔞 (Syn.shift Ds) * ep +
      (3 * 𝔞 (dg (Syn.shift A) (Syn.shift Ds) (Pm x K L) (Qm x L)) + (𝔞 (Syn.shift Ds) - 𝔞 (Syn.shift A)) *
        (𝔞 (fact (Syn.shift L)) * 𝔞 (quo (Syn.shift x) (var 0))) - 𝔞 (Syn.shift Ds) * 𝔞 (Pm x K L)) * et
  · have hb' := on_block hb (ψ := TW D₁ D₂ ≐ one)
    have dl := def_lo (Prf.andE₁ hb') (Prf.andE₂ hb')
    have et := natEq (Prf.hyp0 : ((TW D₁ D₂ ≐ one) :: le (var 0) (Syn.shift D₂) ::
      lt (Syn.shift D₁) (var 0) :: Ctx x Γ) ⊢[PRAAx] _)
    have ef := natEq (term_f (Δ := (TW D₁ D₂ ≐ one) :: le (var 0) (Syn.shift D₂) :: lt (Syn.shift D₁) (var 0) :: Ctx x Γ)
      (x := x) (D₁ := D₁) (D₂ := D₂) (A := A) (Ds := Ds) (K := K) (L := L))
    have ep := natEq (term_p (Δ := (TW D₁ D₂ ≐ one) :: le (var 0) (Syn.shift D₂) :: lt (Syn.shift D₁) (var 0) :: Ctx x Γ)
      (x := x) (D₁ := D₁) (D₂ := D₂) (A := A) (Ds := Ds) (K := K) (L := L))
    have eg := natEq (term_g (Δ := (TW D₁ D₂ ≐ one) :: le (var 0) (Syn.shift D₂) :: lt (Syn.shift D₁) (var 0) :: Ctx x Γ)
      (x := x) (D₁ := D₁) (D₂ := D₂) (A := A) (Ds := Ds) (K := K) (L := L))
    ipra_le sl dl with 3 * eg + (𝔞 (Syn.shift Ds) - 𝔞 (Syn.shift A)) * ef - 𝔞 (Syn.shift Ds) * ep +
      (3 * 𝔞 (dg (Syn.shift A) (Syn.shift Ds) (Pm x K L) (Qm x L)) + (𝔞 (Syn.shift Ds) - 𝔞 (Syn.shift A)) *
        (𝔞 (fact (Syn.shift L)) * 𝔞 (quo (Syn.shift x) (var 0))) - 𝔞 (Syn.shift Ds) * 𝔞 (Pm x K L)) * et

/-- Case 2: `A ΣQ + D ΣQ ≤ 3 Σg + D ΣP` on a block where `r ≥ −a/2`. -/
theorem case_hi_sum (h12 : Γ ⊢[PRAAx] le D₁ D₂)
    (hb : Γ ⊢[PRAAx] OnBlock x D₁ D₂ (stg x A Ds K L ⋏
      le (two * (Syn.shift Ds * monus (Qm x L) (Pm x K L))) (Syn.shift A * Qm x L))) :
    Γ ⊢[PRAAx] le (A * Bs' fzB x D₁ D₂ A Ds K L + Ds * Bs' fzB x D₁ D₂ A Ds K L)
      (num 3 * Bs' gzB x D₁ D₂ A Ds K L + Ds * Bs' pzB x D₁ D₂ A Ds K L) := by
  have h12' := LeanProofs.IPRA.Order.shift_le h12
  refine sum_le_two _ _ _ _ _ _ _ _ _ _ (.allI (.impI ?_))
  simp only [shift_pairT, shift_fact', show Syn.shift (num 3 : PTm n) = num 3 by simp [Syn.shift, PTm.subst_num]]
  refine tw_cases (d := var 0) h12'.wk _ ?_ ?_
  · have et := natEq (Prf.hyp0 : ((TW D₁ D₂ ≐ zero) :: Ctx x Γ) ⊢[PRAAx] _)
    have ef := natEq (term_f (Δ := (TW D₁ D₂ ≐ zero) :: Ctx x Γ) (x := x) (D₁ := D₁) (D₂ := D₂) (A := A) (Ds := Ds) (K := K) (L := L))
    have ep := natEq (term_p (Δ := (TW D₁ D₂ ≐ zero) :: Ctx x Γ) (x := x) (D₁ := D₁) (D₂ := D₂) (A := A) (Ds := Ds) (K := K) (L := L))
    have eg := natEq (term_g (Δ := (TW D₁ D₂ ≐ zero) :: Ctx x Γ) (x := x) (D₁ := D₁) (D₂ := D₂) (A := A) (Ds := Ds) (K := K) (L := L))
    ipra_le 0 with 3 * eg + 𝔞 (Syn.shift Ds) * ep - (𝔞 (Syn.shift A) + 𝔞 (Syn.shift Ds)) * ef +
      (3 * 𝔞 (dg (Syn.shift A) (Syn.shift Ds) (Pm x K L) (Qm x L)) + 𝔞 (Syn.shift Ds) * 𝔞 (Pm x K L) -
        (𝔞 (Syn.shift A) + 𝔞 (Syn.shift Ds)) * (𝔞 (fact (Syn.shift L)) * 𝔞 (quo (Syn.shift x) (var 0)))) * et
  · have hb' := on_block hb (ψ := TW D₁ D₂ ≐ one)
    have dh := def_hi (Prf.andE₁ hb') (Prf.andE₂ hb')
    have et := natEq (Prf.hyp0 : ((TW D₁ D₂ ≐ one) :: le (var 0) (Syn.shift D₂) ::
      lt (Syn.shift D₁) (var 0) :: Ctx x Γ) ⊢[PRAAx] _)
    have ef := natEq (term_f (Δ := (TW D₁ D₂ ≐ one) :: le (var 0) (Syn.shift D₂) :: lt (Syn.shift D₁) (var 0) :: Ctx x Γ)
      (x := x) (D₁ := D₁) (D₂ := D₂) (A := A) (Ds := Ds) (K := K) (L := L))
    have ep := natEq (term_p (Δ := (TW D₁ D₂ ≐ one) :: le (var 0) (Syn.shift D₂) :: lt (Syn.shift D₁) (var 0) :: Ctx x Γ)
      (x := x) (D₁ := D₁) (D₂ := D₂) (A := A) (Ds := Ds) (K := K) (L := L))
    have eg := natEq (term_g (Δ := (TW D₁ D₂ ≐ one) :: le (var 0) (Syn.shift D₂) :: lt (Syn.shift D₁) (var 0) :: Ctx x Γ)
      (x := x) (D₁ := D₁) (D₂ := D₂) (A := A) (Ds := Ds) (K := K) (L := L))
    ipra_le sl dh with 3 * eg + 𝔞 (Syn.shift Ds) * ep - (𝔞 (Syn.shift A) + 𝔞 (Syn.shift Ds)) * ef +
      (3 * 𝔞 (dg (Syn.shift A) (Syn.shift Ds) (Pm x K L) (Qm x L)) + 𝔞 (Syn.shift Ds) * 𝔞 (Pm x K L) -
        (𝔞 (Syn.shift A) + 𝔞 (Syn.shift Ds)) * (𝔞 (fact (Syn.shift L)) * 𝔞 (quo (Syn.shift x) (var 0)))) * et

/-- Case 3: `A ΣQ ≤ 2 Σg` on a block where `|r| ≤ a/2`. -/
theorem case_mid_sum (h12 : Γ ⊢[PRAAx] le D₁ D₂)
    (hb : Γ ⊢[PRAAx] OnBlock x D₁ D₂ (le (two * (Syn.shift Ds * absd (Pm x K L) (Qm x L))) (Syn.shift A * Qm x L))) :
    Γ ⊢[PRAAx] le (A * Bs' fzB x D₁ D₂ A Ds K L) (two * Bs' gzB x D₁ D₂ A Ds K L) := by
  have h12' := LeanProofs.IPRA.Order.shift_le h12
  refine sum_le_lin1 _ _ _ _ _ _ _ (.allI (.impI ?_))
  simp only [shift_pairT, shift_fact', show Syn.shift (two : PTm n) = two by simp [Syn.shift]]
  refine tw_cases (d := var 0) h12'.wk _ ?_ ?_
  · have et := natEq (Prf.hyp0 : ((TW D₁ D₂ ≐ zero) :: Ctx x Γ) ⊢[PRAAx] _)
    have ef := natEq (term_f (Δ := (TW D₁ D₂ ≐ zero) :: Ctx x Γ) (x := x) (D₁ := D₁) (D₂ := D₂) (A := A) (Ds := Ds) (K := K) (L := L))
    have eg := natEq (term_g (Δ := (TW D₁ D₂ ≐ zero) :: Ctx x Γ) (x := x) (D₁ := D₁) (D₂ := D₂) (A := A) (Ds := Ds) (K := K) (L := L))
    ipra_le 0 with 2 * eg - 𝔞 (Syn.shift A) * ef +
      (2 * 𝔞 (dg (Syn.shift A) (Syn.shift Ds) (Pm x K L) (Qm x L)) - 𝔞 (Syn.shift A) * (𝔞 (fact (Syn.shift L)) * 𝔞 (quo (Syn.shift x) (var 0)))) * et
  · have hb' := on_block hb (ψ := TW D₁ D₂ ≐ one)
    have dm := def_mid hb'
    have et := natEq (Prf.hyp0 : ((TW D₁ D₂ ≐ one) :: le (var 0) (Syn.shift D₂) ::
      lt (Syn.shift D₁) (var 0) :: Ctx x Γ) ⊢[PRAAx] _)
    have ef := natEq (term_f (Δ := (TW D₁ D₂ ≐ one) :: le (var 0) (Syn.shift D₂) :: lt (Syn.shift D₁) (var 0) :: Ctx x Γ)
      (x := x) (D₁ := D₁) (D₂ := D₂) (A := A) (Ds := Ds) (K := K) (L := L))
    have eg := natEq (term_g (Δ := (TW D₁ D₂ ≐ one) :: le (var 0) (Syn.shift D₂) :: lt (Syn.shift D₁) (var 0) :: Ctx x Γ)
      (x := x) (D₁ := D₁) (D₂ := D₂) (A := A) (Ds := Ds) (K := K) (L := L))
    ipra_le sl dm with 2 * eg - 𝔞 (Syn.shift A) * ef +
      (2 * 𝔞 (dg (Syn.shift A) (Syn.shift Ds) (Pm x K L) (Qm x L)) - 𝔞 (Syn.shift A) * (𝔞 (fact (Syn.shift L)) * 𝔞 (quo (Syn.shift x) (var 0)))) * et

end Cases

end LeanProofs.IPRA.AnalyticNumberTheory.BlockDeficit

export_ipra AnalyticNumberTheory.BlockDeficit (Bs' OnBlock bv_in gzB gz_at stg)
