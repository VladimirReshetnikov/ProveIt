import IPRADerivations.AnalyticNumberTheory.SymmetrySum

/-!
# Summed Möbius inversion for any body (`pnt_ipra_constructive_2026-11-14`, towards `sb:symmetry-bound`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `selberg.tex`, proof of Lemma `sb:symmetry`:
"`μ * f = 2L − 2c𝟏 + 4c²ε` … `Σ_{n≤x} (μ * f)(n) = 2P_1(x) − 2c⌊x⌋ + 4c²`". The comparison function splits into
nonnegative parts, each of the form `F = g * 𝟏`; for such parts the summed inversion is the same computation as
`SymmetrySum` with `L²` replaced by `g * 𝟏`. For every body `g(e, y)` with a parameter `y` and `B(m) = Σ_{1≤k≤m} (g * 𝟏)(k, y)`:

  `Σ_{1≤d≤x} μ⁺(d) B(⌊x/d⌋) = Σ_{1≤n≤x} g(n, y) + Σ_{1≤d≤x} μ⁻(d) B(⌊x/d⌋)`        (`mobius_summatory`).

* `inner_p`: `Σ_{e ≤ N} [e ∣ k] g(e) = (g * 𝟏)(k)` for `1 ≤ k ≤ N`;
* `row_mob_p`, `mob_p`: the pointwise inversion `Σ_{d∣N} μ⁺(d) (g*𝟏)(N/d) = g(N) + Σ_{d∣N} μ⁻(d) (g*𝟏)(N/d)`
  (`MobiusInversionP.mobius_inversion_p`);
* `row_pt`, `row_conv`, `pt_n`: as in `SymmetrySum`, each row is the convolution `(μ^± * (g * 𝟏))(N)`;
* `mobius_summatory`: summed over `n ≤ x` and reversed by `ConvSummatory.conv_summatory`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.MobiusSummatory

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusBounds (sum_ext shift_pos mu_bound congrMu)
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusInversion (eqb_rem_big)
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusInversionP (aP aN inst3_aP inst3_aN mobius_inversion_p)
open LeanProofs.IPRA.AnalyticNumberTheory.DirichletLeibniz (cvB conv cv_at)
open LeanProofs.IPRA.AnalyticNumberTheory.ConvolutionAssoc (cvF inst2_cvF)
open LeanProofs.IPRA.AnalyticNumberTheory.FactorialLambda (sum_add2)
open LeanProofs.IPRA.AnalyticNumberTheory.ConvSummatory (RB conv_summatory)
open LeanProofs.IPRA.AnalyticNumberTheory.SymmetrySum (aPB aNB inst2_aP inst2_aN row_alg row_zero)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (eq_of_dvd' pos_of_eq_mul)
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

section Summatory

variable (g : PTm 2)

/-- `g(e, snd Z)`. -/
def gZ : PTm 2 := Syn.subst ![var 0, sndT (var 1)] g

theorem inst2_gZ (e Z : PTm n) : inst2 (gZ g) e Z = inst2 g e (sndT Z) := by
  simp only [inst2, gZ, Syn.subst_subst]; congr 1; funext i; fin_cases i <;> simp

/-- `[e ∣ fst x] g(e, snd x)`. -/
abbrev EB : PTm 2 := (sg (var 0) * eqb (rem (fstT (var 1)) (var 0)) zero) * gZ g

theorem inst2_EB (e x : PTm n) :
    inst2 (EB g) e x = (sg e * eqb (rem (fstT x) e) zero) * inst2 g e (sndT x) := by
  have h : inst2 (EB g) e x = (sg e * eqb (rem (fstT x) e) zero) * inst2 (gZ g) e x := by simp [inst2]
  rw [h, inst2_gZ]

/-- `(g * 𝟏)(k, y)` as a body. -/
abbrev bF : PTm 2 := cvF g one

/-- `[d ∣ N] μ⁺_{N+1}(d) (g * 𝟏)(N/d)`, `N = fst Z`, `y = snd Z`. -/
abbrev QP : PTm 2 := ((sg (var 0) * eqb (rem (fstT (var 1)) (var 0)) zero) * muP (succ (fstT (var 1))) (var 0)) *
  ap2 (sumF (cvB g one)) (succ (quo (fstT (var 1)) (var 0))) (pairT (quo (fstT (var 1)) (var 0)) (sndT (var 1)))
abbrev QN : PTm 2 := ((sg (var 0) * eqb (rem (fstT (var 1)) (var 0)) zero) * muN (succ (fstT (var 1))) (var 0)) *
  ap2 (sumF (cvB g one)) (succ (quo (fstT (var 1)) (var 0))) (pairT (quo (fstT (var 1)) (var 0)) (sndT (var 1)))

theorem inst2_QP (d Z : PTm n) : inst2 (QP g) d Z =
    ((sg d * eqb (rem (fstT Z) d) zero) * muP (succ (fstT Z)) d) * conv g one (quo (fstT Z) d) (sndT Z) := by
  simp [inst2, subst_ap2]
theorem inst2_QN (d Z : PTm n) : inst2 (QN g) d Z =
    ((sg d * eqb (rem (fstT Z) d) zero) * muN (succ (fstT Z)) d) * conv g one (quo (fstT Z) d) (sndT Z) := by
  simp [inst2, subst_ap2]

/-- `Σ_{e ≤ N} [e ∣ k] g(e, y) = (g * 𝟏)(k, y)` for `1 ≤ k ≤ N`. -/
theorem inner_p {k N y : PTm n} (hk : Γ ⊢[PRAAx] k ≐ succ (pred k)) (hkN : Γ ⊢[PRAAx] le (succ k) (succ N)) :
    Γ ⊢[PRAAx] ap2 (sumF (EB g)) (succ N) (pairT k y) ≐ conv g one k y := by
  have hk' := shift_pos hk
  have cut : Γ ⊢[PRAAx] ap2 (sumF (EB g)) (succ N) (pairT k y) ≐ ap2 (sumF (EB g)) (succ k) (pairT k y) := by
    refine sum_ext (EB g) (fun Δ a hs hl => ?_) hkN
    rw [inst2_EB, shift_pairT]
    refine zero_mul_l ((congrMul (.eqRefl _) ((congrEqb' (congrAp2 remF (fst_pair _ _) (.eqRefl _)) (.eqRefl _)).eqTrans
      (eqb_rem_big (hk'.weaken hs) hl))).eqTrans (mul_zero _)) _
  refine cut.eqTrans (sum_congr_bounded (EB g) (cvB g one) (pairT k y) (pairT k y) (succ k) (.allI (.impI ?_)))
  rw [inst2_EB, shift_pairT]
  refine .eqTrans ?_ (cv_at _ _ _ _ _).eqSymm
  rw [show inst2 (one : PTm 2) (quo (Syn.shift k) (var 0)) (Syn.shift y) = one by simp [inst2]]
  refine (congrMul (congrMul (.eqRefl _) (congrEqb' (congrAp2 remF (fst_pair _ _) (.eqRefl _)) (.eqRefl _)))
    (congrInst2 g (.eqRefl _) (snd_pair _ _))).eqTrans ?_
  apply deriveNat; ipra_simps; ring

/-- A row of the inversion: `[d ∣ N] μ^±_{N+1}(d) Σ_{e ∣ N/d} g(e) = [d ∣ N] μ^±_{N+1}(d) (g * 𝟏)(N/d)`. -/
theorem row_mob_p {d Z : PTm n} (hN : Γ ⊢[PRAAx] fstT Z ≐ succ (pred (fstT Z))) :
    Γ ⊢[PRAAx] (inst2 (oB (aP (gZ g))) d (pairT (succ (fstT Z)) Z) ≐ inst2 (QP g) d Z) ⋏
      (inst2 (oB (aN (gZ g))) d (pairT (succ (fstT Z)) Z) ≐ inst2 (QN g) d Z) := by
  rw [inst2_oB, inst2_oB, inst2_QP, inst2_QN]
  have f₁ : Γ ⊢[PRAAx] fstT (pairT (succ (fstT Z)) Z) ≐ succ (fstT Z) := fst_pair _ _
  have s₁ : Γ ⊢[PRAAx] sndT (pairT (succ (fstT Z)) Z) ≐ Z := snd_pair _ _
  have cR := congrAp2 (sumF (rowB (aP (gZ g)))) f₁ (congrPairT (.eqRefl d) s₁)
  have cR' := congrAp2 (sumF (rowB (aN (gZ g)))) f₁ (congrPairT (.eqRefl d) s₁)
  have hcP : Syn.shift ((sg d * eqb (rem (fstT Z) d) zero) * muP (succ (fstT Z)) d) =
      (sg (Syn.shift d) * eqb (rem (fstT (Syn.shift Z)) (Syn.shift d)) zero) *
        muP (succ (fstT (Syn.shift Z))) (Syn.shift d) := by
    simp [Syn.shift]
  have hcN : Syn.shift ((sg d * eqb (rem (fstT Z) d) zero) * muN (succ (fstT Z)) d) =
      (sg (Syn.shift d) * eqb (rem (fstT (Syn.shift Z)) (Syn.shift d)) zero) *
        muN (succ (fstT (Syn.shift Z))) (Syn.shift d) := by
    simp [Syn.shift]
  have hq : Syn.shift (pairT (quo (fstT Z) d) (sndT Z)) =
      pairT (quo (fstT (Syn.shift Z)) (Syn.shift d)) (sndT (Syn.shift Z)) := by
    simp [Syn.shift]
  have epq : ∀ {Δ : List (Fm PTm (n + 1))} (e Z' d' : PTm (n + 1)),
      Δ ⊢[PRAAx] (sg e * eqb (rem (quo (fstT Z') d') e) zero) * inst2 (gZ g) e Z' ≐
        inst2 (EB g) e (pairT (quo (fstT Z') d') (sndT Z')) := fun e Z' d' => by
    rw [inst2_gZ, inst2_EB]
    exact congrMul (congrMul (.eqRefl _) (congrEqb' (congrAp2 remF (fst_pair _ _).eqSymm (.eqRefl _)) (.eqRefl _)))
      (congrInst2 g (.eqRefl _) (snd_pair _ _).eqSymm)
  have scP : Γ ⊢[PRAAx] ap2 (sumF (rowB (aP (gZ g)))) (succ (fstT Z)) (pairT d Z) ≐
      ((sg d * eqb (rem (fstT Z) d) zero) * muP (succ (fstT Z)) d) *
        ap2 (sumF (EB g)) (succ (fstT Z)) (pairT (quo (fstT Z) d) (sndT Z)) := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_rowB, shift_pairT, hcP, hq]
    refine (congrInst3 _ (fst_pair _ _) (.eqRefl _) (snd_pair _ _)).eqTrans ?_
    rw [inst3_aP]
    exact congrMul (.eqRefl _) (epq _ _ _)
  have scN : Γ ⊢[PRAAx] ap2 (sumF (rowB (aN (gZ g)))) (succ (fstT Z)) (pairT d Z) ≐
      ((sg d * eqb (rem (fstT Z) d) zero) * muN (succ (fstT Z)) d) *
        ap2 (sumF (EB g)) (succ (fstT Z)) (pairT (quo (fstT Z) d) (sndT Z)) := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_rowB, shift_pairT, hcN, hq]
    refine (congrInst3 _ (fst_pair _ _) (.eqRefl _) (snd_pair _ _)).eqTrans ?_
    rw [inst3_aN]
    exact congrMul (.eqRefl _) (epq _ _ _)
  have key : ∀ (X : PTm n), Γ ⊢[PRAAx] ((sg d * eqb (rem (fstT Z) d) zero) * X) *
      ap2 (sumF (EB g)) (succ (fstT Z)) (pairT (quo (fstT Z) d) (sndT Z)) ≐
      ((sg d * eqb (rem (fstT Z) d) zero) * X) * conv g one (quo (fstT Z) d) (sndT Z) := by
    intro X
    refine .orE (zero_or_succ d) ?_ ?_
    · have s0 : ((d ≐ zero) :: Γ) ⊢[PRAAx] sg d ≐ zero := (congrSg Prf.hyp0).eqTrans sg_zero
      exact (zero_mul_l (zero_mul_l (zero_mul_l s0 _) _) _).eqTrans (zero_mul_l (zero_mul_l (zero_mul_l s0 _) _) _).eqSymm
    · refine .orE (eq_or_ne (rem (fstT Z) d) zero) ?_ ?_
      · let C : List (Fm PTm n) := (rem (fstT Z) d ≐ zero) :: (d ≐ succ (pred d)) :: Γ
        have hd : C ⊢[PRAAx] d ≐ succ (pred d) := Prf.hyp1
        have eN := eq_of_dvd' hd (Prf.hyp0 : C ⊢[PRAAx] dvd d (fstT Z))
        have hk := pos_of_eq_mul hN.wk.wk eN
        have ww := natEq eN; have wp := natEq hd
        have hkN : C ⊢[PRAAx] le (succ (quo (fstT Z) d)) (succ (fstT Z)) := by
          refine (succ_monus_succ _ _).eqTrans (le_of_eq_add (d := pred d * quo (fstT Z) d) ?_)
          apply deriveNat; ipra_simps; linear_combination ww + 𝔞 (quo (fstT Z) d) * wp
        exact congrMul (.eqRefl _) (inner_p g hk hkN)
      · have z : (neg (rem (fstT Z) d ≐ zero) :: (d ≐ succ (pred d)) :: Γ) ⊢[PRAAx]
            sg d * eqb (rem (fstT Z) d) zero ≐ zero :=
          (congrMul (.eqRefl _) (eqb_of_ne Prf.hyp0)).eqTrans (by apply deriveNat; ipra_simps; ring)
        exact (zero_mul_l (zero_mul_l z _) _).eqTrans (zero_mul_l (zero_mul_l z _) _).eqSymm
  exact .andI (cR.eqTrans (scP.eqTrans (key _))) (cR'.eqTrans (scN.eqTrans (key _)))

/-- The pointwise inversion: `Σ_{d∣N} μ⁺(d) (g*𝟏)(N/d) = g(N) + Σ_{d∣N} μ⁻(d) (g*𝟏)(N/d)` for `N = fst Z ≥ 1`. -/
theorem mob_p {Z : PTm n} (hN : Γ ⊢[PRAAx] fstT Z ≐ succ (pred (fstT Z))) :
    Γ ⊢[PRAAx] ap2 (sumF (QP g)) (succ (fstT Z)) Z ≐
      inst2 g (fstT Z) (sndT Z) + ap2 (sumF (QN g)) (succ (fstT Z)) Z := by
  have inv := mobius_inversion_p (Γ := Γ) (gZ g) hN
  rw [inst2_gZ] at inv
  have hN' := shift_pos hN
  rw [show Syn.shift (fstT Z) = fstT (Syn.shift Z) by simp [Syn.shift]] at hN'
  have hs : Syn.shift (succ (fstT Z)) = succ (fstT (Syn.shift Z)) := by simp [Syn.shift]
  have cP : Γ ⊢[PRAAx] ap2 (sumF (oB (aP (gZ g)))) (succ (fstT Z)) (pairT (succ (fstT Z)) Z) ≐
      ap2 (sumF (QP g)) (succ (fstT Z)) Z := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_pairT, hs]
    exact Prf.andE₁ (row_mob_p g hN'.wk)
  have cN : Γ ⊢[PRAAx] ap2 (sumF (oB (aN (gZ g)))) (succ (fstT Z)) (pairT (succ (fstT Z)) Z) ≐
      ap2 (sumF (QN g)) (succ (fstT Z)) Z := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_pairT, hs]
    exact Prf.andE₂ (row_mob_p g hN'.wk)
  have a := natEq inv; have b := natEq cP; have c := natEq cN
  apply deriveNat; ipra_simps
  linear_combination -b + a + c

/-! ## The rows as convolutions, and the summed inversion -/

/-- The row algebra over opaque terms: `((S E') M') L' = (S E)(M L)` from `L' = L`, `M' = M`, `E' = E`. -/
theorem row_alg1 {S E E' M' Md L L' : PTm n} (eL : Γ ⊢[PRAAx] L' ≐ L) (eM : Γ ⊢[PRAAx] M' ≐ Md)
    (eE : Γ ⊢[PRAAx] E' ≐ E) : Γ ⊢[PRAAx] ((S * E') * M') * L' ≐ (S * E) * (Md * L) := by
  have a := natEq eL; have b := natEq eM; have c := natEq eE
  apply deriveNat; ipra_simps
  linear_combination 𝔞 S * 𝔞 E' * 𝔞 M' * a + 𝔞 S * 𝔞 E' * 𝔞 L * b + 𝔞 S * 𝔞 Md * 𝔞 L * c

/-- Both sides vanish when `S = 0`. -/
theorem row_zero1 {S E E' M' Md L L' : PTm n} (hS : Γ ⊢[PRAAx] S ≐ zero) :
    Γ ⊢[PRAAx] ((S * E') * M') * L' ≐ (S * E) * (Md * L) :=
  (zero_mul_l (zero_mul_l (zero_mul_l hS _) _) _).eqTrans (zero_mul_l (zero_mul_l hS _) _).eqSymm

theorem row_pt {d N y : PTm n} (hdN : Γ ⊢[PRAAx] le (succ d) (succ N)) :
    Γ ⊢[PRAAx] (inst2 (QP g) d (pairT N y) ≐ inst2 (cvB aPB (bF g)) d (pairT N y)) ⋏
      (inst2 (QN g) d (pairT N y) ≐ inst2 (cvB aNB (bF g)) d (pairT N y)) := by
  rw [inst2_QP, inst2_QN]
  simp only [DirichletLeibniz.inst2_cvB, inst2_aP, inst2_aN, inst2_cvF]
  have f₁ := fst_pair (Γ := Γ) N y
  have s₁ := snd_pair (Γ := Γ) N y
  have q : Γ ⊢[PRAAx] quo (fstT (pairT N y)) d ≐ quo N d := congrAp2 quoF f₁ (.eqRefl _)
  have cL : Γ ⊢[PRAAx] conv g one (quo (fstT (pairT N y)) d) (sndT (pairT N y)) ≐ conv g one (quo N d) y :=
    congrAp2 (sumF (cvB g one)) (congrSucc q) (congrPairT q s₁)
  have cM := congrMu (Γ := Γ) (d := d) (congrSucc f₁)
  have cE : Γ ⊢[PRAAx] eqb (rem (fstT (pairT N y)) d) zero ≐ eqb (rem N d) zero :=
    congrEqb' (congrAp2 remF f₁ (.eqRefl _)) (.eqRefl _)
  refine .orE (zero_or_succ d) ?_ ?_
  · have hS : ((d ≐ zero) :: Γ) ⊢[PRAAx] sg d ≐ zero := (congrSg Prf.hyp0).eqTrans sg_zero
    exact .andI ((row_zero1 hS).eqTrans (congrMul (congrMul (.eqRefl _) cE.wk.eqSymm) (congrMul (.eqRefl _) cL.wk.eqSymm)))
      ((row_zero1 hS).eqTrans (congrMul (congrMul (.eqRefl _) cE.wk.eqSymm) (congrMul (.eqRefl _) cL.wk.eqSymm)))
  · have mb := mu_bound (Γ := (d ≐ succ (pred d)) :: Γ) Prf.hyp0 hdN.wk
    exact .andI ((row_alg1 cL.wk ((Prf.andE₁ cM).wk.eqTrans (Prf.andE₁ mb)) cE.wk).eqTrans
        (congrMul (congrMul (.eqRefl _) cE.wk.eqSymm) (congrMul (.eqRefl _) cL.wk.eqSymm)))
      ((row_alg1 cL.wk ((Prf.andE₂ cM).wk.eqTrans (Prf.andE₂ mb)) cE.wk).eqTrans
        (congrMul (congrMul (.eqRefl _) cE.wk.eqSymm) (congrMul (.eqRefl _) cL.wk.eqSymm)))

theorem row_conv (N y : PTm n) :
    Γ ⊢[PRAAx] (ap2 (sumF (QP g)) (succ (fstT (pairT N y))) (pairT N y) ≐ conv aPB (bF g) N y) ⋏
      (ap2 (sumF (QN g)) (succ (fstT (pairT N y))) (pairT N y) ≐ conv aNB (bF g) N y) := by
  have rg := congrSucc (fst_pair (Γ := Γ) N y)
  have hs : Syn.shift (succ N) = succ (Syn.shift N) := by simp [Syn.shift]
  refine .andI ((congrAp2 _ rg (.eqRefl _)).eqTrans (sum_congr_bounded _ _ _ _ _ (.allI ?_)))
    ((congrAp2 _ rg (.eqRefl _)).eqTrans (sum_congr_bounded _ _ _ _ _ (.allI ?_)))
  · rw [hs]; refine .impI ?_; rw [shift_pairT]
    exact Prf.andE₁ (row_pt g (Prf.hyp0 : (lt (var 0) (succ (Syn.shift N)) :: Γ.map Fm.shift) ⊢[PRAAx] _))
  · rw [hs]; refine .impI ?_; rw [shift_pairT]
    exact Prf.andE₂ (row_pt g (Prf.hyp0 : (lt (var 0) (succ (Syn.shift N)) :: Γ.map Fm.shift) ⊢[PRAAx] _))

/-- `[n ≥ 1] g(n, y)`. -/
abbrev gS : PTm 2 := sg (var 0) * g

theorem inst2_gS (k y : PTm n) : inst2 (gS g) k y = sg k * inst2 g k y := by simp [inst2]

/-- `(μ⁺ * (g*𝟏))(N) = [N ≥ 1] g(N) + (μ⁻ * (g*𝟏))(N)` for every `N`. -/
theorem pt_n (N y : PTm n) :
    Γ ⊢[PRAAx] inst2 (cvF aPB (bF g)) N y ≐ inst2 (gS g) N y + inst2 (cvF aNB (bF g)) N y := by
  rw [inst2_cvF, inst2_cvF, inst2_gS]
  refine .orE (zero_or_succ N) ?_ ?_
  · let C : List (Fm PTm n) := (N ≐ zero) :: Γ
    have h0 : C ⊢[PRAAx] N ≐ zero := Prf.hyp0
    have cz : ∀ (a : PTm 2), C ⊢[PRAAx] conv a (bF g) N y ≐ zero := fun a => by
      refine (congrAp2 _ (congrSucc h0) (congrPairT h0 (.eqRefl _))).eqTrans ?_
      refine (sum_succ' _ _ _).eqTrans ((congrAdd (sum_zero _ _) (cv_at _ _ _ _ _)).eqTrans ?_)
      exact (congrAdd (.eqRefl _) (zero_mul_l (zero_mul_l sg_zero _) _)).eqTrans (add_zero _)
    have g0 : C ⊢[PRAAx] sg N * inst2 g N y ≐ zero := zero_mul_l ((congrSg h0).eqTrans sg_zero) _
    have a := natEq (cz aPB); have b := natEq (cz aNB); have c := natEq g0
    apply deriveNat; ipra_simps; linear_combination a - b - c
  · let C : List (Fm PTm n) := (N ≐ succ (pred N)) :: Γ
    have hN : C ⊢[PRAAx] fstT (pairT N y) ≐ succ (pred (fstT (pairT N y))) :=
      ConvolutionAssoc.pos_of_eq ((fst_pair _ _).eqTrans Prf.hyp0)
    have sm := mob_p (Γ := C) g hN
    have rc := row_conv (Γ := C) g N y
    have gx := congrInst2 (Γ := C) g (fst_pair N y) (snd_pair N y)
    have s1 : C ⊢[PRAAx] sg N ≐ one := (congrSg Prf.hyp0).eqTrans (sg_succ _)
    have e1 := natEq sm; have e2 := natEq (Prf.andE₁ rc); have e3 := natEq (Prf.andE₂ rc)
    have e4 := natEq gx; have e5 := natEq s1
    apply deriveNat; ipra_simps
    linear_combination -e2 + e1 + e3 + e4 - 𝔞 (inst2 g N y) * e5

/-- Summed Möbius inversion: `Σ_{1≤d≤x} μ⁺(d) B(⌊x/d⌋) = Σ_{1≤n≤x} g(n, y) + Σ_{1≤d≤x} μ⁻(d) B(⌊x/d⌋)`,
`B(m) = Σ_{1≤k≤m} (g * 𝟏)(k, y)`. -/
theorem mobius_summatory (x y : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (RB aPB (bF g))) (succ x) (pairT x y) ≐
      ap2 (sumF (gS g)) (succ x) y + ap2 (sumF (RB aNB (bF g))) (succ x) (pairT x y) := by
  have cP := conv_summatory (Γ := Γ) aPB (bF g) x y
  have cN := conv_summatory (Γ := Γ) aNB (bF g) x y
  have s := sum_add2 (Γ := Γ) (gS g) (cvF aNB (bF g)) (cvF aPB (bF g)) (K := succ x) (x := y) (x' := y) (z := y)
    (.allI (.impI (pt_n g _ _)))
  have e1 := natEq cP; have e2 := natEq cN; have e3 := natEq s
  apply deriveNat; ipra_simps; linear_combination -e1 + e3 + e2

end Summatory

end LeanProofs.IPRA.AnalyticNumberTheory.MobiusSummatory
