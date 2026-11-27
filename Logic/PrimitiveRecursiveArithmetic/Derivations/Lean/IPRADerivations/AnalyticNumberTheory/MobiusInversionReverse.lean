import IPRADerivations.AnalyticNumberTheory.MobiusFloor

/-!
# The reverse direction of Möbius inversion

Packet: `analytic-number-theory/mobius_ipra`, `arithmetic.tex`, "Two-sided inversion", the direction
`f = μ * F ⇒ F = f * 𝟏`; also `analytic-number-theory/mertens-ipra`, `foundations.tex`, `lem:cancel`, in the form
of a convolution identity at every argument.

The Möbius function is the pair `μ = μ⁺ − μ⁻` (`SymmetrySum.aPB`, `aNB`); `ε` is `SymmetryInstances.epsB`.

* `conv_congr1`, `conv_congr2`: the convolution respects schematic pointwise equations of either body;
* `conv_add_l`, `conv_add_r`: it distributes over the sum of bodies;
* `conv_unit`: `(ε * F)(N) = F(N)` for `N ≥ 1`;
* `pb_term`, `conv_PN`: `(μ^± * 𝟏)(M)` are the divisor sums `∑_{d ∣ M} μ^±(d)` of `Mobius.PB`, `Mobius.NB`
  (`MobiusBounds.mu_bound` moves the truncation of `μ`);
* `unit_pt`: `(μ⁺ * 𝟏)(i) = ε(i) + (μ⁻ * 𝟏)(i)` at **every** `i`, including `i = 0` and `i = 1`: the divisor
  cancellation `Mobius.mobius_cancel`, `mobius_one` as an identity of convolutions;
* **`mobius_reverse`**: for every body `F` and `N ≥ 1`,
  `(𝟏 * (μ⁺ * F))(N) = F(N) + (𝟏 * (μ⁻ * F))(N)`, by associativity (`ConvolutionAssoc.conv_assoc`):
  `𝟏 * (μ⁺ * F) = (𝟏 * μ⁺) * F = (ε + 𝟏 * μ⁻) * F = F + 𝟏 * (μ⁻ * F)`;
* **`inversion_reverse`**: if `(μ⁺ * F)(k) = f(k) + (μ⁻ * F)(k)` at every `k`, then `(𝟏 * f)(N) = F(N)` for
  `N ≥ 1`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.MobiusInversionReverse

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (muP muN congrSg zero_mul_l congrEqb' one_inst PB NB inst2_PB
  inst2_NB mobius_cancel mobius_one)
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusBounds (sum_ext mu_bound)
open LeanProofs.IPRA.AnalyticNumberTheory.DirichletLeibniz (cvB conv cv_at inst2_cvB)
open LeanProofs.IPRA.AnalyticNumberTheory.SymmetryInstances (epsB inst2_eps conv_zero)
open LeanProofs.IPRA.AnalyticNumberTheory.HyperbolaSwap (conv_congr_m conv_comm0)
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusFloor (mul_one1)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Congruence and distributivity -/

/-- The convolution respects a schematic pointwise equation of the first body. -/
theorem conv_congr1 (a a' b : PTm 2)
    (h : ∀ {m : ℕ} {Δ : List (Fm PTm m)} (i y : PTm m), Δ ⊢[PRAAx] inst2 a i y ≐ inst2 a' i y) (N y : PTm n) :
    Γ ⊢[PRAAx] conv a b N y ≐ conv a' b N y := by
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  rw [inst2_cvB, inst2_cvB]
  exact congrMul (.eqRefl _) (congrMul (h _ _) (.eqRefl _))

/-- The convolution respects a schematic pointwise equation of the second body. -/
theorem conv_congr2 (a b b' : PTm 2)
    (h : ∀ {m : ℕ} {Δ : List (Fm PTm m)} (i y : PTm m), Δ ⊢[PRAAx] inst2 b i y ≐ inst2 b' i y) (N y : PTm n) :
    Γ ⊢[PRAAx] conv a b N y ≐ conv a b' N y := by
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  rw [inst2_cvB, inst2_cvB]
  exact congrMul (.eqRefl _) (congrMul (.eqRefl _) (h _ _))

theorem dist_r (D A G H : PTm n) : Γ ⊢[PRAAx] D * (A * (G + H)) ≐ D * (A * G) + D * (A * H) := by
  ipra_ring

theorem dist_l (D A B G : PTm n) : Γ ⊢[PRAAx] D * ((A + B) * G) ≐ D * (A * G) + D * (B * G) := by
  ipra_ring

/-- `a * (g + h) = a * g + a * h`. -/
theorem conv_add_r (a g h : PTm 2) (N y : PTm n) :
    Γ ⊢[PRAAx] conv a (addBody g h) N y ≐ conv a g N y + conv a h N y := by
  refine sum_add2 (cvB a g) (cvB a h) (cvB a (addBody g h)) (.allI (.impI ?_))
  rw [inst2_cvB, inst2_cvB, inst2_cvB, inst2_addBody]
  exact dist_r _ _ _ _

/-- `(a + b) * g = a * g + b * g`. -/
theorem conv_add_l (a b g : PTm 2) (N y : PTm n) :
    Γ ⊢[PRAAx] conv (addBody a b) g N y ≐ conv a g N y + conv b g N y := by
  refine sum_add2 (cvB a g) (cvB b g) (cvB (addBody a b) g) (.allI (.impI ?_))
  rw [inst2_cvB, inst2_cvB, inst2_cvB, inst2_addBody]
  exact dist_l _ _ _ _

/-! ## The unit -/

theorem unit_term (F : PTm 2) (d N y : PTm n) : Γ ⊢[PRAAx] inst2 (cvB epsB F) d (pairT N y) ≐
    (sg d * eqb (rem N d) zero) * (eqb d one * inst2 F (quo N d) y) := by
  have h := cv_at (Γ := Γ) epsB F d N y
  rw [inst2_eps] at h
  exact h

theorem ones_alg (X : PTm n) : Γ ⊢[PRAAx] ((one : PTm n) * one) * (one * X) ≐ X := by
  ipra_ring

/-- `(ε * F)(N) = F(N)` for `N ≥ 1`. -/
theorem conv_unit (F : PTm 2) {N : PTm n} (hN : Γ ⊢[PRAAx] le one N) (y : PTm n) :
    Γ ⊢[PRAAx] conv epsB F N y ≐ inst2 F N y := by
  have ext := sum_ext (Γ := Γ) (cvB epsB F) (B := one) (N := succ N) (x := pairT N y) (fun Δ a hs ha => by
    rw [shift_pairT]
    have so : Syn.shift (one : PTm n) = one := by simp [Syn.shift]
    rw [so] at ha
    exact (unit_term F _ _ _).eqTrans ((congrMul (.eqRefl _)
      (zero_mul_l (eqb_zero_of_gt ha) _)).eqTrans (mul_zero _)))
    ((succ_monus_succ _ _).eqTrans hN)
  have s1 := sum_succ' (Γ := Γ) (cvB epsB F) one (pairT N y)
  have s0 := sum_succ' (Γ := Γ) (cvB epsB F) zero (pairT N y)
  have t0 : Γ ⊢[PRAAx] inst2 (cvB epsB F) zero (pairT N y) ≐ zero :=
    (unit_term F zero N y).eqTrans (zero_mul_l (zero_mul_l sg_zero _) _)
  have sg1 : Γ ⊢[PRAAx] sg (one : PTm n) ≐ one := sg_succ _
  have t1 : Γ ⊢[PRAAx] inst2 (cvB epsB F) one (pairT N y) ≐ inst2 F N y :=
    (unit_term F one N y).eqTrans ((congrMul (congrMul sg1 (eqb_of_eq (SymmetryInstances.rem_one N)))
      (congrMul (eqb_of_eq (.eqRefl one)) (congrInst2 F (RSA.quo_one N) (.eqRefl y)))).eqTrans (ones_alg _))
  have low : Γ ⊢[PRAAx] ap2 (sumF (cvB epsB F)) one (pairT N y) ≐ zero :=
    s0.eqTrans ((congrAdd (sum_zero _ _) t0).eqTrans (zero_add zero))
  exact ext.eqTrans (s1.eqTrans ((congrAdd low t1).eqTrans (zero_add _)))

/-! ## The divisor cancellation as an identity of convolutions -/

/-- The terms of `μ^± * 𝟏` are the terms of the divisor sums of `μ^±`. -/
theorem pb_term {d M : PTm n} (h : Γ ⊢[PRAAx] lt d (succ M)) (y : PTm n) :
    Γ ⊢[PRAAx] (inst2 (cvB aPB one) d (pairT M y) ≐ inst2 PB d M) ⋏
      (inst2 (cvB aNB one) d (pairT M y) ≐ inst2 NB d M) := by
  rw [inst2_PB, inst2_NB]
  have cP := cv_at (Γ := Γ) aPB one d M y
  have cN := cv_at (Γ := Γ) aNB one d M y
  rw [inst2_aP, one_inst] at cP
  rw [inst2_aN, one_inst] at cN
  refine .orE (zero_or_succ d) ?_ ?_
  · have z : ((d ≐ zero) :: Γ) ⊢[PRAAx] sg d ≐ zero := (congrSg Prf.hyp0).eqTrans sg_zero
    exact .andI
      (cP.wk.eqTrans ((zero_mul_l (zero_mul_l z _) _).eqTrans (zero_mul_l (zero_mul_l z _) _).eqSymm))
      (cN.wk.eqTrans ((zero_mul_l (zero_mul_l z _) _).eqTrans (zero_mul_l (zero_mul_l z _) _).eqSymm))
  · have mb := mu_bound (Γ := (d ≐ succ (pred d)) :: Γ) Prf.hyp0 h.wk
    exact .andI (cP.wk.eqTrans (congrMul (.eqRefl _) ((mul_one1 _).eqTrans (Prf.andE₁ mb).eqSymm)))
      (cN.wk.eqTrans (congrMul (.eqRefl _) ((mul_one1 _).eqTrans (Prf.andE₂ mb).eqSymm)))

/-- `(μ^± * 𝟏)(M) = ∑_{d ∣ M} μ^±(d)`. -/
theorem conv_PN (M y : PTm n) : Γ ⊢[PRAAx] (conv aPB one M y ≐ ap2 (sumF PB) (succ M) M) ⋏
    (conv aNB one M y ≐ ap2 (sumF NB) (succ M) M) := by
  have hs : Syn.shift (succ M) = succ (Syn.shift M) := by simp [Syn.shift]
  refine .andI (sum_congr_bounded _ _ _ _ _ (.allI ?_)) (sum_congr_bounded _ _ _ _ _ (.allI ?_))
  · rw [hs]; refine .impI ?_; rw [shift_pairT]
    exact Prf.andE₁ (pb_term (Prf.hyp0 : (lt (var 0) (succ (Syn.shift M)) :: Γ.map Fm.shift) ⊢[PRAAx] _) _)
  · rw [hs]; refine .impI ?_; rw [shift_pairT]
    exact Prf.andE₂ (pb_term (Prf.hyp0 : (lt (var 0) (succ (Syn.shift M)) :: Γ.map Fm.shift) ⊢[PRAAx] _) _)

theorem comb {A E B X Y Z : PTm n} (a : Γ ⊢[PRAAx] A ≐ X) (e : Γ ⊢[PRAAx] E ≐ Y) (b : Γ ⊢[PRAAx] B ≐ Z)
    (k : Γ ⊢[PRAAx] X ≐ Y + Z) : Γ ⊢[PRAAx] A ≐ E + B := by
  ipra_lc natEq a - natEq e - natEq b + natEq k

theorem two_le_of {i p q : PTm n} (a : Γ ⊢[PRAAx] i ≐ succ p) (b : Γ ⊢[PRAAx] p ≐ succ q) :
    Γ ⊢[PRAAx] le two i := by
  have a1 := natEq a; have b1 := natEq b
  refine le_of_eq_add (d := q) ?_
  ipra_lc a1 + b1

/-- `(μ⁺ * 𝟏)(i) = ε(i) + (μ⁻ * 𝟏)(i)` at every `i`. -/
theorem unit_pt (i y : PTm n) : Γ ⊢[PRAAx] conv aPB one i y ≐ eqb i one + conv aNB one i y := by
  refine .orE (zero_or_succ i) ?_ ?_
  · let C : List (Fm PTm n) := (i ≐ zero) :: Γ
    have h0 : C ⊢[PRAAx] i ≐ zero := Prf.hyp0
    have z1 : C ⊢[PRAAx] lt zero one := le_refl one
    have ze : C ⊢[PRAAx] eqb i one ≐ zero := (congrEqb' h0 (.eqRefl _)).eqTrans (eqb_zero_of_lt z1)
    exact comb ((conv_congr_m aPB one y h0).eqTrans (conv_zero aPB one y)) ze
      ((conv_congr_m aNB one y h0).eqTrans (conv_zero aNB one y)) (zero_add zero).eqSymm
  · refine .orE (zero_or_succ (pred i)) ?_ ?_
    · let C : List (Fm PTm n) := (pred i ≐ zero) :: (i ≐ succ (pred i)) :: Γ
      have hi : C ⊢[PRAAx] i ≐ succ (pred i) := Prf.hyp1
      have hp : C ⊢[PRAAx] pred i ≐ zero := Prf.hyp0
      have i1 : C ⊢[PRAAx] i ≐ one := hi.eqTrans (congrSucc hp)
      have m1 := mobius_one (Γ := C)
      have cP := conv_PN (Γ := C) one y
      exact comb ((conv_congr_m aPB one y i1).eqTrans ((Prf.andE₁ cP).eqTrans (Prf.andE₁ m1)))
        (eqb_of_eq i1) ((conv_congr_m aNB one y i1).eqTrans ((Prf.andE₂ cP).eqTrans (Prf.andE₂ m1)))
        (add_zero one).eqSymm
    · let C : List (Fm PTm n) := (pred i ≐ succ (pred (pred i))) :: (i ≐ succ (pred i)) :: Γ
      have hi : C ⊢[PRAAx] i ≐ succ (pred i) := Prf.hyp1
      have hp : C ⊢[PRAAx] pred i ≐ succ (pred (pred i)) := Prf.hyp0
      have h2 : C ⊢[PRAAx] le two i := two_le_of hi hp
      have g1 : C ⊢[PRAAx] lt one i := h2
      have cP := conv_PN (Γ := C) i y
      have ze : C ⊢[PRAAx] eqb i one ≐ zero := eqb_zero_of_gt g1
      exact comb (Prf.andE₁ cP) ze (Prf.andE₂ cP) ((mobius_cancel h2).eqTrans (zero_add _).eqSymm)

/-- The same identity for the bodies `𝟏 * μ^±`, at every argument and in every context. -/
theorem unit_body {m : ℕ} {Δ : List (Fm PTm m)} (i y : PTm m) :
    Δ ⊢[PRAAx] inst2 (cvF one aPB) i y ≐ inst2 (addBody epsB (cvF one aNB)) i y := by
  rw [inst2_cvF, inst2_addBody, inst2_eps, inst2_cvF]
  exact (conv_comm0 one aPB i y).eqTrans ((unit_pt i y).eqTrans (congrAdd (.eqRefl _) (conv_comm0 aNB one i y)))

/-! ## The reverse inversion -/

/-- **Reverse Möbius inversion**: `(𝟏 * (μ⁺ * F))(N) = F(N) + (𝟏 * (μ⁻ * F))(N)` for `N ≥ 1`. -/
theorem mobius_reverse (F : PTm 2) {N : PTm n} (hN : Γ ⊢[PRAAx] le one N) (y : PTm n) :
    Γ ⊢[PRAAx] conv one (cvF aPB F) N y ≐ inst2 F N y + conv one (cvF aNB F) N y :=
  (conv_assoc one aPB F N y).eqTrans ((conv_congr1 _ _ F unit_body N y).eqTrans
    ((conv_add_l epsB (cvF one aNB) F N y).eqTrans
      (congrAdd (conv_unit F hN y) (conv_assoc one aNB F N y).eqSymm)))

theorem cancel_alg {L G R X : PTm n} (e1 : Γ ⊢[PRAAx] L ≐ G + R) (e2 : Γ ⊢[PRAAx] L ≐ X + R) :
    Γ ⊢[PRAAx] G ≐ X := by
  ipra_lc natEq e2 - natEq e1

/-- **Two-sided inversion**, the reverse direction: if `(μ⁺ * F)(k) = f(k) + (μ⁻ * F)(k)` at every `k`, then
`(𝟏 * f)(N) = F(N)` for `N ≥ 1`. -/
theorem inversion_reverse (f F : PTm 2)
    (H : ∀ {m : ℕ} {Δ : List (Fm PTm m)} (k y : PTm m),
      Δ ⊢[PRAAx] conv aPB F k y ≐ inst2 f k y + conv aNB F k y)
    {N : PTm n} (hN : Γ ⊢[PRAAx] le one N) (y : PTm n) :
    Γ ⊢[PRAAx] conv one f N y ≐ inst2 F N y := by
  have e1 : Γ ⊢[PRAAx] conv one (cvF aPB F) N y ≐ conv one f N y + conv one (cvF aNB F) N y :=
    (conv_congr2 one (cvF aPB F) (addBody f (cvF aNB F))
      (fun i y => by rw [inst2_cvF, inst2_addBody, inst2_cvF]; exact H i y) N y).eqTrans
      (conv_add_r one f (cvF aNB F) N y)
  exact cancel_alg e1 (mobius_reverse F hN y)

end LeanProofs.IPRA.AnalyticNumberTheory.MobiusInversionReverse
