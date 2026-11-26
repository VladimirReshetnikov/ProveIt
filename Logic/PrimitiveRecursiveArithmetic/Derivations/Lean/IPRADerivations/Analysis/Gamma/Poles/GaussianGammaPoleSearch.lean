import IPRADerivations.Analysis.Gamma.Poles.GaussianGammaPoleZeros
import IPRADerivations.Analysis.Gamma.FunctionalEquations.ReciprocalGamma.GaussianGammaReciprocalInverse

/-!
# Exact pole search for rational reciprocal Gamma inputs

For a rational input with positive numerical denominator, each nonzero
translated numerator has squared norm at least one. The actual bounded
search therefore either returns an exact pole index or supplies the
original `δ=1/B` separation. In the second case the actual reciprocal
anchor contradicts the existing iPRA zero predicate for the C7 program.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaPoleSearch

open_ipra
open GaussianGammaEulerHeadLower (translated poleGuard poleAt)
open GaussianGeneralPolynomialValueName (programZero program_zero_at)
open GaussianGammaCanonicalExponent (source)
open GaussianRootAlgebra (equal equal_of_values re_zero im_zero)
open ComplexLogarithmRemainder (normSq zeroCode)
open GaussianRationalMetric (bounded bounded_to_cleared)
open GaussianRationalHorner (positive_product qzero)
open GaussianRationalL1 (rawDen rawGaussian raw_represents raw_den_positive)
open GaussianCoefficientNameBounds (unit unit_positive)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def testBody : PTm 3 := normSq (translated (var 1) (var 2) (var 0))
def search (z B N : PTm n) : PTm n := Search.Finite.mu testBody (succ N) ![z,B]
def hit (z B N : PTm n) : Fm PTm n :=
  le (search z B N) N ⋏ equal (translated z B (search z B N)) zeroCode

ipra_subst search [Search.Finite.subst_mu, ConciseIPRA.PTm.subst_succ]

theorem test_at (z B k : PTm n) :
    Search.Finite.applyBody testBody k ![z,B] = normSq (translated z B k) := by
  simp [Search.Finite.applyBody,testBody]

theorem norm_zero_at_pole (z B k : PTm n) (h : Γ ⊢[PRAAx] normSq (translated z B k) ≐ zero) :
    Γ ⊢[PRAAx] equal (translated z B k) zeroCode := by
  have v := GaussianProductNorm.norm_zero_values _ h
  exact equal_of_values (v.1.trans re_zero.symm) (v.2.trans im_zero.symm)

theorem returned_hit (z B N : PTm n) (h : Γ ⊢[PRAAx] lt (search z B N) (succ N)) :
    Γ ⊢[PRAAx] hit z B N := by
  have spec := Search.Finite.search_spec (Γ := Γ) testBody (succ N) (search z B N) ![z,B]
  have v := Prf.impE spec.andE₂.andE₁ h
  rw [test_at] at v
  exact .andI ((succ_monus_succ _ _).eqSymm.eqTrans h) (norm_zero_at_pole _ _ _ v)

theorem failed_at (z B N k : PTm n) (h : Γ ⊢[PRAAx] search z B N ≐ succ N) (hk : Γ ⊢[PRAAx] le k N) :
    Γ ⊢[PRAAx] poleAt z B one B k := by
  have spec := Search.Finite.search_spec (Γ := Γ) testBody (succ N) k ![z,B]
  have hlt : Γ ⊢[PRAAx] lt k (search z B N) :=
    lt_congr (.eqRefl _) h.eqSymm ((succ_monus_succ _ _).eqTrans hk)
  have v := Prf.impE spec.andE₂.andE₂ hlt
  rw [test_at] at v
  exact le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono (le_refl (B*B)) (Foundations.BoundedReflection.compl_of_ne v))

theorem failed_guard (z B N : PTm n) (h : Γ ⊢[PRAAx] search z B N ≐ succ N) :
    Γ ⊢[PRAAx] poleGuard z B one B N := by
  refine .allI (.impI ?_)
  let z' := Syn.shift z
  let b := Syn.shift B
  let m := Syn.shift N
  have hs : Γ.map Fm.shift ⊢[PRAAx] search z' b m ≐ succ m := by
    simpa [Fm.shift,Syn.shift,z',b,m] using h.shift
  simpa only [poleGuard,Syn.shift,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,z',b,m] using failed_at z' b m (var 0) hs.wk Prf.hyp0

theorem apart_excludes_zero (f : PR 2) (x h : PTm n) (ha : Γ ⊢[PRAAx] GaussianNameReciprocal.apart f h x)
    (hz : Γ ⊢[PRAAx] programZero f x) : Γ ⊢[PRAAx] .bot := by
  let p := GaussianNameReciprocal.anchor h
  let q := ap2 f p x
  let U := unit h
  let D := rawDen q
  let S := normSq (rawGaussian q)
  let W := U*U*S
  have hp : Γ ⊢[PRAAx] unit p ≐ unit h*(num 4) :=
    (pw_add two h two).eqTrans (congrMul (.eqRefl _) ((pw_succ two one).eqTrans
      ((congrMul (pw_one two) (.eqRefl _)).eqTrans (by ipra_ring))))
  have lower : Γ ⊢[PRAAx] le (D*D) W := GaussianNameReciprocal.lower_cleared q U (unit_positive h) ha
  have upper := bounded_to_cleared q (rawGaussian q) D one (unit p) (raw_den_positive q) (unit_positive p)
    (raw_represents q) (program_zero_at f x p hz)
  have hU : Γ ⊢[PRAAx] le ((num 16)*W) (D*D) := by
    have e := natEq hp
    exact le_congr (by
      unfold W U
      apply deriveNat
      ipra_simps
      rw [e]
      ring) (by ipra_ring) upper
  have pos : Γ ⊢[PRAAx] le one W :=
    le_trans (positive_product _ _ (raw_den_positive q) (raw_den_positive q)) lower
  have strict : Γ ⊢[PRAAx] lt W ((num 16)*W) := by
    change Γ ⊢[PRAAx] le (succ W) ((num 16)*W)
    ipra_le 15*sl pos+14
  exact le_lt_absurd _ (le_trans hU lower) strict

theorem zero_returns_pole (z R B : PTm n) (hs : Γ ⊢[PRAAx] source z R B)
    (hz : Γ ⊢[PRAAx] programZero GaussianGammaC7Name.nameF (GaussianGammaC7Name.data z R B)) :
    Γ ⊢[PRAAx] hit z B (two*R) := by
  have spec := Search.Finite.search_spec (Γ := Γ) testBody (succ (two*R)) zero ![z,B]
  refine .orE (lt_or_eq_of_le spec.andE₁) (returned_hit z B (two*R) Prf.hyp0) ?_
  let C := (search z B (two*R) ≐ succ (two*R)) :: Γ
  have h : C ⊢[PRAAx] poleGuard z B one B (two*R) := failed_guard z B (two*R) Prf.hyp0
  have src : C ⊢[PRAAx] GaussianGammaReciprocalInverse.source z R B one B :=
    .andI hs.wk (.andI (le_refl _) (.andI (hs.andE₂.andE₁).wk h))
  have ap := (GaussianGammaReciprocalInverse.original_gamma_inverse z R B one B src).andE₁.andE₂
  exact .botE _ (apart_excludes_zero _ _ _ ap hz.wk)

theorem returned_pole_gives_zero (z R B : PTm n) (hB : Γ ⊢[PRAAx] le one B) (h : Γ ⊢[PRAAx] hit z B (two*R)) :
    Γ ⊢[PRAAx] programZero GaussianGammaC7Name.nameF (GaussianGammaC7Name.data z R B) := by
  refine .allI ?_
  let z' := Syn.shift z
  let r := Syn.shift R
  let b := Syn.shift B
  let C := Γ.map Fm.shift
  let p : PTm (n+1) := var 0
  have pos : C ⊢[PRAAx] le one b := by simpa [Fm.shift,Syn.shift,b] using hB.shift
  have found : C ⊢[PRAAx] hit z' b (two*r) := by
    simpa [Fm.shift,Syn.shift,hit,z',r,b] using h.shift
  have eq := GaussianGammaPoleZeros.C7_sample_zero_at_pole p z' r b (search z' b (two*r)) pos found.andE₁ found.andE₂
  have zbd : C ⊢[PRAAx] bounded qzero one (unit p) := by
    apply (GaussianRationalMetric.bounded_iff _ zeroCode one one _ (le_refl _) (unit_positive p)
      (GaussianRationalHorner.zero_represents one)).iffMpr
    exact le_congr (by
      have e := natEq (ComplexLogarithmRemainder.normSq_zero (Γ := C) (n := n+1))
      apply deriveNat
      ipra_simps
      rw [e]
      ring) (.eqRefl _) (zero_le _)
  simpa only [programZero,GaussianGammaC7Name.sample,Syn.shift,GaussianGammaC7Name.subst_data,z',r,b,C,p] using
    GaussianRationalReciprocal.bound_congr eq.eqSymm (.eqRefl _) (.eqRefl _) zbd

theorem rational_zero_iff_pole (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    Fm.iff (programZero GaussianGammaC7Name.nameF (GaussianGammaC7Name.data z R B)) (hit z B (two*R)) :=
  .iffI (.impI (zero_returns_pole z R B h.wk Prf.hyp0))
    (.impI (returned_pole_gives_zero z R B (h.andE₂.andE₁).wk Prf.hyp0))

theorem original_rational_pole_search_sound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (search (var 0) (var 1) (var 2)) (succ (var 2)) ⟶ hit (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (returned_hit _ _ _ Prf.hyp0))

theorem original_rational_pole_search_guard_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (search (var 0) (var 1) (var 2) ≐ succ (var 2) ⟶ poleGuard (var 0) (var 1) one (var 1) (var 2)) :=
  closeUniv 3 (.impI (failed_guard _ _ _ Prf.hyp0))

theorem original_rational_C7_zero_returns_pole_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 1) (var 2) ⟶ programZero GaussianGammaC7Name.nameF
        (GaussianGammaC7Name.data (var 0) (var 1) (var 2)) ⟶ hit (var 0) (var 2) (two*var 1)) :=
  closeUniv 3 (.impI (.impI (zero_returns_pole _ _ _ Prf.hyp1 Prf.hyp0)))

theorem original_rational_C7_zero_iff_pole_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 1) (var 2) ⟶ Fm.iff
      (programZero GaussianGammaC7Name.nameF (GaussianGammaC7Name.data (var 0) (var 1) (var 2)))
      (hit (var 0) (var 2) (two*var 1))) :=
  closeUniv 3 (.impI (rational_zero_iff_pole _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaPoleSearch
