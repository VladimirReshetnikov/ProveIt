import IPRADerivations.Analysis.Names.Aggregation.AggregateChain
import IPRADerivations.Core.OrderCertificates

/-!
# Independent-denominator scalar rational error budgets

Finite-demand Section 3, numerical prerequisites for optimization.  Inputs
are actual signed rational codes, with predecessor-denominator storage.
`upper a b A B` is the cleared inequality `a ≤ b + A/B`; `radius` is the
two-sided version.  Every cancelled denominator is the positive denominator
decoded from an input code, or an explicitly positive error denominator.
There are no assumptions about common denominators or signs of values.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.RationalValueBounds

open_ipra
open LeanProofs.IPRA.Analysis.RationalSupMetric
open LeanProofs.IPRA.Foundations.GapDecision
open LeanProofs.IPRA.Probability.Variance (ad)
open LeanProofs.IPRA.Probability.MedianWeighted (ad_le_of ad_mul le_add_ad)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def crossLeft (a b : PTm n) : PTm n :=
  (numeratorOf a).pos * denominatorOf b + (numeratorOf b).neg * denominatorOf a

def cross (a b : PTm n) : ZT n :=
  numeratorOf a * ZT.ofNat (denominatorOf b) - numeratorOf b * ZT.ofNat (denominatorOf a)

def upper (a b A B : PTm n) : Fm PTm n :=
  le (B * crossLeft a b) (B * crossLeft b a + A * denominatorOf a * denominatorOf b)

def radius (a b A B : PTm n) : Fm PTm n :=
  le (B * zabs (cross a b)) (A * denominatorOf a * denominatorOf b)

ipra_subst crossLeft [numeratorOf, ZT.subst]

ipra_subst cross

ipra_subst upper

@[simp] theorem subst_radius {m : ℕ} (σ : Fin n → PTm m) (a b A B : PTm n) :
    (radius a b A B).subst σ = radius (Syn.subst σ a) (Syn.subst σ b)
      (Syn.subst σ A) (Syn.subst σ B) := by
  simp only [radius, subst_le, PTm.subst_mul, subst_zabs, subst_cross, subst_denominatorOf]

theorem denominator_positive (a : PTm n) : Γ ⊢[PRAAx] le one (denominatorOf a) := by
  exact (succ_monus_succ zero _).eqTrans (zero_le _)

alias positive_cancel := Common.mul_cancel_le

theorem cross_absolute (a b : PTm n) :
    Γ ⊢[PRAAx] zabs (cross a b) ≐ ad (crossLeft a b) (crossLeft b a) := by
  apply zabs_congr (v := ⟨crossLeft a b, crossLeft b a⟩)
  change ZT.toZ Γ (numeratorOf a * ZT.ofNat (denominatorOf b) -
    numeratorOf b * ZT.ofNat (denominatorOf a)) = _
  rw [ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_mul, ZT.toZ_ofNat, ZT.toZ_ofNat]
  simp only [crossLeft, ZT.toZ, Q.mk_add, Q.mk_mul, map_add, map_mul]
  ring

theorem upper_of_radius (a b A B : PTm n) (h : Γ ⊢[PRAAx] radius a b A B) :
    Γ ⊢[PRAAx] upper a b A B := by
  have h' := le_congr (congrMul (.eqRefl _) (cross_absolute a b)) (.eqRefl _) h
  have first : Γ ⊢[PRAAx] le (B*crossLeft a b)
      (B*crossLeft b a+B*ad (crossLeft a b) (crossLeft b a)) :=
    le_congr (by ipra_ring) (by ipra_ring)
      (mul_le_mul_right B (le_add_ad (crossLeft a b) (crossLeft b a)))
  exact le_trans first (le_congr (by ipra_ring) (by ipra_ring)
    (add_le_add_right (B*crossLeft b a) h'))

theorem radius_symmetric (a b A B : PTm n) (h : Γ ⊢[PRAAx] radius a b A B) :
    Γ ⊢[PRAAx] radius b a A B := by
  have e : Γ ⊢[PRAAx] zabs (cross b a) ≐ zabs (cross a b) :=
    (zabs_congr (v := -(cross a b)) (by
      simp only [cross, ZT.toZ_sub, ZT.toZ_neg]
      ring)).eqTrans (zabs_neg _)
  exact le_congr (congrMul (.eqRefl _) e).eqSymm (by ipra_ring) h

theorem radius_of_upper (a b A B : PTm n) (hab : Γ ⊢[PRAAx] upper a b A B)
    (hba : Γ ⊢[PRAAx] upper b a A B) : Γ ⊢[PRAAx] radius a b A B := by
  have bounded : Γ ⊢[PRAAx] le (ad (B*crossLeft a b) (B*crossLeft b a))
      (A*denominatorOf a*denominatorOf b) :=
    ad_le_of hab (le_congr (.eqRefl _) (by ipra_ring) hba)
  exact le_congr ((congrMul (.eqRefl _) (cross_absolute a b)).eqTrans
    (ad_mul B (crossLeft a b) (crossLeft b a)).eqSymm).eqSymm (.eqRefl _) bounded

theorem upper_congr {a a' b b' A A' B B' : PTm n}
    (ha : Γ ⊢[PRAAx] a ≐ a') (hb : Γ ⊢[PRAAx] b ≐ b')
    (hA : Γ ⊢[PRAAx] A ≐ A') (hB : Γ ⊢[PRAAx] B ≐ B')
    (h : Γ ⊢[PRAAx] upper a b A B) : Γ ⊢[PRAAx] upper a' b' A' B' := by
  have p := Prf.eqSubst (upper (var 0) (var 1) (var 2) (var 3) : Fm PTm 4)
    (σ := ![a,b,A,B]) (σ' := ![a',b',A',B']) (fun i => by fin_cases i <;> assumption)
    (by simpa [subst_upper] using h)
  simpa [subst_upper] using p

theorem radius_congr {a a' b b' A A' B B' : PTm n}
    (ha : Γ ⊢[PRAAx] a ≐ a') (hb : Γ ⊢[PRAAx] b ≐ b')
    (hA : Γ ⊢[PRAAx] A ≐ A') (hB : Γ ⊢[PRAAx] B ≐ B')
    (h : Γ ⊢[PRAAx] radius a b A B) : Γ ⊢[PRAAx] radius a' b' A' B' := by
  have p := Prf.eqSubst (radius (var 0) (var 1) (var 2) (var 3) : Fm PTm 4)
    (σ := ![a,b,A,B]) (σ' := ![a',b',A',B']) (fun i => by fin_cases i <;> assumption)
    (by simpa [subst_radius] using h)
  simpa [subst_radius] using p

/-- Exact addition of independent rational error budgets. -/
theorem upper_triangle (a b c A B C D : PTm n)
    (hab : Γ ⊢[PRAAx] upper a b A B) (hbc : Γ ⊢[PRAAx] upper b c C D) :
    Γ ⊢[PRAAx] upper a c (A*D+C*B) (B*D) := by
  apply positive_cancel (denominator_positive b)
  ipra_le (Groth.ι (Q.mk Γ D) * Groth.ι (Q.mk Γ (denominatorOf c))) * sl hab +
    (Groth.ι (Q.mk Γ B) * Groth.ι (Q.mk Γ (denominatorOf a))) * sl hbc using
      unfold crossLeft
      ipra_simps
      ring


theorem upper_of_order (a b A B : PTm n)
    (h : Γ ⊢[PRAAx] le (crossLeft a b) (crossLeft b a)) :
    Γ ⊢[PRAAx] upper a b A B := by
  exact le_trans (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right B h))
    (le_add_right _ _)

/-- A zero upper budget at a positive denominator gives exact order. -/
theorem order_of_upper_zero {a b B : PTm n} (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] upper a b zero B) : Γ ⊢[PRAAx] le (crossLeft a b) (crossLeft b a) :=
  positive_cancel hB (le_congr (.eqRefl _) (by ipra_ring) h)

theorem upper_mono (a b A B C D : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] upper a b A B) (hAD : Γ ⊢[PRAAx] le (A*D) (C*B)) :
    Γ ⊢[PRAAx] upper a b C D := by
  apply positive_cancel hB
  ipra_le Groth.ι (Q.mk Γ D) * sl h +
    (Groth.ι (Q.mk Γ (denominatorOf a)) * Groth.ι (Q.mk Γ (denominatorOf b))) * sl hAD


theorem radius_mono (a b A B C D : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] radius a b A B) (hAD : Γ ⊢[PRAAx] le (A*D) (C*B)) :
    Γ ⊢[PRAAx] radius a b C D := by
  apply positive_cancel hB
  ipra_le Groth.ι (Q.mk Γ D) * sl h +
    (Groth.ι (Q.mk Γ (denominatorOf a)) * Groth.ι (Q.mk Γ (denominatorOf b))) * sl hAD


theorem radius_triangle (a b c A B C D : PTm n)
    (hab : Γ ⊢[PRAAx] radius a b A B) (hbc : Γ ⊢[PRAAx] radius b c C D) :
    Γ ⊢[PRAAx] radius a c (A*D+C*B) (B*D) :=
  radius_of_upper a c _ _
    (upper_triangle a b c A B C D (upper_of_radius a b A B hab) (upper_of_radius b c C D hbc))
    (upper_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (by ipra_ring)
      (upper_triangle c b a C D A B (upper_of_radius c b C D (radius_symmetric b c C D hbc))
        (upper_of_radius b a A B (radius_symmetric a b A B hab))))

theorem upper_order_left (a b c A B : PTm n)
    (hab : Γ ⊢[PRAAx] le (crossLeft a b) (crossLeft b a))
    (hbc : Γ ⊢[PRAAx] upper b c A B) : Γ ⊢[PRAAx] upper a c A B :=
  upper_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (by ipra_ring)
    (upper_triangle a b c zero one A B (upper_of_order a b zero one hab) hbc)

theorem upper_order_right (a b c A B : PTm n)
    (hab : Γ ⊢[PRAAx] upper a b A B)
    (hbc : Γ ⊢[PRAAx] le (crossLeft b c) (crossLeft c b)) : Γ ⊢[PRAAx] upper a c A B :=
  upper_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (by ipra_ring)
    (upper_triangle a b c A B zero one hab (upper_of_order b c zero one hbc))

theorem radius_diagonal (a A B : PTm n) : Γ ⊢[PRAAx] radius a a A B :=
  radius_of_upper a a A B (upper_of_order a a A B (le_refl _))
    (upper_of_order a a A B (le_refl _))

theorem upper_cancel (a b A B c : PTm n) (hc : Γ ⊢[PRAAx] le one c)
    (h : Γ ⊢[PRAAx] upper a b (c*A) (c*B)) : Γ ⊢[PRAAx] upper a b A B :=
  positive_cancel hc (le_congr (by ipra_ring) (by ipra_ring) h)

/-- Normalize two unit errors observed at a common positive denominator. -/
theorem upper_two_errors_same {a b D : PTm n} (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] upper a b (D+D) (D*D)) : Γ ⊢[PRAAx] upper a b two D :=
  upper_cancel a b two D D hD
    (upper_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _) h)

/-- Lower either observation denominator while keeping the two error allowances. -/
theorem upper_two_errors_retime {a b B C D E : PTm n} (hBC : Γ ⊢[PRAAx] le one (B*C))
    (hDB : Γ ⊢[PRAAx] le D B) (hEC : Γ ⊢[PRAAx] le E C)
    (h : Γ ⊢[PRAAx] upper a b (B+C) (B*C)) : Γ ⊢[PRAAx] upper a b (D+E) (D*E) :=
  upper_mono _ _ _ _ _ _ hBC h (le_congr (by ipra_ring) (by ipra_ring)
    (add_le_add₂ (mul_le_mul_right (B*D) hEC) (mul_le_mul_right (C*E) hDB)))

/-- Bound two observations by twice the error at a common earlier denominator. -/
theorem upper_two_errors {a b B C D : PTm n} (hBC : Γ ⊢[PRAAx] le one (B*C))
    (hD : Γ ⊢[PRAAx] le one D) (hDB : Γ ⊢[PRAAx] le D B) (hDC : Γ ⊢[PRAAx] le D C)
    (h : Γ ⊢[PRAAx] upper a b (B+C) (B*C)) : Γ ⊢[PRAAx] upper a b two D :=
  upper_two_errors_same hD (upper_two_errors_retime hBC hDB hDC h)

/-- A single reciprocal error is covered by a pair including a denominator no larger. -/
theorem upper_one_error {a b B D E : PTm n} (hB : Γ ⊢[PRAAx] le one B) (hEB : Γ ⊢[PRAAx] le E B)
    (h : Γ ⊢[PRAAx] upper a b one B) : Γ ⊢[PRAAx] upper a b (D+E) (D*E) :=
  upper_mono _ _ _ _ _ _ hB h (le_congr (by ipra_ring) (by ipra_ring)
    (le_trans (mul_le_mul_right D hEB) (le_add_right (B*D) (E*B))))

theorem radius_cancel (a b A B c : PTm n) (hc : Γ ⊢[PRAAx] le one c)
    (h : Γ ⊢[PRAAx] radius a b (c*A) (c*B)) : Γ ⊢[PRAAx] radius a b A B :=
  positive_cancel hc (le_congr (by ipra_ring) (by ipra_ring) h)

/-- Add two successive one-sided bounds at a common positive denominator. -/
theorem upper_triangle_same {a b c A C B : PTm n} (hB : Γ ⊢[PRAAx] le one B)
    (hab : Γ ⊢[PRAAx] upper a b A B) (hbc : Γ ⊢[PRAAx] upper b c C B) :
    Γ ⊢[PRAAx] upper a c (A+C) B :=
  upper_cancel a c (A+C) B B hB (upper_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (upper_triangle a b c A B C B hab hbc))

/-- Add two successive radii at a common positive denominator. -/
theorem radius_triangle_same {a b c A C B : PTm n} (hB : Γ ⊢[PRAAx] le one B)
    (hab : Γ ⊢[PRAAx] radius a b A B) (hbc : Γ ⊢[PRAAx] radius b c C B) :
    Γ ⊢[PRAAx] radius a c (A+C) B :=
  radius_cancel a c (A+C) B B hB (radius_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (radius_triangle a b c A B C B hab hbc))

/-- Actual signed numerator swap, preserving predecessor-denominator storage. -/
def negate (a : PTm n) : PTm n :=
  pairT (pairT (numeratorOf a).neg (numeratorOf a).pos) (sndT a)

ipra_subst negate [numeratorOf, ZT.subst]

theorem negate_pos (a : PTm n) : Γ ⊢[PRAAx] (numeratorOf (negate a)).pos ≐ (numeratorOf a).neg :=
  (fst_pair _ _).fstE
theorem negate_neg (a : PTm n) : Γ ⊢[PRAAx] (numeratorOf (negate a)).neg ≐ (numeratorOf a).pos :=
  (fst_pair _ _).sndE
theorem negate_denominator (a : PTm n) : Γ ⊢[PRAAx] denominatorOf (negate a) ≐ denominatorOf a :=
  congrSucc (snd_pair _ _)

theorem negate_congr {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) : Γ ⊢[PRAAx] negate a ≐ negate b := by
  ipra_congr (negate (var 0) : PTm 1) with [h]

theorem crossLeft_negate (a b : PTm n) :
    Γ ⊢[PRAAx] crossLeft (negate b) (negate a) ≐ crossLeft a b :=
  (congrAdd (congrMul (negate_pos b) (negate_denominator a))
    (congrMul (negate_neg a) (negate_denominator b))).eqTrans (add_comm _ _)

theorem upper_negate (a b A B : PTm n) (h : Γ ⊢[PRAAx] upper a b A B) :
    Γ ⊢[PRAAx] upper (negate b) (negate a) A B := by
  have L : Γ ⊢[PRAAx] B*crossLeft (negate b) (negate a) ≐ B*crossLeft a b :=
    congrMul (.eqRefl _) (crossLeft_negate a b)
  have R : Γ ⊢[PRAAx] B*crossLeft (negate a) (negate b)+A*denominatorOf (negate b)*denominatorOf (negate a) ≐
      B*crossLeft b a+A*denominatorOf a*denominatorOf b :=
    (congrAdd (congrMul (.eqRefl _) (crossLeft_negate b a))
      (congrMul (congrMul (.eqRefl _) (negate_denominator b)) (negate_denominator a))).eqTrans (by ipra_ring)
  exact le_congr L.eqSymm R.eqSymm h

theorem radius_negate (a b A B : PTm n) (h : Γ ⊢[PRAAx] radius a b A B) :
    Γ ⊢[PRAAx] radius (negate a) (negate b) A B :=
  radius_of_upper _ _ A B
    (upper_negate b a A B (upper_of_radius b a A B (radius_symmetric a b A B h)))
    (upper_negate a b A B (upper_of_radius a b A B h))

/-- Transport uses decoded numerator/denominator equality, never equality of
potentially noncanonical raw codes. -/
theorem upper_components {a a' b b' A B : PTm n}
    (hap : Γ ⊢[PRAAx] (numeratorOf a).pos ≐ (numeratorOf a').pos)
    (han : Γ ⊢[PRAAx] (numeratorOf a).neg ≐ (numeratorOf a').neg)
    (had : Γ ⊢[PRAAx] denominatorOf a ≐ denominatorOf a')
    (hbp : Γ ⊢[PRAAx] (numeratorOf b).pos ≐ (numeratorOf b').pos)
    (hbn : Γ ⊢[PRAAx] (numeratorOf b).neg ≐ (numeratorOf b').neg)
    (hbd : Γ ⊢[PRAAx] denominatorOf b ≐ denominatorOf b')
    (h : Γ ⊢[PRAAx] upper a b A B) : Γ ⊢[PRAAx] upper a' b' A B :=
  le_congr (congrMul (.eqRefl _) (congrAdd (congrMul hap hbd) (congrMul hbn had)))
    (congrAdd (congrMul (.eqRefl _) (congrAdd (congrMul hbp had) (congrMul han hbd)))
      (congrMul (congrMul (.eqRefl _) had) hbd)) h

theorem upper_unnegate_right (a b A B : PTm n)
    (h : Γ ⊢[PRAAx] upper a (negate (negate b)) A B) : Γ ⊢[PRAAx] upper a b A B :=
  upper_components (.eqRefl _) (.eqRefl _) (.eqRefl _)
    ((negate_pos (negate b)).eqTrans (negate_neg b))
    ((negate_neg (negate b)).eqTrans (negate_pos b))
    ((negate_denominator (negate b)).eqTrans (negate_denominator b)) h

theorem upper_unnegate_left (a b A B : PTm n)
    (h : Γ ⊢[PRAAx] upper (negate (negate a)) b A B) : Γ ⊢[PRAAx] upper a b A B :=
  upper_components ((negate_pos (negate a)).eqTrans (negate_neg a))
    ((negate_neg (negate a)).eqTrans (negate_pos a))
    ((negate_denominator (negate a)).eqTrans (negate_denominator a))
    (.eqRefl _) (.eqRefl _) (.eqRefl _) h

theorem upper_negate_elim (a b A B : PTm n)
    (h : Γ ⊢[PRAAx] upper (negate a) b A B) : Γ ⊢[PRAAx] upper (negate b) a A B :=
  upper_unnegate_right _ _ A B (upper_negate _ _ A B h)

end LeanProofs.IPRA.Analysis.RationalValueBounds
