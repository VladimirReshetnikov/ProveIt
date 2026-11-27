import IPRADerivations.Analysis.Gamma.EulerProducts.Approximants.Continuity.GaussianGammaEulerContinuityReference
import IPRADerivations.Analysis.Logarithm.FiniteSeries.Composition.GaussianFiniteLogarithmDyadicTail
import IPRADerivations.Analysis.Names.Rates.Reciprocals.GaussianNamedInverseRate

/-!
# A computed continuity modulus for the SAME original C7 Gamma name

The C10 cutoff is fixed before the common finite exponential reference.
Its actual input variation is then controlled by a numerical dyadic
modulus depending only on the requested accuracy and original disk.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaInputContinuity

open_ipra
open GaussianGammaEulerContinuityReference (headBound inputGain reference reciprocalBudget original_C7_reference reference_distance_wide)
open GaussianRationalHorner (positive_product ofGaussian)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same distance_symmetric)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def loss (R N : PTm n) : PTm n := num 6+num 6*headBound R N+two*headBound R N*R
def numerator (p q r R A D N : PTm n) : PTm n :=
  two*GaussianGammaEulerApproximationName.rate R*D*unit p*unit q*unit r+
  N*D*((unit p+unit q)*unit r+loss R N*unit p*unit q)+
  N*inputGain r R N*A*unit p*unit q*unit r
def denominator (p q r D N : PTm n) : PTm n := N*D*unit p*unit q*unit r
ipra_subst loss

/-- Quantitative original C7 continuity before choosing the cutoff and
accuracy schedules. Every tolerance is derived from original input data. -/
theorem quantitative_distance (p q r z w R B A D N : PTm n)
    (hz : Γ ⊢[PRAAx] GaussianGammaEulerConvergence.source z R B N)
    (hw : Γ ⊢[PRAAx] GaussianGammaEulerConvergence.source w R B N)
    (hD : Γ ⊢[PRAAx] le one D)
    (hd : Γ ⊢[PRAAx] distanceBounded (ofGaussian z B) (ofGaussian w B) A D) : Γ ⊢[PRAAx]
    distanceBounded (GaussianGammaC7Name.sample p z R B) (GaussianGammaC7Name.sample q w R B)
      (numerator p q r R A D N) (denominator p q r D N) := by
  have hN := (GaussianGammaEulerConvergence.local_source z R B N hz).andE₂.andE₁
  have den : Γ ⊢[PRAAx] le one (denominator p q r D N) :=
    positive_product _ _ (positive_product _ _ (positive_product _ _ (positive_product _ _ hN hD) (unit_positive p)) (unit_positive q)) (unit_positive r)
  have left := distance_radius_mono _ _ _ _ (reciprocalBudget p r R N*D*unit q) (denominator p q r D N)
    (positive_product _ _ (positive_product _ _ hN (unit_positive p)) (unit_positive r)) den
    (le_of_eq_add (d := zero) (by unfold denominator; ipra_ring)) (original_C7_reference p r z R B N hz)
  have middle := distance_radius_mono _ _ _ _
    ((inputGain r R N*A*unit r+two*headBound R N*D*R)*N*unit p*unit q) (denominator p q r D N)
    (positive_product _ _ hD (unit_positive r)) den (le_of_eq_add (d := zero) (by unfold denominator; ipra_ring))
    (reference_distance_wide r z w R B A D N hN hz.andE₁.andE₂.andE₁ hD hz.andE₁.andE₂.andE₂ hw.andE₁.andE₂.andE₂ hd)
  have right := distance_radius_mono _ _ _ _ (reciprocalBudget q r R N*D*unit p) (denominator p q r D N)
    (positive_product _ _ (positive_product _ _ hN (unit_positive q)) (unit_positive r)) den
    (le_of_eq_add (d := zero) (by unfold denominator; ipra_ring))
    (distance_symmetric _ _ _ _ (positive_product _ _ (positive_product _ _ hN (unit_positive q)) (unit_positive r))
      (original_C7_reference q r w R B N hw))
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold numerator reciprocalBudget loss; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ den (distance_triangle_same _ _ _ _ _ _ den left middle) right)

def cutoff (s R : PTm n) : PTm n := succ (GaussianGammaEulerApproximationName.cutoff (s+num 3) R)
def accuracy (s R : PTm n) : PTm n := s+loss R (cutoff s R)+num 4
def modulus (s R : PTm n) : PTm n := s+inputGain (accuracy s R) R (cutoff s R)+num 4
ipra_subst cutoff
ipra_subst accuracy
ipra_subst modulus [GaussianGammaEulerContinuityReference.inputGain, GaussianGammaEulerContinuityReference.finiteGain, GaussianGammaEulerContinuityReference.finiteBound]

theorem cutoff_positive (s R : PTm n) : Γ ⊢[PRAAx] le one (cutoff s R) := zero_lt_succ _
theorem cutoff_source (s z R B : PTm n) (h : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source z R B) : Γ ⊢[PRAAx]
    GaussianGammaEulerConvergence.source z R B (cutoff s R) := by
  have old := GaussianGammaEulerApproximationName.cutoff_guards (Γ := Γ) (s+num 3) R
  exact .andI h (.andI (le_trans old.andE₁ (le_succ_self _)) (le_trans old.andE₂.andE₁ (le_succ_self _)))

theorem binary_padding (s C : PTm n) : Γ ⊢[PRAAx] le (num 4*C*unit s) (unit (s+C+num 4)) := by
  have old := le_trans (le_succ_self (Γ := Γ) C) (RationalClosure.succ_le_two_pow C)
  have first : Γ ⊢[PRAAx] le (C*(num 4*unit s)) (unit C*(num 4*unit s)) := mul_le_mul_right (num 4*unit s) old
  have four : Γ ⊢[PRAAx] le (num 4) (num 16) := le_of_eq_add (d := num 12) (by ipra_ring)
  have second := mul_le_mul_right (unit C*unit s) four
  have e : Γ ⊢[PRAAx] unit (s+C+num 4) ≐ (unit s*unit C)*num 16 :=
    (pw_add two (s+C) (num 4)).eqTrans (congrMul (pw_add two s C) GaussianFiniteLogarithmDyadicTail.two_four)
  have right : Γ ⊢[PRAAx] num 16*(unit C*unit s) ≐ unit (s+C+num 4) :=
    (by ipra_ring : Γ ⊢[PRAAx] num 16*(unit C*unit s) ≐ (unit s*unit C)*num 16).eqTrans e.eqSymm
  exact le_trans (le_congr (by ipra_ring) (.eqRefl _) first) (le_congr (by ipra_ring) right second)

theorem cutoff_budget (s R : PTm n) : Γ ⊢[PRAAx]
    le (num 8*GaussianGammaEulerApproximationName.rate R*unit s) (cutoff s R) := by
  have old := (GaussianGammaEulerApproximationName.cutoff_guards (Γ := Γ) (s+num 3) R).andE₂.andE₂
  have e : Γ ⊢[PRAAx] unit (succ (s+num 3)) ≐ unit s*num 16 :=
    (congrAp2 powF (by ipra_ring : Γ ⊢[PRAAx] succ (s+num 3) ≐ s+num 4) (.eqRefl two)).eqTrans
      ((pw_add two s (num 4)).eqTrans (congrMul (.eqRefl _) GaussianFiniteLogarithmDyadicTail.two_four))
  have twice := mul_le_mul_right (GaussianGammaEulerApproximationName.rate R*unit s)
    (le_of_eq_add (Γ := Γ) (d := num 8) (by ipra_ring) : Γ ⊢[PRAAx] le (num 8) (num 16))
  have right : Γ ⊢[PRAAx] num 16*(GaussianGammaEulerApproximationName.rate R*unit s) ≐
      GaussianGammaEulerApproximationName.rate R*unit (succ (s+num 3)) :=
    (by ipra_ring : Γ ⊢[PRAAx] num 16*(GaussianGammaEulerApproximationName.rate R*unit s) ≐
      GaussianGammaEulerApproximationName.rate R*(unit s*num 16)).eqTrans (congrMul (.eqRefl _) e.eqSymm)
  exact le_trans (le_trans (le_congr (by ipra_ring) right twice) old) (le_succ_self _)

/-- The three independently derived residual budgets fit inside one
requested dyadic unit; all schedules are actual numerical terms. -/
theorem residual_budget (s R : PTm n) : Γ ⊢[PRAAx]
    le ((two*GaussianGammaEulerApproximationName.rate R*unit (modulus s R)*unit (accuracy s R)+
      cutoff s R*loss R (cutoff s R)*unit (modulus s R)+
      cutoff s R*inputGain (accuracy s R) R (cutoff s R)*unit (accuracy s R))*unit s)
      (cutoff s R*unit (modulus s R)*unit (accuracy s R)) := by
  let N := cutoff s R
  let T := loss R N
  let C := inputGain (accuracy s R) R N
  let D := unit (modulus s R)
  let U := unit (accuracy s R)
  let Z := N*D*U
  have a := mul_le_mul_right (D*U) (cutoff_budget (Γ := Γ) s R)
  have b := mul_le_mul_right (N*D) (binary_padding (Γ := Γ) s T)
  have c := mul_le_mul_right (N*U) (binary_padding (Γ := Γ) s C)
  have together := add_le_add₂ (add_le_add₂ a b) c
  have first : Γ ⊢[PRAAx] le (num 4*((two*GaussianGammaEulerApproximationName.rate R*D*U+N*T*D+N*C*U)*unit s)) (num 3*Z) :=
    le_congr (by unfold U D accuracy modulus T C N; ipra_ring) (by unfold Z U D accuracy modulus T C N; ipra_ring) together
  have grow : Γ ⊢[PRAAx] le (num 3*Z) (num 4*Z) := le_of_eq_add (d := Z) (by ipra_ring)
  exact RationalValueBounds.positive_cancel
    (le_of_eq_add (d := num 3) (by ipra_ring) : Γ ⊢[PRAAx] le one (num 4)) (le_trans first grow)

def tolerance (p q s : PTm n) : PTm n := (unit p+unit q)*unit s+unit p*unit q
def toleranceDen (p q s : PTm n) : PTm n := unit p*unit q*unit s
ipra_subst tolerance
ipra_subst toleranceDen

/-- Actual original reciprocal Gamma continuity on every original disk.
The returned observation error is exactly 2^-p+2^-q+2^-s. -/
theorem original_C7_continuity (p q s z w R B : PTm n)
    (hz : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source z R B)
    (hw : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source w R B)
    (hd : Γ ⊢[PRAAx] distanceBounded (ofGaussian z B) (ofGaussian w B) one (unit (modulus s R))) : Γ ⊢[PRAAx]
    distanceBounded (GaussianGammaC7Name.sample p z R B) (GaussianGammaC7Name.sample q w R B)
      (tolerance p q s) (toleranceDen p q s) := by
  let N := cutoff s R
  let D := unit (modulus s R)
  let U := unit (accuracy s R)
  have den : Γ ⊢[PRAAx] le one (denominator p q (accuracy s R) D N) :=
    positive_product _ _ (positive_product _ _ (positive_product _ _ (positive_product _ _ (cutoff_positive s R) (unit_positive _)) (unit_positive p)) (unit_positive q)) (unit_positive _)
  have residual := mul_le_mul_right (unit p*unit p*unit q*unit q) (residual_budget (Γ := Γ) s R)
  have both := add_le_add₂ (le_refl (Γ := Γ) (N*D*(unit p+unit q)*U*unit p*unit q*unit s)) residual
  apply distance_radius_mono _ _ _ _ (tolerance p q s) (toleranceDen p q s) den
    (positive_product _ _ (positive_product _ _ (unit_positive p) (unit_positive q)) (unit_positive s)) _
    (quantitative_distance p q (accuracy s R) z w R B one D N (cutoff_source s z R B hz) (cutoff_source s w R B hw) (unit_positive _) hd)
  exact le_congr (by simp only [numerator,denominator,tolerance,toleranceDen,N,D,U]; ipra_ring)
    (by simp only [denominator,tolerance,toleranceDen,N,D,U]; ipra_ring) both

/-- The exact independent-precision rate interface for the original names. -/
theorem original_C7_independent_rate (s z w R B : PTm n)
    (hz : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source z R B)
    (hw : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source w R B)
    (hd : Γ ⊢[PRAAx] distanceBounded (ofGaussian z B) (ofGaussian w B) one (unit (modulus s R))) : Γ ⊢[PRAAx]
    GaussianNamedInverseRate.independentRate GaussianGammaC7Name.nameF GaussianGammaC7Name.nameF
      (GaussianGammaC7Name.data z R B) (GaussianGammaC7Name.data w R B) one (unit s) := by
  refine .allI (.allI ?_)
  have zs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
      GaussianGammaCanonicalExponent.source (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift B)) := by
    simpa [Fm.shift,Syn.shift] using hz.shift.shift
  have ws : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
      GaussianGammaCanonicalExponent.source (Syn.shift (Syn.shift w)) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift B)) := by
    simpa [Fm.shift,Syn.shift] using hw.shift.shift
  have ds : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
      distanceBounded (ofGaussian (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift B)))
        (ofGaussian (Syn.shift (Syn.shift w)) (Syn.shift (Syn.shift B))) one
        (unit (modulus (Syn.shift (Syn.shift s)) (Syn.shift (Syn.shift R)))) := by
    simpa [Fm.shift,Syn.shift] using hd.shift.shift
  have old := original_C7_continuity (var 1) (var 0) (Syn.shift (Syn.shift s)) (Syn.shift (Syn.shift z))
    (Syn.shift (Syn.shift w)) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift B)) zs ws ds
  have aligned : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
      distanceBounded (GaussianGammaC7Name.sample (var 1) (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift B)))
        (GaussianGammaC7Name.sample (var 0) (Syn.shift (Syn.shift w)) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift B)))
        (GaussianNamedInverseRate.rateNumerator one (unit (Syn.shift (Syn.shift s))) (var 1) (var 0))
        (GaussianNamedInverseRate.rateDenominator (unit (Syn.shift (Syn.shift s))) (var 1) (var 0)) :=
    distance_congr (.eqRefl _) (.eqRefl _)
      (by unfold tolerance GaussianNamedInverseRate.rateNumerator; ipra_ring)
      (by unfold toleranceDen GaussianNamedInverseRate.rateDenominator; ipra_ring) old
  simpa only [GaussianNamedInverseRate.independentRate,GaussianGammaC7Name.sample,
    GaussianGammaC7Name.subst_data,PTm.subst_succ,PTm.subst_zero,GaussianCoefficientNameBounds.subst_unit,Syn.shift] using aligned

def input (s z w R B : PTm n) : Fm PTm n := GaussianGammaCanonicalExponent.source z R B ⋏
  (GaussianGammaCanonicalExponent.source w R B ⋏ distanceBounded (ofGaussian z B) (ofGaussian w B) one (unit (modulus s R)))
ipra_subst input

/-- Both original observations, computed input modulus and exact returned tolerance. -/
def output (p q s z w R B : PTm n) : PTm n := pairT (GaussianGammaC7Name.sample p z R B)
  (pairT (GaussianGammaC7Name.sample q w R B) (pairT (modulus s R) (pairT (tolerance p q s) (toleranceDen p q s))))
def outputF : PR 7 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
def run (p q s z w R B : PTm n) : PTm n := PTm.app outputF ![p,q,s,z,w,R,B]
ipra_subst output [GaussianGammaC7Name.sample]
ipra_subst run

theorem program_at (p q s z w R B : PTm n) : Γ ⊢[PRAAx] run p q s z w R B ≐ output p q s z w R B := by
  simpa [run,outputF] using toPR_eq (Γ := Γ)
    (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) : PTm 7) ![p,q,s,z,w,R,B]
theorem returned_left (p q s z w R B : PTm n) : Γ ⊢[PRAAx] fstT (run p q s z w R B) ≐ GaussianGammaC7Name.sample p z R B :=
  (program_at p q s z w R B).fstE
theorem returned_tail (p q s z w R B : PTm n) : Γ ⊢[PRAAx] sndT (run p q s z w R B) ≐
    pairT (GaussianGammaC7Name.sample q w R B) (pairT (modulus s R) (pairT (tolerance p q s) (toleranceDen p q s))) :=
  (program_at p q s z w R B).sndE
theorem returned_right (p q s z w R B : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run p q s z w R B)) ≐ GaussianGammaC7Name.sample q w R B :=
  (returned_tail p q s z w R B).fstE
theorem returned_rest (p q s z w R B : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run p q s z w R B)) ≐
    pairT (modulus s R) (pairT (tolerance p q s) (toleranceDen p q s)) :=
  (returned_tail p q s z w R B).sndE
theorem returned_modulus (p q s z w R B : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run p q s z w R B))) ≐ modulus s R :=
  (returned_rest p q s z w R B).fstE
theorem returned_budget (p q s z w R B : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run p q s z w R B))) ≐
    pairT (tolerance p q s) (toleranceDen p q s) :=
  (returned_rest p q s z w R B).sndE
theorem returned_numerator (p q s z w R B : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (sndT (run p q s z w R B)))) ≐ tolerance p q s :=
  (returned_budget p q s z w R B).fstE
theorem returned_denominator (p q s z w R B : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (sndT (run p q s z w R B)))) ≐ toleranceDen p q s :=
  (returned_budget p q s z w R B).sndE
theorem returned_distance (p q s z w R B : PTm n) (h : Γ ⊢[PRAAx] input s z w R B) : Γ ⊢[PRAAx]
    distanceBounded (fstT (run p q s z w R B)) (fstT (sndT (run p q s z w R B)))
      (fstT (sndT (sndT (sndT (run p q s z w R B))))) (sndT (sndT (sndT (sndT (run p q s z w R B))))) :=
  distance_congr (returned_left p q s z w R B).eqSymm (returned_right p q s z w R B).eqSymm
    (returned_numerator p q s z w R B).eqSymm (returned_denominator p q s z w R B).eqSymm
    (original_C7_continuity p q s z w R B h.andE₁ h.andE₂.andE₁ h.andE₂.andE₂)

theorem actual_original_C7_input_continuity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (input (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      distanceBounded (GaussianGammaC7Name.sample (var 0) (var 3) (var 5) (var 6))
        (GaussianGammaC7Name.sample (var 1) (var 4) (var 5) (var 6)) (tolerance (var 0) (var 1) (var 2)) (toleranceDen (var 0) (var 1) (var 2))) :=
  closeUniv 7 (.impI (original_C7_continuity _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))
theorem actual_original_C7_input_independent_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      GaussianNamedInverseRate.independentRate GaussianGammaC7Name.nameF GaussianGammaC7Name.nameF
        (GaussianGammaC7Name.data (var 1) (var 3) (var 4)) (GaussianGammaC7Name.data (var 2) (var 3) (var 4)) one (unit (var 0))) :=
  closeUniv 5 (.impI (original_C7_independent_rate _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))
theorem actual_continuity_binary_padding_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le (num 4*var 1*unit (var 0)) (unit (var 0+var 1+num 4))) := closeUniv 2 (binary_padding _ _)
theorem actual_continuity_cutoff_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le (num 8*GaussianGammaEulerApproximationName.rate (var 1)*unit (var 0)) (cutoff (var 0) (var 1))) :=
  closeUniv 2 (cutoff_budget _ _)
theorem actual_original_C7_continuity_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ≐
      output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) := closeUniv 7 (program_at _ _ _ _ _ _ _)
theorem actual_returned_original_C7_input_continuity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (input (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      distanceBounded (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)))
        (fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))))
        (fstT (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))))))
        (sndT (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))))))) :=
  closeUniv 7 (.impI (returned_distance _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaInputContinuity
