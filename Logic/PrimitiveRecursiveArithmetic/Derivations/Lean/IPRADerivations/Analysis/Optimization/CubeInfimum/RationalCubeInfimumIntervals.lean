import IPRADerivations.Analysis.RationalArithmetic.Grids.Minimization.RationalCubeMinimum

/-!
# The original intervals around actual cube minima

These are the source L_k=m_k-2^(-k-1), U_k=m_k+2^(-k-2).
Their cross order follows from the actual minimum and selected-point
errors at one explicit computed precision. Signed rational endpoints keep
all original decoded denominators. No interval consistency is assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalCubeInfimumIntervals

open_ipra
open RationalCubeMinimum (minimum minimizer coherence continuity)
open RationalCubeGrid (scale fraction)
open RationalSupMetric (numeratorOf denominatorOf)
open RationalArithmetic (represents)
open RationalArgmin (rationalLE)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

def lower (A : PR 3) (mu : PR 2) (d k x : PTm n) : PTm n := RationalArithmetic.add (minimum A mu d k x)
  (RationalArithmetic.negative (fraction one (succ k)))
def upper (A : PR 3) (mu : PR 2) (d k x : PTm n) : PTm n := RationalArithmetic.add (minimum A mu d k x)
  (fraction one (RationalCubeMinimum.precision k))
def lowerNumerator (A : PR 3) (mu : PR 2) (d k x : PTm n) : ZT n :=
  numeratorOf (minimum A mu d k x)*ZT.ofNat (scale (succ k))-ZT.ofNat (denominatorOf (minimum A mu d k x))
def upperNumerator (A : PR 3) (mu : PR 2) (d k x : PTm n) : ZT n :=
  numeratorOf (minimum A mu d k x)*ZT.ofNat (scale (RationalCubeMinimum.precision k))+ZT.ofNat (denominatorOf (minimum A mu d k x))
def lowerDenominator (A : PR 3) (mu : PR 2) (d k x : PTm n) : PTm n := denominatorOf (minimum A mu d k x)*scale (succ k)
def upperDenominator (A : PR 3) (mu : PR 2) (d k x : PTm n) : PTm n := denominatorOf (minimum A mu d k x)*scale (RationalCubeMinimum.precision k)

ipra_subst lower [one]
ipra_subst upper [one]
ipra_subst lowerNumerator
ipra_subst upperNumerator
ipra_subst lowerDenominator
ipra_subst upperDenominator

theorem lower_positive (A : PR 3) (mu : PR 2) (d k x : PTm n) : Γ ⊢[PRAAx] le one (lowerDenominator A mu d k x) :=
  RationalAlgebra.positive_product (RationalArgmin.denominator_positive _) (RationalCubeGrid.scale_positive _)
theorem upper_positive (A : PR 3) (mu : PR 2) (d k x : PTm n) : Γ ⊢[PRAAx] le one (upperDenominator A mu d k x) :=
  RationalAlgebra.positive_product (RationalArgmin.denominator_positive _) (RationalCubeGrid.scale_positive _)
theorem lower_canonical (A : PR 3) (mu : PR 2) (d k x : PTm n) : Γ ⊢[PRAAx] RationalNormalForm.wellFormed (lower A mu d k x) := RationalArithmetic.add_guard _ _
theorem upper_canonical (A : PR 3) (mu : PR 2) (d k x : PTm n) : Γ ⊢[PRAAx] RationalNormalForm.wellFormed (upper A mu d k x) := RationalArithmetic.add_guard _ _

theorem lower_represents (A : PR 3) (mu : PR 2) (d k x : PTm n) : Γ ⊢[PRAAx]
    represents (lower A mu d k x) (lowerNumerator A mu d k x) (lowerDenominator A mu d k x) := by
  have r := RationalRepresentations.represents_add (Γ := Γ) (minimum A mu d k x)
    (RationalArithmetic.negative (fraction one (succ k))) _ _ _ _ (RationalRepresentations.represents_self _)
    (RationalRepresentations.represents_negative _ _ _ (RationalCubeGrid.fraction_represents one (succ k)))
  ipra_lc [lower, lowerNumerator, lowerDenominator] ZT.toZ_eq r

theorem upper_represents (A : PR 3) (mu : PR 2) (d k x : PTm n) : Γ ⊢[PRAAx]
    represents (upper A mu d k x) (upperNumerator A mu d k x) (upperDenominator A mu d k x) := by
  have r := RationalRepresentations.represents_add (Γ := Γ) (minimum A mu d k x)
    (fraction one (RationalCubeMinimum.precision k)) _ _ _ _ (RationalRepresentations.represents_self _)
    (RationalCubeGrid.fraction_represents one (RationalCubeMinimum.precision k))
  ipra_lc [upper, upperNumerator, upperDenominator] ZT.toZ_eq r

/-- The exact source cross inequalities, obtained at a finite computed query. -/
theorem cross_order (A : PR 3) (mu : PR 2) (d x i j : PTm n) (hc : Γ ⊢[PRAAx] coherence A d x)
    (ht : Γ ⊢[PRAAx] continuity A mu d x) : Γ ⊢[PRAAx] rationalLE (lower A mu d i x) (upper A mu d j x) := by
  let a := minimum A mu d i x
  let b := minimum A mu d j x
  let H := scale (succ i)
  let T := scale (RationalCubeMinimum.precision j)
  let D := denominatorOf a
  let E := denominatorOf b
  let U := H*T*RationalValueBounds.crossLeft a b
  let V := H*T*RationalValueBounds.crossLeft b a+(H+T)*D*E
  let C := two*H*T*D*E
  have first := RationalCubeMinimum.minimum_upper A mu d i x (minimizer A mu d j x) C ht (RationalCubeMinimum.minimizer_presented _ _ _ _ _)
  have second := RationalCubeMinimum.minimizer_upper A mu d j x C hc
  have sum := RationalValueBounds.upper_triangle a (RationalCubeMinimum.sample A (minimizer A mu d j x) C x) b
    (H+scale C) (H*scale C) (T+scale C) (T*scale C) first second
  have reduced : Γ ⊢[PRAAx] RationalValueBounds.upper a b (two*H*T+scale C*(H+T)) (H*T*scale C) :=
    RationalValueBounds.upper_cancel _ _ _ _ (scale C) (RationalCubeGrid.scale_positive C)
      (RationalValueBounds.upper_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (by ipra_ring) sum)
  have finite : Γ ⊢[PRAAx] le (U*scale C) (V*scale C+C) :=
    le_congr (by dsimp [U]; ipra_ring) (by dsimp [V,C,D,E]; ipra_ring) reduced
  have gap : Γ ⊢[PRAAx] le U V := GapRemoval.gap finite
  apply RationalArithmetic.order_of_representations _ _ _ _ _ _ (lower_represents A mu d i x) (upper_represents A mu d j x)
    (lower_positive _ _ _ _ _) (upper_positive _ _ _ _ _)
  change Γ ⊢[PRAAx] zle
    ((numeratorOf a*ZT.ofNat H-ZT.ofNat D)*ZT.ofNat (E*T))
    ((numeratorOf b*ZT.ofNat T+ZT.ofNat E)*ZT.ofNat (D*H))
  apply zle_of_toZ (monus V U)
  have e := natEq (eq_add_of_le gap)
  simp only [ZT.toZ_mul,ZT.toZ_sub,ZT.toZ_add,ZT.toZ_ofNat]
  simp only [ZT.toZ]
  dsimp [U,V,D,E]
  dsimp [U,V,D,E] at e
  unfold RationalValueBounds.crossLeft at e ⊢
  ipra_simps
  linear_combination -e

/-- A signed counterpart of the natural representative error bridge. -/
theorem upper_of_representations (c d : PTm n) (a b : ZT n) (A B P Q : PTm n)
    (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B)
    (hc : Γ ⊢[PRAAx] represents c a A) (hd : Γ ⊢[PRAAx] represents d b B)
    (h : Γ ⊢[PRAAx] zle (ZT.ofNat Q*(a*ZT.ofNat B-b*ZT.ofNat A)) (ZT.ofNat (P*A*B))) :
    Γ ⊢[PRAAx] RationalValueBounds.upper c d P Q := by
  let gap := monus ((ZT.ofNat (P*A*B)).pos+(ZT.ofNat Q*(a*ZT.ofNat B-b*ZT.ofNat A)).neg)
    ((ZT.ofNat Q*(a*ZT.ofNat B-b*ZT.ofNat A)).pos+(ZT.ofNat (P*A*B)).neg)
  have eq := ZT.toZ_eq hc
  have ed := ZT.toZ_eq hd
  have bound := zle_toZ h
  apply RationalValueBounds.positive_cancel (RationalAlgebra.positive_product hA hB)
  refine le_of_eq_add (d := denominatorOf c*denominatorOf d*gap) ?_
  apply deriveNat
  simp only [ZT.toZ_mul,ZT.toZ_ofNat,ZT.toZ_sub] at eq ed bound
  simp only [ZT.toZ] at eq ed bound
  unfold RationalValueBounds.crossLeft
  dsimp [gap]
  ipra_simps
  linear_combination 𝔞(Q)*𝔞(B)*𝔞(denominatorOf d)*eq-𝔞(Q)*𝔞(A)*𝔞(denominatorOf c)*ed-
    𝔞(denominatorOf c)*𝔞(denominatorOf d)*bound

/-- L_k is a source lower bound, unfolded at every requested sampler precision. -/
theorem lower_sample (A : PR 3) (mu : PR 2) (d k x y p : PTm n) (ht : Γ ⊢[PRAAx] continuity A mu d x)
    (hy : Γ ⊢[PRAAx] RationalCubeMinimum.presentedCube y d) : Γ ⊢[PRAAx]
    RationalValueBounds.upper (lower A mu d k x) (RationalCubeMinimum.sample A y p x) one (scale p) := by
  let a := minimum A mu d k x
  let b := RationalCubeMinimum.sample A y p x
  let H := scale (succ k)
  let S := scale p
  let D := denominatorOf a
  let E := denominatorOf b
  let gap := monus ((H*S)*RationalValueBounds.crossLeft b a+(H+S)*D*E) ((H*S)*RationalValueBounds.crossLeft a b)
  have old := RationalCubeMinimum.minimum_upper A mu d k x y p ht hy
  have eq : Γ ⊢[PRAAx] (H*S)*RationalValueBounds.crossLeft b a+(H+S)*D*E ≐
      (H*S)*RationalValueBounds.crossLeft a b+gap := eq_add_of_le old
  apply upper_of_representations _ _ _ _ _ _ _ _ (lower_positive A mu d k x) (RationalArgmin.denominator_positive b)
    (lower_represents A mu d k x) (RationalRepresentations.represents_self b)
  change Γ ⊢[PRAAx] zle (ZT.ofNat S*((numeratorOf a*ZT.ofNat H-ZT.ofNat D)*ZT.ofNat E-
    numeratorOf b*ZT.ofNat (D*H))) (ZT.ofNat (one*(D*H)*E))
  apply zle_of_toZ gap
  have e := natEq eq
  simp only [ZT.toZ_mul,ZT.toZ_sub,ZT.toZ_ofNat]
  simp only [ZT.toZ]
  dsimp [D,E] at e ⊢
  unfold RationalValueBounds.crossLeft at e
  ipra_simps
  linear_combination -e

/-- U_k encloses the actual selected point, at every requested precision. -/
theorem selected_sample (A : PR 3) (mu : PR 2) (d k x p : PTm n) (hc : Γ ⊢[PRAAx] coherence A d x) : Γ ⊢[PRAAx]
    RationalValueBounds.upper (RationalCubeMinimum.sample A (minimizer A mu d k x) p x) (upper A mu d k x) one (scale p) := by
  let a := RationalCubeMinimum.sample A (minimizer A mu d k x) p x
  let b := minimum A mu d k x
  let T := scale (RationalCubeMinimum.precision k)
  let S := scale p
  let D := denominatorOf a
  let E := denominatorOf b
  let gap := monus ((T*S)*RationalValueBounds.crossLeft b a+(T+S)*D*E) ((T*S)*RationalValueBounds.crossLeft a b)
  have old := RationalCubeMinimum.minimizer_upper A mu d k x p hc
  have eq : Γ ⊢[PRAAx] (T*S)*RationalValueBounds.crossLeft b a+(T+S)*D*E ≐
      (T*S)*RationalValueBounds.crossLeft a b+gap := eq_add_of_le old
  apply upper_of_representations _ _ _ _ _ _ _ _ (RationalArgmin.denominator_positive a) (upper_positive A mu d k x)
    (RationalRepresentations.represents_self a) (upper_represents A mu d k x)
  change Γ ⊢[PRAAx] zle (ZT.ofNat S*(numeratorOf a*ZT.ofNat (E*T)-
    (numeratorOf b*ZT.ofNat T+ZT.ofNat E)*ZT.ofNat D)) (ZT.ofNat (one*D*(E*T)))
  apply zle_of_toZ gap
  have e := natEq eq
  simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_sub,ZT.toZ_ofNat]
  simp only [ZT.toZ]
  dsimp [D,E] at e ⊢
  unfold RationalValueBounds.crossLeft at e
  ipra_simps
  linear_combination -e

/-- The exact source width 3/(4*2^k), before taking running intersections. -/
theorem original_width (A : PR 3) (mu : PR 2) (d k x : PTm n) : Γ ⊢[PRAAx]
    RationalValueBounds.radius (upper A mu d k x) (lower A mu d k x) (succ two) ((two*two)*scale k) := by
  let a := minimum A mu d k x
  let D := denominatorOf a
  let H := scale (succ k)
  let T := scale (RationalCubeMinimum.precision k)
  have cross : Γ ⊢[PRAAx] ZT.eq
      ((numeratorOf a*ZT.ofNat T+ZT.ofNat D)*ZT.ofNat (D*H)-
        (numeratorOf a*ZT.ofNat H-ZT.ofNat D)*ZT.ofNat (D*T)) (ZT.ofNat (D*D*(H+T))) := by
    ipra_lc
  apply RationalCubeGrid.radius_of_representations _ _ _ _ _ _ _ _ (upper_positive A mu d k x) (lower_positive A mu d k x)
    (upper_represents A mu d k x) (lower_represents A mu d k x)
  change Γ ⊢[PRAAx] le (((two*two)*scale k)*Foundations.GapDecision.zabs
      ((numeratorOf a*ZT.ofNat T+ZT.ofNat D)*ZT.ofNat (D*H)-
        (numeratorOf a*ZT.ofNat H-ZT.ofNat D)*ZT.ofNat (D*T))) ((succ two)*(D*T)*(D*H))
  have abs : Γ ⊢[PRAAx] Foundations.GapDecision.zabs
      ((numeratorOf a*ZT.ofNat T+ZT.ofNat D)*ZT.ofNat (D*H)-
        (numeratorOf a*ZT.ofNat H-ZT.ofNat D)*ZT.ofNat (D*T)) ≐ D*D*(H+T) :=
    (Foundations.GapDecision.zabs_congr (ZT.toZ_eq cross)).eqTrans
      ((congrAdd (monus_zero _) (zero_monus _)).eqTrans (add_zero _))
  apply le_congr (congrMul (.eqRefl _) abs).eqSymm (.eqRefl _)
  apply le_of_eq_add (d := zero)
  dsimp [H,T]
  apply deriveNat
  ipra_simps
  rw [natEq (RationalCubeMinimum.scale_precision (Γ := Γ) k)]
  ipra_simps
  have e1 : Γ ⊢[PRAAx] scale (succ k) ≐ scale k*two := pw_succ _ _
  rw [natEq e1]
  ipra_simps
  ring

theorem nonempty (A : PR 3) (mu : PR 2) (d k x : PTm n) (hc : Γ ⊢[PRAAx] coherence A d x)
    (ht : Γ ⊢[PRAAx] continuity A mu d x) : Γ ⊢[PRAAx] rationalLE (lower A mu d k x) (upper A mu d k x) :=
  cross_order A mu d x k k hc ht

def output (A : PR 3) (mu : PR 2) (d k x : PTm n) : PTm n := pairT (lower A mu d k x)
  (pairT (upper A mu d k x) (pairT (minimizer A mu d k x) (minimum A mu d k x)))
def outputF (A : PR 3) (mu : PR 2) : PR 3 := PTm.toPR (output A mu (var 0) (var 1) (var 2))
def run (A : PR 3) (mu : PR 2) (d k x : PTm n) : PTm n := app (outputF A mu) ![d,k,x]
ipra_subst output
ipra_subst run

theorem program_at (A : PR 3) (mu : PR 2) (d k x : PTm n) : Γ ⊢[PRAAx] run A mu d k x ≐ output A mu d k x := by
  simpa [run,outputF,Matrix.cons_val_succ',Matrix.cons_val_zero'] using
    toPR_eq (Γ := Γ) (output A mu (var 0) (var 1) (var 2) : PTm 3) ![d,k,x]
theorem returned_lower (A : PR 3) (mu : PR 2) (d k x : PTm n) : Γ ⊢[PRAAx] fstT (run A mu d k x) ≐ lower A mu d k x :=
  (program_at A mu d k x).fstE
theorem returned_upper (A : PR 3) (mu : PR 2) (d k x : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run A mu d k x)) ≐ upper A mu d k x :=
  (program_at A mu d k x).sndE.fstE
private theorem returned_tail (A : PR 3) (mu : PR 2) (d k x : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run A mu d k x)) ≐
    pairT (minimizer A mu d k x) (minimum A mu d k x) :=
  (program_at A mu d k x).sndE.sndE
theorem returned_minimizer (A : PR 3) (mu : PR 2) (d k x : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run A mu d k x))) ≐ minimizer A mu d k x :=
  (returned_tail A mu d k x).fstE
theorem returned_minimum (A : PR 3) (mu : PR 2) (d k x : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run A mu d k x))) ≐ minimum A mu d k x :=
  (returned_tail A mu d k x).sndE
theorem returned_width (A : PR 3) (mu : PR 2) (d k x : PTm n) : Γ ⊢[PRAAx]
    RationalValueBounds.radius (fstT (sndT (run A mu d k x))) (fstT (run A mu d k x)) (succ two) ((two*two)*scale k) :=
  RationalValueBounds.radius_congr (returned_upper A mu d k x).eqSymm (returned_lower A mu d k x).eqSymm (.eqRefl _) (.eqRefl _)
    (original_width A mu d k x)
theorem returned_lower_sample (A : PR 3) (mu : PR 2) (d k x y p : PTm n) (ht : Γ ⊢[PRAAx] continuity A mu d x)
    (hy : Γ ⊢[PRAAx] RationalCubeMinimum.presentedCube y d) : Γ ⊢[PRAAx]
    RationalValueBounds.upper (fstT (run A mu d k x)) (RationalCubeMinimum.sample A y p x) one (scale p) :=
  RationalValueBounds.upper_congr (returned_lower A mu d k x).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (lower_sample A mu d k x y p ht hy)

theorem actual_original_interval_representations_closed (A : PR 3) (mu : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (represents (lower A mu (var 0) (var 1) (var 2)) (lowerNumerator A mu (var 0) (var 1) (var 2)) (lowerDenominator A mu (var 0) (var 1) (var 2)) ⋏
      represents (upper A mu (var 0) (var 1) (var 2)) (upperNumerator A mu (var 0) (var 1) (var 2)) (upperDenominator A mu (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.andI (lower_represents _ _ _ _ _) (upper_represents _ _ _ _ _))
theorem actual_original_interval_canonical_closed (A : PR 3) (mu : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (RationalNormalForm.wellFormed (lower A mu (var 0) (var 1) (var 2)) ⋏ RationalNormalForm.wellFormed (upper A mu (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.andI (lower_canonical _ _ _ _ _) (upper_canonical _ _ _ _ _))
theorem actual_original_intervals_cross_order_closed (A : PR 3) (mu : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (coherence A (var 0) (var 1) ⟶ continuity A mu (var 0) (var 1) ⟶
      rationalLE (lower A mu (var 0) (var 2) (var 1)) (upper A mu (var 0) (var 3) (var 1))) :=
  closeUniv 4 (.impI (.impI (cross_order _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_original_interval_nonempty_closed (A : PR 3) (mu : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (coherence A (var 0) (var 2) ⟶ continuity A mu (var 0) (var 2) ⟶
      rationalLE (lower A mu (var 0) (var 1) (var 2)) (upper A mu (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (.impI (nonempty _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_original_interval_width_closed (A : PR 3) (mu : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (RationalValueBounds.radius (upper A mu (var 0) (var 1) (var 2)) (lower A mu (var 0) (var 1) (var 2)) (succ two) ((two*two)*scale (var 1))) :=
  closeUniv 3 (original_width _ _ _ _ _)
theorem actual_original_interval_lower_bound_closed (A : PR 3) (mu : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (continuity A mu (var 0) (var 2) ⟶ RationalCubeMinimum.presentedCube (var 3) (var 0) ⟶
      RationalValueBounds.upper (lower A mu (var 0) (var 1) (var 2)) (RationalCubeMinimum.sample A (var 3) (var 4) (var 2)) one (scale (var 4))) :=
  closeUniv 5 (.impI (.impI (lower_sample _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_original_interval_selected_upper_closed (A : PR 3) (mu : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (coherence A (var 0) (var 2) ⟶ RationalValueBounds.upper
      (RationalCubeMinimum.sample A (minimizer A mu (var 0) (var 1) (var 2)) (var 3) (var 2)) (upper A mu (var 0) (var 1) (var 2)) one (scale (var 3))) :=
  closeUniv 4 (.impI (selected_sample _ _ _ _ _ _ Prf.hyp0))
theorem actual_original_interval_program_closed (A : PR 3) (mu : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run A mu (var 0) (var 1) (var 2) ≐ output A mu (var 0) (var 1) (var 2)) := closeUniv 3 (program_at _ _ _ _ _)
theorem actual_returned_original_interval_width_closed (A : PR 3) (mu : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (RationalValueBounds.radius (fstT (sndT (run A mu (var 0) (var 1) (var 2)))) (fstT (run A mu (var 0) (var 1) (var 2)))
      (succ two) ((two*two)*scale (var 1))) := closeUniv 3 (returned_width _ _ _ _ _)
theorem actual_returned_original_interval_lower_closed (A : PR 3) (mu : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (continuity A mu (var 0) (var 2) ⟶ RationalCubeMinimum.presentedCube (var 3) (var 0) ⟶
      RationalValueBounds.upper (fstT (run A mu (var 0) (var 1) (var 2))) (RationalCubeMinimum.sample A (var 3) (var 4) (var 2)) one (scale (var 4))) :=
  closeUniv 5 (.impI (.impI (returned_lower_sample _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.RationalCubeInfimumIntervals
