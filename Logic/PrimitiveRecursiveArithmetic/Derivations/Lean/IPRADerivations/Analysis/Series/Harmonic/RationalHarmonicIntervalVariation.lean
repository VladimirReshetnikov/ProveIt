import IPRADerivations.Analysis.Series.Harmonic.RationalHarmonicInterval
import IPRADerivations.AnalyticNumberTheory.LogElementary

/-!
# Finite harmonic interval variation on an original positive-time domain

The old exact reciprocal rectangle bound controls differences at the
actual common-refinement endpoints. Only original numerical positivity,
a lower time bound and a cleared original time-distance are inputs.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalHarmonicIntervalVariation

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicChebyshev (S_mono)
open RationalHarmonicInterval (common numerator horizon interval)
open Products (fact)
open GammaEulerMesh (factorial_positive)
open RationalValueBounds (upper radius radius_of_upper)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The old native rectangle estimate weakened to its left endpoint. -/
theorem harmonic_increment (u v F : PTm n) (hvu : Γ ⊢[PRAAx] le v u) : Γ ⊢[PRAAx]
    le (v*S u F) (v*S v F+monus u v*F) := by
  have split := eq_add_of_le hvu
  have old := AnalyticNumberTheory.LogElementary.log_upper (Γ := Γ) v (monus u v) F
  have sums := congrAp2 (sumF hB) split.eqSymm (.eqRefl F)
  have old' := le_congr (congrMul (.eqRefl _) sums) (.eqRefl _) old
  have mono := S_mono F hvu
  ipra_le sl old'+sl mono

private theorem common_upper (a b c d Q P L A D : PTm n)
    (h : Γ ⊢[PRAAx] le (D*(S (Q*a) (fact L)+S (P*d) (fact L)))
      (D*(S (Q*b) (fact L)+S (P*c) (fact L))+A*fact L)) : Γ ⊢[PRAAx]
    upper (common a b Q L) (common c d P L) A D := by
  let F := fact L
  apply RationalCubeInfimumIntervals.upper_of_representations (common a b Q L) (common c d P L)
    (numerator a b Q L) (numerator c d P L) F F A D (factorial_positive L) (factorial_positive L)
    (RationalHarmonicInterval.common_value a b Q L) (RationalHarmonicInterval.common_value c d P L)
  apply zle_of_toZ (F*monus (D*(S (Q*b) F+S (P*c) F)+A*F) (D*(S (Q*a) F+S (P*d) F)))
  have e := natEq (eq_add_of_le h)
  simp only [ZT.toZ_mul,ZT.toZ_sub,ZT.toZ_ofNat]
  simp only [numerator,ZT.toZ]
  ipra_simps
  linear_combination -𝔞 F*e

/-- The exact finite ordered relative-time variation estimate at the
actual common-refinement meshes dQ and bQ. -/
theorem ordered_common_variation (a b c d Q M A D L : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hd : Γ ⊢[PRAAx] le one d) (hQ : Γ ⊢[PRAAx] le one Q)
    (horder : Γ ⊢[PRAAx] le (a*d) (b*c))
    (hlower : Γ ⊢[PRAAx] le b (M*a))
    (hclose : Γ ⊢[PRAAx] le (D*monus (b*c) (a*d)) (A*b*d)) : Γ ⊢[PRAAx]
    radius (common a b (d*Q) L) (common c d (b*Q) L) (M*A) D := by
  let u := Q*(b*c)
  let v := Q*(a*d)
  let w := Q*(b*d)
  let F := fact L
  have hv : Γ ⊢[PRAAx] le one v := RationalAlgebra.positive_product hQ (RationalAlgebra.positive_product ha hd)
  have vu : Γ ⊢[PRAAx] le v u := AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl Q) horder
  have delta : Γ ⊢[PRAAx] monus u v ≐ Q*monus (b*c) (a*d) := by
    have equation : Γ ⊢[PRAAx] u ≐ v+Q*monus (b*c) (a*d) :=
      (congrMul (.eqRefl Q) (eq_add_of_le horder)).eqTrans (by dsimp [u,v]; ipra_ring)
    exact (congrMonus equation (.eqRefl v)).eqTrans (add_monus' _ _)
  have first : Γ ⊢[PRAAx] le (D*monus u v) (A*(Q*b*d)) :=
    le_congr (by
      have e := natEq delta
      apply deriveNat; ipra_simps; rw [e]; ring) (by ipra_ring) (mul_le_mul_right Q hclose)
  have second : Γ ⊢[PRAAx] le (A*(Q*b*d)) ((M*A)*v) :=
    le_congr (by ipra_ring) (by dsimp [v]; ipra_ring) (mul_le_mul_right (A*Q*d) hlower)
  have times := mul_le_mul_right D (harmonic_increment u v F vu)
  have endpoint := mul_le_mul_right F (le_trans first second)
  have clear : Γ ⊢[PRAAx] le (v*(D*S u F)) (v*(D*S v F+(M*A)*F)) := by
    ipra_le sl times+sl endpoint
  have distance := RationalValueBounds.positive_cancel hv clear
  have mono := AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl D) (S_mono F vu)
  have rev : Γ ⊢[PRAAx] le (D*S v F) (D*S u F+(M*A)*F) := le_trans mono (le_add_right _ _)
  have eu : Γ ⊢[PRAAx] S ((b*Q)*c) F ≐ S u F := congrAp2 (sumF hB) (by dsimp [u]; ipra_ring) (.eqRefl _)
  have ev : Γ ⊢[PRAAx] S ((d*Q)*a) F ≐ S v F := congrAp2 (sumF hB) (by dsimp [v]; ipra_ring) (.eqRefl _)
  have ew : Γ ⊢[PRAAx] S ((b*Q)*d) F ≐ S w F := congrAp2 (sumF hB) (by dsimp [w]; ipra_ring) (.eqRefl _)
  have ex : Γ ⊢[PRAAx] S ((d*Q)*b) F ≐ S w F := congrAp2 (sumF hB) (by dsimp [w]; ipra_ring) (.eqRefl _)
  have revWith : Γ ⊢[PRAAx] le (D*(S v F+S w F)) (D*(S w F+S u F)+(M*A)*F) :=
    le_congr (by ipra_ring) (by ipra_ring) (add_le_add_right (D*S w F) rev)
  have distWith : Γ ⊢[PRAAx] le (D*(S u F+S w F)) (D*(S w F+S v F)+(M*A)*F) :=
    le_congr (by ipra_ring) (by ipra_ring) (add_le_add_right (D*S w F) distance)
  have forward : Γ ⊢[PRAAx] le (D*(S ((d*Q)*a) F+S ((b*Q)*d) F))
      (D*(S ((d*Q)*b) F+S ((b*Q)*c) F)+(M*A)*F) :=
    le_congr (congrMul (.eqRefl _) (congrAdd ev ew)).eqSymm
      (congrAdd (congrMul (.eqRefl _) (congrAdd ex eu)) (.eqRefl _)).eqSymm revWith
  have backward : Γ ⊢[PRAAx] le (D*(S ((b*Q)*c) F+S ((d*Q)*b) F))
      (D*(S ((b*Q)*d) F+S ((d*Q)*a) F)+(M*A)*F) :=
    le_congr (congrMul (.eqRefl _) (congrAdd eu ex)).eqSymm
      (congrAdd (congrMul (.eqRefl _) (congrAdd ew ev)) (.eqRefl _)).eqSymm distWith
  exact radius_of_upper _ _ _ _ (common_upper a b c d (d*Q) (b*Q) L (M*A) D forward)
    (common_upper c d a b (b*Q) (d*Q) L (M*A) D backward)


def gap (a b c d : PTm n) : PTm n := monus (a*d) (b*c)+monus (b*c) (a*d)
ipra_subst gap

theorem common_variation (a b c d Q M A D L : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b)
    (hc : Γ ⊢[PRAAx] le one c) (hd : Γ ⊢[PRAAx] le one d) (hQ : Γ ⊢[PRAAx] le one Q)
    (hl : Γ ⊢[PRAAx] le b (M*a)) (hr : Γ ⊢[PRAAx] le d (M*c))
    (hclose : Γ ⊢[PRAAx] le (D*gap a b c d) (A*b*d)) : Γ ⊢[PRAAx]
    radius (common a b (d*Q) L) (common c d (b*Q) L) (M*A) D := by
  refine .orE (le_total (a*d) (b*c)) ?_ ?_
  · have e : le (a*d) (b*c)::Γ ⊢[PRAAx] gap a b c d ≐ monus (b*c) (a*d) :=
      (congrAdd Prf.hyp0 (.eqRefl _)).eqTrans (zero_add _)
    have close := le_congr (congrMul (.eqRefl _) e) (.eqRefl _) hclose.wk
    exact ordered_common_variation a b c d Q M A D L ha.wk hd.wk hQ.wk Prf.hyp0 hl.wk close
  · have e : le (b*c) (a*d)::Γ ⊢[PRAAx] gap a b c d ≐ monus (d*a) (c*b) :=
      ((congrAdd (.eqRefl _) Prf.hyp0).eqTrans (add_zero _)).eqTrans (congrMonus (mul_comm _ _) (mul_comm _ _))
    have close : le (b*c) (a*d)::Γ ⊢[PRAAx] le (D*monus (d*a) (c*b)) (A*d*b) :=
      le_congr (congrMul (.eqRefl _) e) (by ipra_ring) hclose.wk
    have order : le (b*c) (a*d)::Γ ⊢[PRAAx] le (c*b) (d*a) := le_congr (mul_comm _ _) (mul_comm _ _) Prf.hyp0
    exact RationalValueBounds.radius_symmetric _ _ _ _
      (ordered_common_variation c d a b Q M A D L hc.wk hb.wk hQ.wk order hr.wk close)

/-- The actual unrefined finite values obey the exact relative-time
variation bound M*A/D + 2/Q, with only original time data as inputs. -/
theorem finite_variation (a b c d Q M A D : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b)
    (hc : Γ ⊢[PRAAx] le one c) (hd : Γ ⊢[PRAAx] le one d)
    (hQ : Γ ⊢[PRAAx] le one Q) (hD : Γ ⊢[PRAAx] le one D)
    (hl : Γ ⊢[PRAAx] le b (M*a)) (hr : Γ ⊢[PRAAx] le d (M*c))
    (hclose : Γ ⊢[PRAAx] le (D*gap a b c d) (A*b*d)) : Γ ⊢[PRAAx]
    radius (interval a b Q) (interval c d Q) ((M*A)*Q+two*D) (D*Q) := by
  let L := Q*(a*d+b*c+b*d)
  have leftH : Γ ⊢[PRAAx] le (horizon a b (d*Q)) L :=
    le_of_eq_add (d := Q*b*c) (by dsimp [horizon,L]; ipra_ring)
  have rightH : Γ ⊢[PRAAx] le (horizon c d (b*Q)) L :=
    le_of_eq_add (d := Q*a*d) (by dsimp [horizon,L]; ipra_ring)
  have middle := RationalValueBounds.radius_congr (RationalHarmonicInterval.at_common a b (d*Q) L leftH)
    (RationalHarmonicInterval.at_common c d (b*Q) L rightH) (.eqRefl _) (.eqRefl _)
    (common_variation a b c d Q M A D L ha hb hc hd hQ hl hr hclose)
  have left := RationalValueBounds.radius_symmetric _ _ _ _ (RationalHarmonicInterval.refinement a b Q d ha hb hQ hd)
  have right := RationalHarmonicInterval.refinement c d Q b hc hd hQ hb
  have total := RationalValueBounds.radius_triangle _ _ _ (one*D+(M*A)*Q) (Q*D) one Q
    (RationalValueBounds.radius_triangle _ _ _ one Q (M*A) D left middle) right
  exact RationalValueBounds.radius_mono _ _ _ _ ((M*A)*Q+two*D) (D*Q)
    (RationalAlgebra.positive_product (RationalAlgebra.positive_product hQ hD) hQ) total
    (le_of_eq_add (d := zero) (by ipra_ring))


def input (a b c d Q M A D : PTm n) : Fm PTm n :=
  (le one a ⋏ (le one b ⋏ (le one c ⋏ (le one d ⋏ (le one Q ⋏ le one D))))) ⋏
    ((le b (M*a) ⋏ le d (M*c)) ⋏ le (D*gap a b c d) (A*b*d))
def tolerance (Q M A D : PTm n) : PTm n := (M*A)*Q+two*D
def toleranceDen (Q D : PTm n) : PTm n := D*Q
def output (a b c d Q M A D : PTm n) : PTm n := pairT (interval a b Q)
  (pairT (interval c d Q) (pairT (tolerance Q M A D) (toleranceDen Q D)))
def outputF : PR 8 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))
def run (a b c d Q M A D : PTm n) : PTm n := PTm.app outputF ![a,b,c,d,Q,M,A,D]
ipra_subst tolerance
ipra_subst toleranceDen
ipra_subst output

theorem program_at (a b c d Q M A D : PTm n) : Γ ⊢[PRAAx] run a b c d Q M A D ≐ output a b c d Q M A D := by
  simpa [run,outputF] using toPR_eq (Γ := Γ)
    (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) : PTm 8) ![a,b,c,d,Q,M,A,D]
theorem from_input (a b c d Q M A D : PTm n) (h : Γ ⊢[PRAAx] input a b c d Q M A D) : Γ ⊢[PRAAx]
    radius (interval a b Q) (interval c d Q) (tolerance Q M A D) (toleranceDen Q D) :=
  finite_variation a b c d Q M A D h.andE₁.andE₁ h.andE₁.andE₂.andE₁ h.andE₁.andE₂.andE₂.andE₁
    h.andE₁.andE₂.andE₂.andE₂.andE₁ h.andE₁.andE₂.andE₂.andE₂.andE₂.andE₁
    h.andE₁.andE₂.andE₂.andE₂.andE₂.andE₂ h.andE₂.andE₁.andE₁ h.andE₂.andE₁.andE₂ h.andE₂.andE₂

theorem returned_left (a b c d Q M A D : PTm n) : Γ ⊢[PRAAx] fstT (run a b c d Q M A D) ≐ interval a b Q :=
  (program_at a b c d Q M A D).fstE
theorem returned_coarse_tail (a b c d Q M A D : PTm n) : Γ ⊢[PRAAx] sndT (run a b c d Q M A D) ≐
    pairT (interval c d Q) (pairT (tolerance Q M A D) (toleranceDen Q D)) :=
  (program_at a b c d Q M A D).sndE
theorem returned_right (a b c d Q M A D : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run a b c d Q M A D)) ≐ interval c d Q :=
  (returned_coarse_tail a b c d Q M A D).fstE
theorem returned_budget_tail (a b c d Q M A D : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run a b c d Q M A D)) ≐
    pairT (tolerance Q M A D) (toleranceDen Q D) :=
  (returned_coarse_tail a b c d Q M A D).sndE
theorem returned_numerator (a b c d Q M A D : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run a b c d Q M A D))) ≐ tolerance Q M A D :=
  (returned_budget_tail a b c d Q M A D).fstE
theorem returned_denominator (a b c d Q M A D : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run a b c d Q M A D))) ≐ toleranceDen Q D :=
  (returned_budget_tail a b c d Q M A D).sndE
theorem returned_radius (a b c d Q M A D : PTm n) (h : Γ ⊢[PRAAx] input a b c d Q M A D) : Γ ⊢[PRAAx]
    radius (fstT (run a b c d Q M A D)) (fstT (sndT (run a b c d Q M A D)))
      (fstT (sndT (sndT (run a b c d Q M A D)))) (sndT (sndT (sndT (run a b c d Q M A D)))) :=
  RationalValueBounds.radius_congr (returned_left a b c d Q M A D).eqSymm (returned_right a b c d Q M A D).eqSymm
    (returned_numerator a b c d Q M A D).eqSymm (returned_denominator a b c d Q M A D).eqSymm (from_input a b c d Q M A D h)

theorem original_harmonic_increment_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (var 1) (var 0) ⟶ le (var 1*S (var 0) (var 2)) (var 1*S (var 1) (var 2)+monus (var 0) (var 1)*var 2)) :=
  closeUniv 3 (.impI (harmonic_increment _ _ _ Prf.hyp0))
theorem actual_finite_harmonic_interval_variation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      radius (interval (var 0) (var 1) (var 4)) (interval (var 2) (var 3) (var 4))
        (tolerance (var 4) (var 5) (var 6) (var 7)) (toleranceDen (var 4) (var 7))) :=
  closeUniv 8 (.impI (from_input _ _ _ _ _ _ _ _ Prf.hyp0))
theorem actual_harmonic_interval_variation_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ≐
      output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)) := closeUniv 8 (program_at _ _ _ _ _ _ _ _)
theorem actual_returned_harmonic_interval_variation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      radius (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)))
        (fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))))
        (fstT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)))))
        (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)))))) :=
  closeUniv 8 (.impI (returned_radius _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.RationalHarmonicIntervalVariation
