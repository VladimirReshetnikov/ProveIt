import IPRADerivations.Analysis.Names.Rates.Reciprocals.GaussianNamedInverseRate

/-!
# Exact composition of independent Gaussian observation rates

The two genuine rate observations meet at an arbitrary original middle
query. Its two dyadic errors are removed at the existing explicit finite
rational gap query. No regularity or limit premise is needed in addition
to the two supplied independent rates.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedRateComposition

open_ipra
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator rate_at denominator_positive shift_independent_rate)
open GaussianRationalMetric (qsub distanceBounded)
open GaussianRationalHorner (positive_product)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def leadingNumerator (A B C E : PTm n) : PTm n := A*E+C*B
def leadingDenominator (B E : PTm n) : PTm n := B*E

ipra_subst leadingNumerator
ipra_subst leadingDenominator

theorem observation_slack (F G H : PR 2) (x y z A B C E p q t : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hE : Γ ⊢[PRAAx] le one E)
    (hf : Γ ⊢[PRAAx] independentRate F G x y A B) (hg : Γ ⊢[PRAAx] independentRate G H y z C E) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (qsub (ap2 F p x) (ap2 H q z))
      (rateNumerator (leadingNumerator A B C E) (leadingDenominator B E) p q)
      (rateDenominator (leadingDenominator B E) p q) two t := by
  have left := rate_at F G x y A B p t hf
  have right := rate_at G H y z C E t q hg
  have lb := denominator_positive B p t hB
  have rb := denominator_positive E t q hE
  have joined := GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ lb rb left right
  have nb := positive_product _ _ (denominator_positive (leadingDenominator B E) p q (positive_product _ _ hB hE)) (unit_positive t)
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ lb rb) nb
    (le_of_eq_add (d := zero) (by dsimp only [rateNumerator,rateDenominator,leadingNumerator,leadingDenominator]; unfold unit; ipra_ring)) joined

def gapQuery (F H : PR 2) (x z A B C E p q : PTm n) : PTm n :=
  GaussianRationalSlackRemoval.precision (qsub (ap2 F p x) (ap2 H q z))
    (rateNumerator (leadingNumerator A B C E) (leadingDenominator B E) p q)
    (rateDenominator (leadingDenominator B E) p q) two

theorem independent_at (F G H : PR 2) (x y z A B C E p q : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hE : Γ ⊢[PRAAx] le one E)
    (hf : Γ ⊢[PRAAx] independentRate F G x y A B) (hg : Γ ⊢[PRAAx] independentRate G H y z C E) : Γ ⊢[PRAAx]
    distanceBounded (ap2 F p x) (ap2 H q z)
      (rateNumerator (leadingNumerator A B C E) (leadingDenominator B E) p q)
      (rateDenominator (leadingDenominator B E) p q) :=
  GaussianRationalSlackRemoval.slack_removal_at _ _ _ two
    (denominator_positive _ _ _ (positive_product _ _ hB hE))
    (observation_slack F G H x y z A B C E p q (gapQuery F H x z A B C E p q) hB hE hf hg)

theorem compose (F G H : PR 2) (x y z A B C E : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hE : Γ ⊢[PRAAx] le one E)
    (hf : Γ ⊢[PRAAx] independentRate F G x y A B) (hg : Γ ⊢[PRAAx] independentRate G H y z C E) : Γ ⊢[PRAAx]
    independentRate F H x z (leadingNumerator A B C E) (leadingDenominator B E) := by
  refine .allI (.allI ?_)
  let sh (v : PTm n) := Syn.shift (Syn.shift v)
  have bs := Order.shift_one_le (Order.shift_one_le hB)
  have es := Order.shift_one_le (Order.shift_one_le hE)
  have fs := shift_independent_rate (shift_independent_rate hf)
  have gs := shift_independent_rate (shift_independent_rate hg)
  simpa only [independentRate,Syn.shift,subst_leadingNumerator,subst_leadingDenominator,sh] using
    independent_at F G H (sh x) (sh y) (sh z) (sh A) (sh B) (sh C) (sh E) (var 1) (var 0) bs es fs gs

theorem same_denominator_at (F G H : PR 2) (x y z A B C p q : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hf : Γ ⊢[PRAAx] independentRate F G x y A B)
    (hg : Γ ⊢[PRAAx] independentRate G H y z C B) : Γ ⊢[PRAAx]
    distanceBounded (ap2 F p x) (ap2 H q z) (rateNumerator (A+C) B p q) (rateDenominator B p q) :=
  distance_radius_mono _ _ _ _ _ _ (denominator_positive _ _ _ (positive_product _ _ hB hB)) (denominator_positive B p q hB)
    (le_of_eq_add (d := zero) (by unfold leadingNumerator leadingDenominator rateNumerator rateDenominator; ipra_ring))
    (independent_at F G H x y z A B C B p q hB hB hf hg)

theorem same_denominator (F G H : PR 2) (x y z A B C : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hf : Γ ⊢[PRAAx] independentRate F G x y A B)
    (hg : Γ ⊢[PRAAx] independentRate G H y z C B) : Γ ⊢[PRAAx] independentRate F H x z (A+C) B := by
  refine .allI (.allI ?_)
  let sh (v : PTm n) := Syn.shift (Syn.shift v)
  have bs := Order.shift_one_le (Order.shift_one_le hB)
  have fs := shift_independent_rate (shift_independent_rate hf)
  have gs := shift_independent_rate (shift_independent_rate hg)
  simpa only [independentRate,Syn.shift,PTm.subst_add,sh] using
    same_denominator_at F G H (sh x) (sh y) (sh z) (sh A) (sh B) (sh C) (var 1) (var 0) bs fs gs

theorem symmetric (F G : PR 2) (x y A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] independentRate F G x y A B) : Γ ⊢[PRAAx] independentRate G F y x A B := by
  refine .allI (.allI ?_)
  let sh (v : PTm n) := Syn.shift (Syn.shift v)
  have bs := Order.shift_one_le (Order.shift_one_le hB)
  have hs := shift_independent_rate (shift_independent_rate h)
  have obs := distance_symmetric _ _ _ _ (denominator_positive _ _ _ bs) (rate_at F G (sh x) (sh y) (sh A) (sh B) (var 0) (var 1) hs)
  have swapped : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
      distanceBounded (ap2 G (var 1) (sh y)) (ap2 F (var 0) (sh x))
        (rateNumerator (sh A) (sh B) (var 1) (var 0)) (rateDenominator (sh B) (var 1) (var 0)) :=
    distance_congr (.eqRefl _) (.eqRefl _) (by unfold rateNumerator; ipra_ring) (by unfold rateDenominator; ipra_ring) obs
  simpa only [independentRate,Syn.shift,sh] using swapped

theorem actual_independent_rate_composition_closed (F G H : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    ((le one (var 4) ⋏ (le one (var 6) ⋏ (independentRate F G (var 0) (var 1) (var 3) (var 4) ⋏
      independentRate G H (var 1) (var 2) (var 5) (var 6)))) ⟶
      independentRate F H (var 0) (var 2) (leadingNumerator (var 3) (var 4) (var 5) (var 6)) (leadingDenominator (var 4) (var 6))) :=
  closeUniv 7 (.impI (compose F G H _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

theorem actual_same_denominator_rate_composition_closed (F G H : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((le one (var 4) ⋏ (independentRate F G (var 0) (var 1) (var 3) (var 4) ⋏ independentRate G H (var 1) (var 2) (var 5) (var 4))) ⟶
      independentRate F H (var 0) (var 2) (var 3+var 5) (var 4)) :=
  closeUniv 6 (.impI (same_denominator F G H _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianNamedRateComposition
