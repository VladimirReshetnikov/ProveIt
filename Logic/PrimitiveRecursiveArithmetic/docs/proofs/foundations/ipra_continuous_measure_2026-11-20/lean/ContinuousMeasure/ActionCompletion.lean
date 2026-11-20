import ContinuousMeasure.Presentations

/-!
# A checked extension schedule for quantitative dense actions

The gain and the primitive-recursive modulus must be supplied with their
contracts. This file proves that the explicit arithmetic schedule constructs
regular L1 names and respects the stated equivalence of names.
-/

namespace IPRAContinuousMeasure

theorem dyadic_nonneg (p : Nat) : 0 ≤ dyadic p :=
  Rat.pow_nonneg (by grind)

theorem dyadic_add (p q : Nat) : dyadic (p + q) = dyadic p * dyadic q := by
  induction q with
  | zero => simp [dyadic, Rat.pow_zero]
  | succ q ih =>
      have hp : dyadic (p + (q + 1)) = dyadic (p + q) * (1 / 2 : Rat) := by
        change (1 / 2 : Rat) ^ ((p + q) + 1) = (1 / 2 : Rat) ^ (p + q) * (1 / 2 : Rat)
        exact Rat.pow_succ _ _
      have hq : dyadic (q + 1) = dyadic q * (1 / 2 : Rat) := Rat.pow_succ _ _
      rw [hp, ih, hq, Rat.mul_assoc]

theorem dyadic_two (p : Nat) : dyadic (p + 2) = dyadic p / 4 := by
  rw [dyadic_add]
  have htwo : dyadic 2 = (1 / 4 : Rat) := by
    simp only [dyadic, Rat.pow_succ, Rat.pow_zero]
    grind
  rw [htwo]
  grind

theorem amplitude_reserve : ∀ c : Nat, ((c : Rat) + 1) * dyadic c ≤ 1 := by
  intro c
  induction c with
  | zero =>
      simp only [dyadic, Rat.pow_zero, Rat.mul_one]
      grind
  | succ c ih =>
      have hc : 0 ≤ (c : Rat) := Rat.natCast_nonneg
      have hfac : ((c : Rat) + 2) * (1 / 2 : Rat) ≤ (c : Rat) + 1 := by grind
      have hmul := Rat.mul_le_mul_of_nonneg_right hfac (dyadic_nonneg c)
      have hs : dyadic (c + 1) = dyadic c * (1 / 2 : Rat) := Rat.pow_succ _ _
      rw [hs, Rat.natCast_add]
      grind

theorem amplitude_absorb (c : Nat) : (c : Rat) * dyadic c ≤ 1 := by
  have hfac : (c : Rat) ≤ (c : Rat) + 1 := by grind
  exact Rat.le_trans
    (Rat.mul_le_mul_of_nonneg_right hfac (dyadic_nonneg c)) (amplitude_reserve c)

/-- The deliberately simple offset c is primitive recursive. A binary-length
offset is more efficient, and can replace it after proving the same inequality. -/
theorem gain_at_precision {B : Rat} (c p : Nat) (hB : B ≤ (c : Rat)) :
    B * dyadic (p + c + 2) ≤ dyadic (p + 2) := by
  have hprod := Rat.mul_le_mul_of_nonneg_right (amplitude_absorb c)
    (dyadic_nonneg (p + 2))
  have he : p + c + 2 = (p + 2) + c := by omega
  have hg := Rat.mul_le_mul_of_nonneg_right hB (dyadic_nonneg (p + c + 2))
  rw [he, dyadic_add] at hg
  rw [he, dyadic_add]
  grind

/-- The explicit dense-action sampler is a regular L1 name. -/
theorem action_regular {A B : ProbabilityTower} (T : DenseAction A B)
    (f : RegularL1Name A) (c : Nat) (hc : T.gain ≤ (c : Rat)) :
    ActionRegularityGoal T f c := by
  intro p q
  have h := T.stability (f.sample (p + c + 2)) (f.sample (q + c + 2)) (p + 2) (q + 2)
  have hr := f.regular (p + c + 2) (q + c + 2)
  have hm := Rat.mul_le_mul_of_nonneg_left hr T.gainNonneg
  have hp := gain_at_precision c p hc
  have hq := gain_at_precision c q hc
  have hdp := dyadic_nonneg p
  have hdq := dyadic_nonneg q
  unfold actionSample
  have hep := dyadic_two p
  have heq := dyadic_two q
  grind

def mapName {A B : ProbabilityTower} (T : DenseAction A B)
    (f : RegularL1Name A) (c : Nat) (hc : T.gain ≤ (c : Rat)) : RegularL1Name B where
  sample := actionSample T f c
  regular := action_regular T f c hc

/-- The chosen output name is independent of which equivalent input name is
used. The quantitative statement is the declared `SameL1Name` relation. -/
theorem mapName_respects {A B : ProbabilityTower} (T : DenseAction A B)
    (f g : RegularL1Name A) (c : Nat) (hc : T.gain ≤ (c : Rat))
    (hfg : SameL1Name f g) : SameL1Name (mapName T f c hc) (mapName T g c hc) := by
  intro p
  have h := T.stability (f.sample (p + c + 2)) (g.sample (p + c + 2)) (p + 2) (p + 2)
  have hi := hfg (p + c + 2)
  have hm := Rat.mul_le_mul_of_nonneg_left hi T.gainNonneg
  have hp := gain_at_precision c p hc
  have hd := dyadic_nonneg p
  change SimpleTable.distance (T.run (f.sample (p + c + 2)) (p + 2))
      (T.run (g.sample (p + c + 2)) (p + 2)) ≤ 2 * dyadic p
  have he := dyadic_two p
  grind

/-- Composition retains the product gain and has a fully explicit schedule.
The integer c bounds the OUTER gain. -/
def composeDenseAction {A B C : ProbabilityTower} (T : DenseAction A B)
    (S : DenseAction B C) (c : Nat) (hc : S.gain ≤ (c : Rat)) : DenseAction A C where
  run f p := S.run (T.run f (p + c + 2)) (p + 2)
  gain := S.gain * T.gain
  gainNonneg := Rat.mul_nonneg S.gainNonneg T.gainNonneg
  stability := by
    intro f g p q
    have hs := S.stability (T.run f (p + c + 2)) (T.run g (q + c + 2)) (p + 2) (q + 2)
    have ht := T.stability f g (p + c + 2) (q + c + 2)
    have hm := Rat.mul_le_mul_of_nonneg_left ht S.gainNonneg
    have hp := gain_at_precision c p hc
    have hq := gain_at_precision c q hc
    have hdp := dyadic_nonneg p
    have hdq := dyadic_nonneg q
    have hep := dyadic_two p
    have heq := dyadic_two q
    grind

end IPRAContinuousMeasure
