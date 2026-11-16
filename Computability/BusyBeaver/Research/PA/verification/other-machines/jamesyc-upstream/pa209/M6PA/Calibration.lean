module
public import M6PA.NativeSoundness
public import M6.ZeroStackSafety
@[expose] public section
namespace M6.PA
open NativeCalculus FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
/-- Ordinary first-order PA consistency rules out a finite native refutation.
    This is a theorem using the rebuilt native-to-PA interpretation, not a new
    axiom and not a claim about consistency of Lean. -/
theorem no_native_refutation (hcons : Consistent) : ¬ Proved 1 := by
  letI : FFL.Entailment.Consistent theory := hcons
  intro h
  have hbot : theory ⊬ (⊥ : ArithmeticSentence) :=
    FFL.Entailment.Consistent.not_bot
  exact hbot (NativeHFS.native_refutation_PA_bottom h)

theorem actual_words_safe (hcons : Consistent) (cs : List Source.Enumeration.Command) :
    ∃ out, Source.commandsEval cs ZeroStackSafety.zeroStore = some out ∧
      ZeroStackSafety.SoundStore out :=
  ZeroStackSafety.words_safe (no_native_refutation hcons) cs _ ZeroStackSafety.zero_sound
#print axioms no_native_refutation
#print axioms actual_words_safe
end M6.PA
