import IPRABridge.Standard
import DiophantineConsistency.IPRAExplicitZFCFinal
import DiophantineConsistency.IPRANineCurrent

/-! Exact ConciseIPRA exports of the two nine-variable ZFC consistency equations.
The first comes from the compiled enumerator and the second from the quartic
gates of the maintained equation. Both use the same Foundation refutation
predicate. -/

set_option autoImplicit false
noncomputable section

namespace IPRABridge.Checks.ZFCEquations

open LO LO.FirstOrder LeanProofs.ConciseIPRA
open scoped LO.FirstOrder
open DiophantineConsistency
open IPRAFoundationZFCMappedNegation (mappedNativeRefutation)

/-- The selected Foundation ZFC consistency sentence in the Concise language. -/
def consistency : Fm PTm 0 :=
  toConciseSentence (∼mappedNativeRefutation PRALanguage.embedding)

/-- The no-zero formula of the compiled enumerator's exact nine-variable equation. -/
def explicitNoZero : Fm PTm 0 :=
  toConciseSentence (IPRAExpressionNative.nativeNoZero ExplicitZFCSyntax.expression)

/-- The no-zero formula of the exact nine-variable quartic-gate equation. -/
def currentNoZero : Fm PTm 0 :=
  toConciseSentence (IPRAExpressionNative.nativeNoZero IPRANineCurrent.expression)

theorem explicit_equivalence : Prf PRAAx [] (Fm.iff explicitNoZero consistency) :=
  standardToConcise IPRAExplicitZFCFinal.standard_equivalence

theorem current_equivalence : Prf PRAAx [] (Fm.iff currentNoZero consistency) :=
  standardToConcise IPRANineCurrent.standard_equivalence

#print axioms explicit_equivalence
#print axioms current_equivalence

end IPRABridge.Checks.ZFCEquations
