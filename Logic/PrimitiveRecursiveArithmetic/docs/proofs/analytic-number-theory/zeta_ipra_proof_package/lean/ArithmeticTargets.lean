import ConciseIPRA.NativeBiInterpretation

/-!
The deep-embedding endpoint, not a claimed proof of zeta theory.
STATUS: uncompiled candidate against repository f7e5eac0a94a0e690a22cbeecc5f6cca9270e6df.

A fixed finite rational residual checker is compiled to `PR 1`, taking
one code packing all rational inputs, chart bounds and precision. It returns
zero for invalid domain data, and zero for a valid inequality; thus the
closed target expresses the universally quantified domain implication.
For named inputs a fixed name program is inlined, and its regularity/domain
certificates remain explicit hypotheses. No PR universal evaluator is used.
-/
namespace ZetaIPRA.Object
open LeanProofs.ConciseIPRA
open LeanProofs.ConciseIPRA.Syn
open scoped LeanProofs.ConciseIPRA.Fm

/-- A fixed checker symbol, not its proof or a semantic evaluator. -/
def residualBody (checker : PR 1) : Fm PTm 1 :=
  (PTm.app checker (fun _ => (PTm.var 0 : PTm 1))) ≐ PTm.zero

def residualSentence (checker : PR 1) : Fm PTm 0 :=
  Fm.all (residualBody checker)

def RequiredDerivation (checker : PR 1) : Prop :=
  Prf PRAAx [] (residualSentence checker)

/-- This transports an already completed object proof. It does not supply it. -/
theorem native_of_completed
    (checker : PR 1) (h : RequiredDerivation checker) :
    NPrf [] (NFm.ofPRA (residualSentence checker)) := by
  exact (pra_iff_native).mp h

-- Future completion: construct each checker by PR constructors, prove its
-- decoding meaning, and supply RequiredDerivation checker without assuming
-- that conclusion. The manuscript's obligation table specifies each case.
#print axioms native_of_completed

end ZetaIPRA.Object
