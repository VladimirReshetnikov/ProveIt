import BusyBeaver.ZFC.KDecoderSuffix215
import BusyBeaver.ZFC.KTape

/-! One literal K215 leaf, with both decrement outcomes checked from the exact
primitive port. This is two of the 6,176 branch cases, not full suffix coverage. -/
namespace SetTheory.BusyBeaver.ZFC.KDecoderSuffix215Example

open KZip KRuntimeCore KSim KSimPrefix KDecoderPrefix215
open RegisterPath SiteCoverage KTableCore
set_option maxHeartbeats 0
set_option maxRecDepth 65536

def word : List Bool := [false, false, false]
def port : SConf := leafPort [false, false] false 27

theorem literal_leaf : LeafAt KSource215.t215 word (.decnz 8) :=
  .left (.left (.left (.here _)))

/-- The literal prefix is 84 --0--> 95 --0--> 27. Its complete left frame is
retained. No assumptions on the gap or register list are used. -/
theorem decoder_prefix : PrefixSpec tm215 word port := by
  intro n vs
  change Reach tm215 (conc n vs (start word))
    (conc n vs (leafPort [false, false] false 27))
  rw [conc_start, conc_leafPort]
  let rest := List.replicate (n + 61) false ++ true :: sepsR vs
  change Reach tm215 (zc 84 [true] (false :: false :: false :: rest))
    (zc 27 [false, false, true] (false :: rest))
  have first : KZip.step tm215 (zc 84 [true] (false :: false :: false :: rest)) =
      some (zc 95 [false, true] (false :: false :: rest)) := zR (by rfl)
  have second : KZip.step tm215 (zc 95 [false, true] (false :: false :: rest)) =
      some (zc 27 [false, false, true] (false :: rest)) := zR (by rfl)
  exact (Reach.of_step first).trans (Reach.of_step second)

/-- The balanced table has already been proved equal to the literal machine.
This finite check covers the zero and nonzero decrement branches. -/
theorem suffix_checked : checkEdgeFrom tm215 word port (.decnz 8) = true := by
  have hfast : checkEdgeFrom (KBoot.fastOf KBoot215.tt215) word port (.decnz 8) = true := by
    decide +kernel
  have heq : KBoot.fastOf KBoot215.tt215 = tm215 := by
    funext q b
    exact KBoot215.fast215 q b
  simpa only [heq] using hfast

/-- Actual all-natural site semantics for this source leaf. -/
theorem semantic_site : KSim.EdgeSpec tm215 word (.decnz 8) :=
  edgeSpec_of_prefix_checked (KTape.boxLemmas (by decide) (.inr rfl)) decoder_prefix suffix_checked

#print axioms literal_leaf
#print axioms decoder_prefix
#print axioms suffix_checked
#print axioms semantic_site

end SetTheory.BusyBeaver.ZFC.KDecoderSuffix215Example
