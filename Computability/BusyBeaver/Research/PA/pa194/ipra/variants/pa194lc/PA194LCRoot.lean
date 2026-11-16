import PA194LCPhysical
import PA194TrieRoot
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194LCRoot
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194CompressedSourceFrame (args)
open PA194SourceControllerCode PA194Path27Header PA194UnaryRuns PA194ZeroRuns PA194FiniteControls PA194HalfDiv PA194StateOne
open ConPA.Machine ConPA.Machine.Compressed
open M6.Runtime

abbrev sourceRootCode : Code 4 := PA194TrieRoot.sourceRootCode PA194LCData.path

theorem path_short (i : Nat) : (PA194LCData.path i).length ≤ 48 := by
  exact PA194TrieRoot.path_short PA194LCData.sourceTrie (by decide +kernel) i

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem root_eval (gap : M) (box : BoxSt → M) (i extra : Nat) (effect : Eff) :
    PA194LCPhysical.root gap box i extra effect =
      ⟪(24 : M),(1 : M),modelWord (PA194LCData.path i)
        (F zeros ![gap+modelNumeral M (48+extra-(PA194LCData.path i).length),
          F pushOne (fun _ => box (.plain effect))])⟫ :=
  PA194TrieRoot.root_eval PA194LCData.path PA194LCData.denseControl PA194LCPhysical.rootControl gap box i extra effect

theorem root_advanced_gap (gap : M) (box : BoxSt → M) (i : Nat) (effect : Eff) :
    PA194LCPhysical.root gap box i 1 effect = PA194LCPhysical.root (gap + 1) box i 0 effect :=
  PA194TrieRoot.root_advanced_gap PA194LCData.path PA194LCData.denseControl PA194LCPhysical.rootControl path_short gap box i effect

theorem root_initial_file (gap : M) (box : BoxSt → M) (i : Nat) (effect : Eff) :
    PA194LCPhysical.root gap box i 0 effect =
      PA194LCPhysical.root gap (fun _ => box (.plain effect)) i :=
  PA194TrieRoot.root_initial_file PA194LCData.path PA194LCData.denseControl PA194LCPhysical.rootControl gap box i effect

theorem sourceRoot_eval (s gap count spare : M) (i : Fin 3673)
    (hpc : F pc ![s] = modelNumeral M i.val) :
    F sourceRootCode ![s,gap,count,spare] =
      PA194LCPhysical.root gap (fun _ => F PA194RegisterPermutation.sourceFileCode (args s count spare)) i.val :=
  PA194TrieRoot.sourceRoot_eval PA194LCData.path PA194LCData.denseControl PA194LCPhysical.rootControl s gap count spare i hpc

#print axioms path_short
#print axioms sourceRoot_eval
#print axioms root_advanced_gap
end models
end PA194LCRoot
