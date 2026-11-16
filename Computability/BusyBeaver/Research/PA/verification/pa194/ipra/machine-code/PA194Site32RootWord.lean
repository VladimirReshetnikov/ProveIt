import PA194Site32HeaderTo64
import PA194State42Boundary
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site32RootWord
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194Site32HeaderTo64 PA194State42Boundary PA194Path27Header PA194UnaryRuns PA194StateOne PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem secondRootWord (w : M) :
    let y0 := (w+w)+(w+w)
    let y1 := y0+y0+1
    let y2 := y1+y1+1
    let t := (1 : M)+y2+y2
    let t1 := t+t
    let t2 := t1+t1
    let t3 := t2+t2
    let t4 := t3+t3
    modelWord (PA194SourceProgram.path 32) (w+w) = t4+1 := by
  have heq : (1 : M)+((w+w)+(w+w))+((w+w)+(w+w)) =
      ((w+w)+(w+w))+((w+w)+(w+w))+1 := by ac_rfl
  have h := PA194Path32Header.path32Word w
  dsimp only at h ⊢
  rw [←heq]
  exact h
#print axioms secondRootWord
end models
end PA194Site32RootWord
