import PA194HalfFileScan
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194HalfFileWithTail
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194RegisterFile PA194UnaryRuns PA194BinaryDouble BinaryTapeCodes
open PA194HalfFileScan PRAModelIOpenPairing TableDispatch
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

/-- When at least one file block remains, its separator makes the remaining
file even for any suffix, including nonstandard suffixes. -/
theorem scanHalfBlockWithTail (n q dest : Nat) (e : Fin (n+3) → M) (l p : M)
    (hp : F (fileCode (n+2)) e = p+p)
    (hloop : ∀ x y : M, F PackedClock.encodedStep (fun _ =>
      F pairCode ![modelNumeral M q,F pairCode ![x,y+y+1]]) =
      F pairCode ![modelNumeral M q,F pairCode ![x+x+1,y]])
    (hexit : ∀ x y : M, F PackedClock.encodedStep (fun _ =>
      F pairCode ![modelNumeral M q,F pairCode ![x,y+y]]) =
      F pairCode ![modelNumeral M dest,F pairCode ![x+x,y]]) :
    ∃ r : M, F (fileCode (n+1)) (fun i => e i.succ) = r+r ∧
      let x := F ones ![e 0+1,l]
      F PA194Stepper.stepper ![(e 0+1)+1,F pairCode ![modelNumeral M q,F pairCode ![l,p]]] =
      F pairCode ![modelNumeral M dest,F pairCode ![x+x,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let tail : Fin (n+2) → M := fun i => e i.succ
  let r := F ones ![tail 0+1,F (fileCode n) (fun i => tail i.succ)]
  have hr : F (fileCode (n+1)) tail = r+r := by
    rw [modelFileSucc,modelBlock]
  let a := F ones ![e 0+1,r+r]
  have hf : F (fileCode (n+2)) e = a+a := by
    rw [modelFileSucc,modelBlock,hr]
  rw [hf] at hp
  have hh := congrArg (fun x : M => F halfCode (fun _ => x)) hp
  rw [(modelDouble a).2,(modelDouble p).2] at hh
  subst p
  have hs := PA194GenericRightScan.modelFullScan q hloop (e 0+1) l (r+r)
  refine ⟨r,hr,?_⟩
  dsimp only
  change F PA194Stepper.stepper ![F addCode ![e 0+1,F oneCode Fin.elim0],_] = _
  rw [modelAddOne,PA194Stepper.modelStepperSucc,hs,hexit]

/-- The same suffix-preserving scan, with its exact remaining-file half. -/
theorem scanHalfBlockWithTailExact (n q dest : Nat) (e : Fin (n+3) → M) (l p : M)
    (hp : F (fileCode (n+2)) e = p+p)
    (hloop : ∀ x y : M, F PackedClock.encodedStep (fun _ =>
      F pairCode ![modelNumeral M q,F pairCode ![x,y+y+1]]) =
      F pairCode ![modelNumeral M q,F pairCode ![x+x+1,y]])
    (hexit : ∀ x y : M, F PackedClock.encodedStep (fun _ =>
      F pairCode ![modelNumeral M q,F pairCode ![x,y+y]]) =
      F pairCode ![modelNumeral M dest,F pairCode ![x+x,y]]) :
    let tail : Fin (n+2) → M := fun i => e i.succ
    let r := F ones ![tail 0+1,F (fileCode n) (fun i => tail i.succ)]
    let x := F ones ![e 0+1,l]
    F (fileCode (n+1)) tail = r+r ∧
    F PA194Stepper.stepper ![(e 0+1)+1,F pairCode ![modelNumeral M q,F pairCode ![l,p]]] =
      F pairCode ![modelNumeral M dest,F pairCode ![x+x,r]] := by
  dsimp only
  let tail : Fin (n+2) → M := fun i => e i.succ
  let r := F ones ![tail 0+1,F (fileCode n) (fun i => tail i.succ)]
  have hr : F (fileCode (n+1)) tail = r+r := by rw [modelFileSucc,modelBlock]
  obtain ⟨r',hr',hs⟩ := scanHalfBlockWithTail n q dest e l p hp hloop hexit
  have hh := congrArg (fun x : M => F halfCode (fun _ => x)) (hr'.symm.trans hr)
  rw [(modelDouble r').2,(modelDouble r).2] at hh
  subst r'
  exact ⟨hr,hs⟩
#print axioms scanHalfBlockWithTailExact
#print axioms scanHalfBlockWithTail
end models
end PA194HalfFileWithTail
