import PA194ModelMPPair
import PA194ModelMPTransfer
import PA194MPLiteralRows3554
import PA194MPLiteralRows3621

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false

namespace PA194ModelMPPush
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open PA194SchedulerFetchPositive PA194ModelMPDrain PA194ModelMPTransfer PA194MPLiteralRows

structure Rows (base : Nat) : Prop where
  takeTop : TransferRows base (base+3) 1 6
  takeStack : TransferRows (base+3) (base+6) 2 1
  packPair : PA194ModelMPPair.Rows (base+6)
  storeStack : TransferRows (base+16) (base+19) 7 2

theorem entryRows : Rows 3568 :=
  ⟨⟨by decide,s3568,s3569,s3570⟩,⟨by decide,s3571,s3572,s3573⟩,
    ⟨by decide,s3574,s3575,s3576,s3577,s3578,s3579,s3580,s3581,s3582,s3583⟩,
    ⟨by decide,s3584,s3585,s3586⟩⟩

theorem successRows : Rows 3634 :=
  ⟨⟨by decide,s3634,s3635,s3636⟩,⟨by decide,s3637,s3638,s3639⟩,
    ⟨by decide,s3640,s3641,s3642,s3643,s3644,s3645,s3646,s3647,s3648,s3649⟩,
    ⟨by decide,s3650,s3651,s3652⟩⟩

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def pushed (a : Fin 11 → M) : Fin 11 → M :=
  Function.update (Function.update a 1 0) 2 (cantor (a 1) (a 2))

/-- The two PA194 MP pushes share the same literal 19-row instruction pattern. -/
theorem push (base : Nat) (rows : Rows base) (a : Fin 11 → M) (tail : M)
    (hX : a 6 = 0) (hY : a 7 = 0) :
    ReachesPositive (sourceState base a tail) (sourceState (base+19) (pushed a) tail) := by
  let a1 := transferArgs a 1 6
  let a2 := transferArgs a1 2 1
  let a3 := PA194ModelMPPair.values a2 0 0 (cantor (a2 6) (a2 1))
  have h1 := transfer base (base+3) 1 6 rows.takeTop (by decide) a tail
  have h2 := transfer (base+3) (base+6) 2 1 rows.takeStack (by decide) a1 tail
  have hY' : a2 7 = (0 : M) := by simp [a2,a1,transferArgs,location,hY]
  have h3 := PA194ModelMPPair.pair (base+6) rows.packPair a2 tail hY'
  have h4 := transfer (base+16) (base+19) 7 2 rows.storeStack (by decide) a3 tail
  have hout : transferArgs a3 7 2 = pushed a := by
    funext i
    fin_cases i <;> simp [a3,a2,a1,transferArgs,location,PA194ModelMPPair.values,pushed,hX,hY]
  rw [hout] at h4
  exact appendPositive (append (append h1.reaches h2.reaches) h3.reaches) h4

#print axioms push
end models
end PA194ModelMPPush
