module
/- M6 PA-model runtime port. This is a fresh append-one/table adaptation;
its theorem scope is not the completed PA-unprovability endpoint. -/
public import PA196.Arithmetic.Machine.PAInternalCarryCode
@[expose] public section

namespace PA196.Arithmetic.Machine.PA.InternalTrace.ReturnCode
open M6
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ScanBits
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma cell_affine (n l : V) :
    repeatBits n 1 (4*l+1) = repeatBits n 0 4*l+repeatBits n 1 1 := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih => rw [repeat_succ,repeat_succ,repeat_succ,ih]; ring1

def affineBlueprint : VecRec.Blueprint 0 where
  nil := .mkSigma “y. !pairDef y 1 0”
  adjoin := .mkSigma “y p xs ih. ∃ a b k c, !pi₁Def a ih ∧ !pi₂Def b ih ∧
    !repeatGraph k p 0 4 ∧ !repeatGraph c p 1 1 ∧ !pairDef y (a*k) (a*c+b)”

noncomputable def affineConstruction : VecRec.Construction V affineBlueprint where
  nil _ := ⟪1,0⟫
  adjoin (_ p _ ih) := ⟪π₁ ih*repeatBits p 0 4,π₁ ih*repeatBits p 1 1+π₂ ih⟫
  nil_defined := .mk fun v => by simp [affineBlueprint]
  adjoin_defined := .mk fun v => by simp [affineBlueprint,repeat_defined.df]

noncomputable def affine (xs : V) : V := affineConstruction.result ![] xs

def affineGraph : 𝚺ᴬ₁.Semisentence 2 := affineBlueprint.resultDef
instance affine_defined : 𝚺ᴬ₁-Function₁ (affine : V → V) via affineGraph :=
  affineConstruction.result_defined

noncomputable def leftFile (xs l : V) : V := π₁ (affine xs)*l+π₂ (affine xs)
def leftGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “y xs l. ∃ z a b, !affineGraph z xs ∧ !pi₁Def a z ∧ !pi₂Def b z ∧ y=a*l+b”
instance left_defined : 𝚺ᴬ₁-Function₂ (leftFile : V → V → V) via leftGraph :=
  .mk fun v => by simp [leftGraph,affine_defined.df,leftFile]
instance left_definable : 𝚺ᴬ₁-Function₂ (leftFile : V → V → V) := left_defined.to_definable

@[simp] lemma left_nil (l : V) : leftFile 0 l=l := by
  simp [leftFile,affine,affineConstruction]
lemma left_adjoin (p xs l : V) :
    leftFile (p∷xs) l=leftFile xs (repeatBits p 1 (4*l+1)) := by
  simp only [leftFile,affine,VecRec.Construction.result_adjoin]
  simp only [affineConstruction]
  simp only [pi₁_pair,pi₂_pair]
  rw [cell_affine]
  ring1

end PA196.Arithmetic.Machine.PA.InternalTrace.ReturnCode

