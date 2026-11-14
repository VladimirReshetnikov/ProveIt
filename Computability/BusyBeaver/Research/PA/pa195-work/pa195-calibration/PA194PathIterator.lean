import PA194PathZero
import PA194ChildCodes
import DiophantineConsistency.PRAHistoryPairCode
import DiophantineConsistency.PRAExhaustion

/-! An explicit primitive-recursion code for paths chosen between the two
certified PA194 decoder children. The root and branch selector are arbitrary
supplied codes; the two child codes carry explicit candidate-PRA proofs. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace PA194PathIterator
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRASelectCode
  PRAHistoryPairCode PRAExhaustion

def unary {n : Nat} (f : Code 1) (x : Code n) : Code n := .comp f (.cons x (.nil n))

/-- The step receives `[index, previous, seed]`. Zero chooses the second
child; every nonzero selector value chooses the first. -/
def pathStep (firstChild secondChild : Code 1) (choice : Code 2) : Code 3 :=
  selectAmong (bin choice (.proj 2) (.proj 0))
    (unary firstChild (.proj 1)) (unary secondChild (.proj 1))

def pathCore (root firstChild secondChild : Code 1) (choice : Code 2) : Code 2 :=
  .prec root (pathStep firstChild secondChild choice)

/-- Exposed argument order `[seed, index]`, matching the path-freshness theorem. -/
def pathCode (root firstChild secondChild : Code 1) (choice : Code 2) : Code 2 :=
  .comp (pathCore root firstChild secondChild choice) (.cons (.proj 1) (.cons (.proj 0) (.nil 2)))

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen

theorem modelUnary {n : Nat} (f : Code 1) (x : Code n) (e : Fin n → M) :
    Structure.func (L := language) (unary f x) e =
      Structure.func (L := language) f (fun _ => Structure.func (L := language) x e) := by
  rw [unary, modelComposition]
  congr 1
  funext i
  exact Fin.cases rfl (fun j => Fin.elim0 j) i

theorem modelPathBase (root firstChild secondChild : Code 1) (choice : Code 2) (seed : M) :
    PA195PathBound.pathValue (pathCode root firstChild secondChild choice) seed 0 =
      Structure.func (L := language) root (fun _ => seed) := by
  unfold PA195PathBound.pathValue pathCode
  rw [modelSwapComposition]
  have h := modelBase (M := M) root (pathStep firstChild secondChild choice) (fun _ => seed)
  have he : (fun i : Fin 2 => Fin.cases (Structure.func (L := language) (Code.zero 0) Fin.elim0) (fun _ : Fin 1 => seed) i) = ![(0 : M),seed] := by
    funext j
    refine Fin.cases rfl (fun k => ?_) j
    exact Fin.cases rfl (fun l => Fin.elim0 l) k
  rw [he] at h
  exact h

theorem modelPathStepRaw (root firstChild secondChild : Code 1) (choice : Code 2)
    (seed i : M) :
    PA195PathBound.pathValue (pathCode root firstChild secondChild choice) seed (i+1) =
      Structure.func (L := language) selectCode
        ![Structure.func (L := language) choice ![seed,i],
          Structure.func (L := language) firstChild (fun _ =>
            PA195PathBound.pathValue (pathCode root firstChild secondChild choice) seed i),
          Structure.func (L := language) secondChild (fun _ =>
            PA195PathBound.pathValue (pathCode root firstChild secondChild choice) seed i)] := by
  unfold PA195PathBound.pathValue pathCode
  rw [modelSwapComposition]
  change Structure.func (L := language) (pathCore root firstChild secondChild choice)
    ![Structure.func (L := language) addCode ![i,Structure.func (L := language) oneCode Fin.elim0],seed] = _
  rw [modelAddOne i]
  have h := modelStep (M := M) root (pathStep firstChild secondChild choice) ![i,seed]
  change Structure.func (L := language) (pathCore root firstChild secondChild choice)
    ![Structure.func (L := language) Code.succ (fun _ => i),seed] =
    Structure.func (L := language) (pathStep firstChild secondChild choice)
      ![i,Structure.func (L := language) (pathCore root firstChild secondChild choice) ![i,seed],seed] at h
  rw [h]
  simp only [pathStep, modelSelectAmong, modelBin, modelUnary, modelProjection]
  rw [modelSwapComposition]
  rfl

/-- Without requiring a Boolean-valued selector, every successor is one of
the actual PA194 numeric decoder's two Cantor children. -/
theorem modelPathStep (root firstChild secondChild : Code 1) (choice : Code 2)
    (hfirst : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding PA194ChildCodes.firstMatrix.val) firstChild)
    (hsecond : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding PA194ChildCodes.secondMatrix.val) secondChild)
    (seed i : M) :
    let f := pathCode root firstChild secondChild choice
    PA195PathBound.pathValue f seed (i+1) = first (PA195PathBound.pathValue f seed i / 4) ∨
      PA195PathBound.pathValue f seed (i+1) = second (PA195PathBound.pathValue f seed i / 4) := by
  dsimp only
  rw [modelPathStepRaw, PA194ChildCodes.modelFirstCode firstChild hfirst,
    PA194ChildCodes.modelSecondCode secondChild hsecond]
  let test := Structure.func (L := language) choice ![seed,i]
  rcases modelZeroOrSuccPred test with hz | hs
  · right
    change Structure.func (L := language) selectCode ![test,_,_] = _
    rw [hz, modelSelectZero]
  · left
    change Structure.func (L := language) selectCode ![test,_,_] = _
    rw [←hs, modelSelectSucc]

/-- The explicit branch iterator inherits zero-safe path self-freshness in
every candidate-PRA model, for arbitrary model-length limits. -/
theorem modelPathSelfFresh (root firstChild secondChild : Code 1) (choice : Code 2)
    (hfirst : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding PA194ChildCodes.firstMatrix.val) firstChild)
    (hsecond : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding PA194ChildCodes.secondMatrix.val) secondChild)
    (seed limit : M) :
    let f := pathCode root firstChild secondChild choice
    ¬PA195PathBound.PathOccurs f seed limit (PA195PathBound.pathValue f seed 0) := by
  dsimp only
  apply PA195PathBound.safe_path_self_fresh
  intro i _
  exact modelPathStep root firstChild secondChild choice hfirst hsecond seed i

end models
#print axioms modelPathStep
#print axioms modelPathSelfFresh
end PA194PathIterator
