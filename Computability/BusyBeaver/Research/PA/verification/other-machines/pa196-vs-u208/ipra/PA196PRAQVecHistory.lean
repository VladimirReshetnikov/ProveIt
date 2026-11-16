import PA196PRAQVecTower
import DiophantineConsistency.PRAHistorySeqConsCode

/-! A candidate-PRA history code for the qVec majorant tower with an arbitrary
model-internal seed. The sequence coding and trace specification are separate. -/
set_option autoImplicit false
namespace PA196PRAQVecHistory
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
  PA196PRAQVecTower

def firstHistory (cons : Code 2) : Code 1 := bin cons (.zero 1) (.proj 0)
def nextIndex : Code 3 := .comp .succ (.cons (.proj 0) (.nil 3))
noncomputable def nextValue : Code 3 :=
  .comp towerCode (.cons nextIndex (.cons (.proj 2) (.nil 3)))
noncomputable def historyStep (cons : Code 2) : Code 3 := bin cons (.proj 1) nextValue
noncomputable def historyCode (cons : Code 2) : Code 2 := .prec (firstHistory cons) (historyStep cons)

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩

noncomputable def history (cons : Code 2) (n seed : M) : M :=
  Structure.func (L := language) (historyCode cons) ![n, seed]

theorem history_zero (cons : Code 2) (seed : M) :
    history cons 0 seed = Structure.func (L := language) cons ![0,seed] := by
  have h := modelBase (M := M) (firstHistory cons) (historyStep cons) ![seed]
  change history cons 0 seed = Structure.func (L := language) (firstHistory cons) ![seed] at h
  rw [h,firstHistory,modelBin,modelProjection]
  rw [PRAMultiplication.modelZero]
  rfl

theorem history_succ (cons : Code 2) (n seed : M) :
    history cons (n+1) seed = Structure.func (L := language) cons
      ![history cons n seed, tower (n+1) seed] := by
  have h := modelStep (M := M) (firstHistory cons) (historyStep cons) ![n,seed]
  change history cons (Structure.func (L := language) Code.succ (fun _ => n)) seed =
    Structure.func (L := language) (historyStep cons) ![n,history cons n seed,seed] at h
  rw [show Structure.func (L := language) Code.succ (fun _ => n) = n+1 from (modelAddOne n).symm] at h
  rw [h,historyStep,modelBin,modelProjection,nextValue,modelComposition]
  congr 1
  funext j
  refine Fin.cases rfl (fun k => ?_) j
  refine Fin.cases ?_ (fun l => Fin.elim0 l) k
  change Structure.func (L := language) towerCode _ = tower (n+1) seed
  unfold tower
  congr 1
  funext k
  refine Fin.cases ?_ (fun l => ?_) k
  · change Structure.func (L := language) nextIndex ![n,history cons n seed,seed] = n+1
    rw [nextIndex, modelComposition]
    calc
      _ = Structure.func (L := language) Code.succ (fun _ => n) := by
        congr 1
        funext j
        refine Fin.cases ?_ (fun k => Fin.elim0 k) j
        exact modelProjection 0 _
      _ = n + 1 := (modelAddOne n).symm
  · exact Fin.cases (modelProjection 2 _ ) (fun m => Fin.elim0 m) l

end models
#print axioms history_zero
#print axioms history_succ
end PA196PRAQVecHistory
