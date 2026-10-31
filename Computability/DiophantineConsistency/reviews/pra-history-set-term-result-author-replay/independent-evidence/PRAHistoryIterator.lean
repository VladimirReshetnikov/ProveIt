import DiophantineConsistency.PRAHistorySeqConsCode
set_option autoImplicit false
namespace DiophantineConsistency.PRAHistoryIterator
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
  PRAHistorySeqConsCode

/-- Value recursion: the step receives the previous index and value. -/
def valueCode (base : Code 0) (step : Code 2) : Code 1 := .prec base step

def firstHistory (cons : Code 2) (base : Code 0) : Code 0 :=
  bin cons (.zero 0) base

def nextIndex : Code 2 := .comp .succ (.cons (.proj 0) (.nil 2))
def nextValue (base : Code 0) (step : Code 2) : Code 2 :=
  .comp (valueCode base step) (.cons nextIndex (.nil 2))
def historyStep (cons : Code 2) (base : Code 0) (step : Code 2) : Code 2 :=
  bin cons (.proj 1) (nextValue base step)
def historyCode (cons : Code 2) (base : Code 0) (step : Code 2) : Code 1 :=
  .prec (firstHistory cons base) (historyStep cons base step)

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

theorem modelValueBase (base : Code 0) (step : Code 2) :
    Structure.func (L := language) (M := M) (valueCode base step)
      (fun _ => Structure.func (L := language) (Code.zero 0) Fin.elim0) =
      Structure.func (L := language) base Fin.elim0 := by
  have h := modelBase (M := M) base step (Fin.elim0 : Fin 0 → M)
  have he : Fin.cases (Structure.func (L := language) (Code.zero 0) Fin.elim0)
      (Fin.elim0 : Fin 0 → M) = (fun _ : Fin 1 => Structure.func (L := language) (Code.zero 0) Fin.elim0) := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  rw [he] at h
  exact h

theorem modelValueStep (base : Code 0) (step : Code 2) (i : M) :
    Structure.func (L := language) (valueCode base step)
      (fun _ => Structure.func (L := language) Code.succ (fun _ => i)) =
      Structure.func (L := language) step
        ![i,Structure.func (L := language) (valueCode base step) (fun _ => i)] := by
  have h := modelStep (M := M) base step (fun _ : Fin 1 => i)
  have he : (fun j : Fin 2 => Fin.cases i
      (Fin.cases (Structure.func (L := language) (valueCode base step) (fun _ => i))
        (Fin.elim0 : Fin 0 → M)) j) =
      ![i,Structure.func (L := language) (valueCode base step) (fun _ => i)] := rfl
  have hy : (fun _ : Fin 0 => i) = (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  rw [hy] at h
  have hs : Fin.cases (Structure.func (L := language) Code.succ (fun _ => i))
      (Fin.elim0 : Fin 0 → M) = (fun _ : Fin 1 => Structure.func (L := language) Code.succ (fun _ => i)) := by
    funext j
    exact Fin.cases rfl (fun k => Fin.elim0 k) j
  rw [hs] at h
  change Structure.func (L := language) (valueCode base step)
      (fun _ => Structure.func (L := language) Code.succ (fun _ => i)) =
    Structure.func (L := language) step (Fin.cases i (Fin.cases
      (Structure.func (L := language) (valueCode base step) (fun _ => i))
      (Fin.elim0 : Fin 0 → M))) at h
  rw [he] at h
  exact h

theorem modelHistoryBase (cons : Code 2) (base : Code 0) (step : Code 2) :
    Structure.func (L := language) (M := M) (historyCode cons base step)
      (fun _ => Structure.func (L := language) (Code.zero 0) Fin.elim0) =
      Structure.func (L := language) cons
        ![Structure.func (L := language) (Code.zero 0) Fin.elim0,
          Structure.func (L := language) base Fin.elim0] := by
  have h := modelValueBase (M := M) (firstHistory cons base) (historyStep cons base step)
  rw [show valueCode (firstHistory cons base) (historyStep cons base step) =
    historyCode cons base step from rfl] at h
  rw [h,firstHistory,modelBin]

theorem modelHistoryStep (cons : Code 2) (base : Code 0) (step : Code 2) (i : M) :
    Structure.func (L := language) (historyCode cons base step)
      (fun _ => Structure.func (L := language) Code.succ (fun _ => i)) =
      Structure.func (L := language) cons
        ![Structure.func (L := language) (historyCode cons base step) (fun _ => i),
          Structure.func (L := language) (valueCode base step)
            (fun _ => Structure.func (L := language) Code.succ (fun _ => i))] := by
  have h := modelValueStep (M := M) (firstHistory cons base) (historyStep cons base step) i
  rw [show valueCode (firstHistory cons base) (historyStep cons base step) =
    historyCode cons base step from rfl] at h
  rw [h,historyStep,modelBin,modelProjection,nextValue,modelComposition]
  congr 1
  funext j
  refine Fin.cases rfl (fun k => ?_) j
  refine Fin.cases ?_ (fun l => Fin.elim0 l) k
  congr 1
  funext k
  refine Fin.cases ?_ (fun l => Fin.elim0 l) k
  have ha : (fun j : Fin 1 => Structure.func (L := language)
      (getCode (.cons nextIndex (.nil 2)) j)
      ![i,Structure.func (L := language) (historyCode cons base step) (fun _ => i)]) =
      (fun _ => Structure.func (L := language) Code.succ (fun _ => i)) := by
    funext j
    refine Fin.cases ?_ (fun k => Fin.elim0 k) j
    change Structure.func (L := language) nextIndex ![i,
      Structure.func (L := language) (historyCode cons base step) (fun _ => i)] = _
    rw [nextIndex,modelComposition]
    congr 1
    funext k
    refine Fin.cases ?_ (fun l => Fin.elim0 l) k
    exact modelProjection 0 _
  rw [ha]
end models
end DiophantineConsistency.PRAHistoryIterator
