import ZFCinPA.ModelCodedFreeRenaming

/-!
Represented finite sequent images for the internal two-counter free renaming.
The total image graph is fixed before the arithmetic model. Constructor and
SHIFT image laws retain actual formula-set premises where syntax laws need
well-formed inputs. No source derivation is translated by this module.
-/
namespace LeanProofs.ZFCinPA.ModelCodedRenamingSets
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA.ModelCodedFreeRenaming
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

lemma setRename_existsUnique (L : Language) [L.Encodable] [L.LORDefinable]
    (chosen level offset sequence : V) :
    ∃! out : V, ∀ y, y ∈ out ↔ ∃ x ∈ sequence, y = rename L chosen level offset x :=
  sigma₁_replacement (by definability) sequence

noncomputable def setRename (L : Language) [L.Encodable] [L.LORDefinable]
    (chosen level offset sequence : V) : V :=
  Classical.choose! (setRename_existsUnique L chosen level offset sequence)
noncomputable def setRenameDef (L : Language) [L.Encodable] [L.LORDefinable] :
    𝚺₁.Semisentence 5 := .mkSigma “out chosen level offset sequence.
      (∀ y ∈' out, ∃ x ∈' sequence, !(renameDef L) y chosen level offset x) ∧
      (∀ x ∈' sequence, ∃ y, !(renameDef L) y chosen level offset x ∧ y ∈ out)”

lemma mem_setRename_iff (chosen level offset : V) {sequence y : V} :
    y ∈ setRename L chosen level offset sequence ↔
      ∃ x ∈ sequence, y = rename L chosen level offset x :=
  Classical.choose!_spec (setRename_existsUnique L chosen level offset sequence) y
lemma rename_mem_setRename (chosen level offset : V) {sequence p : V} (hp : p ∈ sequence) :
    rename L chosen level offset p ∈ setRename L chosen level offset sequence :=
  mem_setRename_iff chosen level offset |>.mpr ⟨p,hp,rfl⟩

private lemma setRename_graph (chosen level offset out sequence : V) :
    out = setRename L chosen level offset sequence ↔
      (∀ y ∈ out, ∃ x ∈ sequence, y = rename L chosen level offset x) ∧
      (∀ x ∈ sequence, rename L chosen level offset x ∈ out) := by
  constructor
  · rintro rfl
    exact ⟨fun _ hy => (mem_setRename_iff chosen level offset).mp hy,
      fun _ hx => rename_mem_setRename chosen level offset hx⟩
  · rintro ⟨hforward,hback⟩
    apply mem_ext
    intro y
    constructor
    · intro hy
      exact (mem_setRename_iff chosen level offset).mpr (hforward y hy)
    · intro hy
      rcases (mem_setRename_iff chosen level offset).mp hy with ⟨x,hx,rfl⟩
      exact hback x hx
instance setRename_defined :
    𝚺₁-Function₄[V] (setRename L) via setRenameDef L := .mk fun e => by
  simp [setRenameDef,setRename_graph]
instance setRename_delta : 𝚫₁-Function₄[V] (setRename L) :=
  setRename_defined.graph_delta.to_definable

lemma setRename_isFormulaSet (chosen level offset : V) {sequence : V}
    (hs : IsFormulaSet L sequence) :
    IsFormulaSet L (setRename L chosen level offset sequence) := by
  intro p hp
  rcases (mem_setRename_iff chosen level offset).mp hp with ⟨q,hq,rfl⟩
  exact rename_isSemiformula chosen level offset (hs q hq)

@[simp] lemma setRename_empty (chosen level offset : V) :
    setRename L chosen level offset (∅ : V) = ∅ := by
  apply mem_ext
  intro y
  simp [mem_setRename_iff]
@[simp] lemma setRename_insert (chosen level offset p sequence : V) :
    setRename L chosen level offset (insert p sequence) =
      insert (rename L chosen level offset p) (setRename L chosen level offset sequence) := by
  apply mem_ext
  intro y
  simp [mem_setRename_iff]
lemma setRename_subset (chosen level offset : V) {sequence target : V}
    (h : sequence ⊆ target) :
    setRename L chosen level offset sequence ⊆ setRename L chosen level offset target := by
  intro y hy
  rcases (mem_setRename_iff chosen level offset).mp hy with ⟨x,hx,rfl⟩
  exact rename_mem_setRename chosen level offset (h hx)

lemma setRename_shift_lift (chosen level offset : V) {sequence : V}
    (hs : IsFormulaSet L sequence) :
    setRename L chosen (level+1) offset (setShift L sequence) =
      setShift L (setRename L chosen level offset sequence) := by
  apply mem_ext
  intro y
  constructor
  · intro hy
    rcases (mem_setRename_iff chosen (level+1) offset).mp hy with ⟨q,hq,rfl⟩
    rcases mem_setShift_iff.mp hq with ⟨p,hp,rfl⟩
    exact mem_setShift_iff.mpr ⟨rename L chosen level offset p,
      rename_mem_setRename chosen level offset hp,
      rename_shift_lift chosen level offset (hs p hp).isUFormula⟩
  · intro hy
    rcases mem_setShift_iff.mp hy with ⟨q,hq,rfl⟩
    rcases (mem_setRename_iff chosen level offset).mp hq with ⟨p,hp,rfl⟩
    exact (mem_setRename_iff chosen (level+1) offset).mpr
      ⟨shift L p,shift_mem_setShift hp,
        (rename_shift_lift chosen level offset (hs p hp).isUFormula).symm⟩
lemma setRename_shift_offset (chosen offset : V) {sequence : V}
    (hs : IsFormulaSet L sequence) :
    setRename L chosen 0 offset (setShift L sequence) =
      setRename L chosen 0 (offset+1) sequence := by
  apply mem_ext
  intro y
  constructor
  · intro hy
    rcases (mem_setRename_iff chosen 0 offset).mp hy with ⟨q,hq,rfl⟩
    rcases mem_setShift_iff.mp hq with ⟨p,hp,rfl⟩
    exact (mem_setRename_iff chosen 0 (offset+1)).mpr
      ⟨p,hp,rename_shift_offset chosen offset (hs p hp).isUFormula⟩
  · intro hy
    rcases (mem_setRename_iff chosen 0 (offset+1)).mp hy with ⟨p,hp,rfl⟩
    exact (mem_setRename_iff chosen 0 offset).mpr
      ⟨shift L p,shift_mem_setShift hp,
        (rename_shift_offset chosen offset (hs p hp).isUFormula).symm⟩

lemma rename_substs1 (chosen level offset : V) {p term : V}
    (hp : IsSemiformula L 1 p) (ht : IsTerm L term) :
    rename L chosen level offset (substs1 L term p) =
      substs1 L (termRename L chosen level offset term) (rename L chosen level offset p) := by
  unfold substs1
  rw [rename_subst chosen level offset hp 0 (term ∷ 0) (by simp [ht]),
    termRenameVec_singleton chosen level offset ht.isUTerm]

end LeanProofs.ZFCinPA.ModelCodedRenamingSets
