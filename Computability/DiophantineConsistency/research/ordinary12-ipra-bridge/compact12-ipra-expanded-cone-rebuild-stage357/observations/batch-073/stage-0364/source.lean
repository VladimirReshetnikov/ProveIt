import ZFCinPA.Instances
import ZFCinPA.ValidatorVectorMap

set_option autoImplicit false
noncomputable section

/-!
# Internal lists for validator hypothesis contexts

The parts of the internal context calculus that do not mention a provability
predicate or a formula encoder, shared by `R2Ctx` (the C254 validator) and
`ValidatorProofContext222` (the C222 history predicate). Both modules re-export
these names.

* `imps G g = g₁ → (g₂ → ⋯ → g)`, the implication chain over an internal list;
* `shiftList`, the formula-wise `shift ℒₛₑₜ` of a list;
* `Enum L s` (`L` lists exactly the members of the set `s`), which exists for
  every set (`exists_enum`).
-/

namespace LeanProofs.ZFCinPA.ValidatorContextLists

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCode254
open scoped LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

instance wim_sigma1 : 𝚺₁-Function₂[V] wim := wim_defined.to_definable₀

/-! ## Implication chains -/

namespace Imps

def blueprint : VecRec.Blueprint 1 where
  nil := .mkSigma “y g. y = g”
  adjoin := .mkSigma “y p ps ih g. !wimDef y p ih”

noncomputable def construction : VecRec.Construction V blueprint where
  nil param := param 0
  adjoin _ p _ ih := wim p ih
  nil_defined := .mk fun v ↦ by simp [blueprint]
  adjoin_defined := .mk fun v ↦ by simp [blueprint]

end Imps

/-- `imps [g₁, …, gₙ] g = g₁ → (g₂ → ⋯ → (gₙ → g))`. -/
noncomputable def imps (G g : V) : V := Imps.construction.result ![g] G

@[simp] lemma imps_nil (g : V) : imps (0 : V) g = g := by simp [imps, Imps.construction]
@[simp] lemma imps_cons (a G g : V) : imps (a ∷ G) g = wim a (imps G g) := by
  simp [imps, Imps.construction]

def impsDef : 𝚺₁.Semisentence 3 := Imps.blueprint.resultDef

instance imps_defined : 𝚺₁-Function₂[V] imps via impsDef := .mk fun v ↦ by
  have e : (fun i : Fin 1 ↦ v i.succ.succ) = ![v 2] :=
    funext fun i ↦ by rw [Fin.fin_one_eq_zero i]; rfl
  rw [impsDef, (Imps.construction (V := V)).eval_resultDef v, e]
  rfl

instance imps_definable : 𝚺₁-Function₂[V] imps := imps_defined.to_definable

theorem imps_graph (out G g : V) :
    V ⊧/![out,G,g] impsDef.val ↔ out = imps G g :=
  (imps_defined (V := V)).df ![out,G,g]

theorem imps_total_unique (G g : V) :
    ∃! out : V, V ⊧/![out,G,g] impsDef.val :=
  ⟨imps G g, (imps_graph _ _ _).mpr rfl, fun _ h => (imps_graph _ _ _).mp h⟩

/-! ## Shifted lists -/

namespace ShiftList

def blueprint : VecRec.Blueprint 0 where
  nil := .mkSigma “y. y = 0”
  adjoin := .mkSigma “y p ps ih. ∃ q, !(shiftGraph ℒₛₑₜ) q p ∧ !adjoinDef y q ih”

noncomputable def construction : VecRec.Construction V blueprint where
  nil _ := 0
  adjoin _ p _ ih := shift ℒₛₑₜ p ∷ ih
  nil_defined := .mk fun v ↦ by simp [blueprint]
  adjoin_defined := .mk fun v ↦ by simp [blueprint]

end ShiftList

noncomputable def shiftList (L : V) : V := ShiftList.construction.result ![] L

@[simp] lemma shiftList_nil : shiftList (0 : V) = 0 := by simp [shiftList, ShiftList.construction]
@[simp] lemma shiftList_cons (p L : V) : shiftList (p ∷ L) = shift ℒₛₑₜ p ∷ shiftList L := by
  simp [shiftList, ShiftList.construction]

def shiftListDef : 𝚺₁.Semisentence 2 := ShiftList.blueprint.resultDef

instance shiftList_defined : 𝚺₁-Function₁[V] shiftList via shiftListDef := .mk fun v ↦ by
  have e : (fun i : Fin 0 ↦ v i.succ.succ) = ![] := funext fun i ↦ i.elim0
  rw [shiftListDef, (ShiftList.construction (V := V)).eval_resultDef v, e]
  rfl

instance shiftList_definable : 𝚺₁-Function₁[V] shiftList := shiftList_defined.to_definable

lemma shiftList_len_nth : ∀ L : V, len (shiftList L) = len L ∧
    ∀ i < len L, (shiftList L).[i] = shift ℒₛₑₜ L.[i] := by
  exact ValidatorVectorMap.len_nth (shift ℒₛₑₜ) shiftList shiftList_nil shiftList_cons

lemma mem_shiftList (L y : V) : y ∈ᵥ shiftList L ↔ ∃ p, p ∈ᵥ L ∧ y = shift ℒₛₑₜ p :=
  ValidatorVectorMap.mem _ _ L y (shiftList_len_nth L)

/-! ## Enumerations of sets -/

/-- `L` lists exactly the members of `s`. -/
def Enum (L s : V) : Prop := (∀ y ∈ s, y ∈ᵥ L) ∧ ∀ i < len L, L.[i] ∈ s

lemma Enum.mem {L s : V} (h : Enum L s) {y : V} : y ∈ᵥ L ↔ y ∈ s := by
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact h.2 i hi
  · exact h.1 y

lemma enum_of_mem {L s : V} (h : ∀ y, y ∈ᵥ L ↔ y ∈ s) : Enum L s :=
  ⟨fun y hy ↦ (h y).2 hy, fun _ hi ↦ (h _).1 (nth_mem_memVec hi)⟩

def enumDef : 𝚺₁.Semisentence 2 := .mkSigma
  “L s. (∀ y < s, y ∈ s → !memVecDef.sigma y L) ∧ ∃ l, !lenDef l L ∧
    ∀ i < l, ∃ y, !nthDef y L i ∧ y ∈ s”
instance enum_defined : 𝚺₁-Relation[V] Enum via enumDef :=
  .mk fun e => by
    simp only [enumDef]
    simp
    constructor
    · rintro ⟨h, hl⟩
      exact ⟨fun y hy => h y (lt_of_mem hy) hy, hl⟩
    · rintro ⟨h, hl⟩
      exact ⟨fun y _ hy => h y hy, hl⟩
instance enum_definable : 𝚫₁-Relation[V] Enum := by unfold Enum; definability

lemma exists_enum : ∀ s : V, ∃ L, Enum L s := by
  apply insert_induction_sigmaOne
  · definability
  · exact ⟨0, enum_of_mem fun y ↦ by simp⟩
  · rintro a s - ⟨L, hL⟩
    exact ⟨a ∷ L, enum_of_mem fun y ↦ by simp [hL.mem]⟩

end LeanProofs.ZFCinPA.ValidatorContextLists
