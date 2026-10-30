import DiophantineConsistency.PRAModelIOpenPairing
import DiophantineConsistency.PRASelectCode
import DiophantineConsistency.PRAQOrder

set_option autoImplicit false
namespace DiophantineConsistency.PRAHistoryPairCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRABooleanOps
  PRASelectCode PRAQOrder PRAModelIOpenPairing

def bin {n : ℕ} (f : Code 2) (a b : Code n) : Code n :=
  .comp f (.cons a (.cons b (.nil n)))
def x : Code 2 := .proj 0
def y : Code 2 := .proj 1
def pairCode : Code 2 := selectAmong ltBitCode
  (bin addCode (bin mulCode y y) x)
  (bin addCode (bin addCode (bin mulCode x x) x) y)

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem modelBin {n : ℕ} (f : Code 2) (a b : Code n) (e : Fin n → M) :
    Structure.func (L := language) (bin f a b) e =
      Structure.func (L := language) f ![Structure.func (L := language) a e,
        Structure.func (L := language) b e] := by
  rw [bin, modelComposition]
  congr 1
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  exact Fin.cases rfl (fun k => Fin.elim0 k) j

theorem modelPairCode (a b : M) :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
    Structure.func (L := language) pairCode ![a,b] = pair a b := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  simp only [pairCode, modelSelectAmong, modelBin, x, y, modelProjection]
  change Structure.func (L := language) selectCode
    ![Structure.func (L := language) ltBitCode ![a,b], b*b+a,a*a+a+b] = _
  have hb : IsBit (Structure.func (L := language) ltBitCode ![a,b]) := by
    rw [modelLtBit]
    exact modelNonzeroBit _
  have hc := modelLtBitDefinition a b
  by_cases h : a < b
  · have ht := hc.mp h
    rw [ht, modelSelectOne]
    simp [pair, h]
  · have ht : Structure.func (L := language) ltBitCode ![a,b] =
        Structure.func (L := language) (Code.zero 0) Fin.elim0 := by
      rcases hb with hz | ho
      · exact hz
      · exact False.elim (h (hc.mpr ho))
    rw [ht, modelSelectZero]
    simp [pair, h]
theorem modelPairCodeGraph (a b : M) :
    (Semiformula.lMap embedding pairDef.val).Eval
      ![Structure.func (L := language) pairCode ![a,b],a,b] Empty.elim := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  exact (pairGraph_spec a b _).mpr (modelPairCode a b)

def pairRew : Rew language Empty 3 Empty 2 := Rew.embSubsts
  ![.func pairCode ![#0,#1],#0,#1]

def graphSentence : Sentence language := ∀⁰* (pairRew ▹ (Semiformula.lMap embedding pairDef.val))

theorem modelGraphSentence : M↓[language] ⊧ graphSentence := by
  simp only [models_iff, graphSentence, Semiformula.eval_allClosure]
  intro e
  rw [Matrix.fun_eq_vec_two e]
  simp only [Semiformula.eval_rew]
  have hv : (Semiterm.val (L := language) ![e 0,e 1] Empty.elim ∘
      pairRew ∘ Semiterm.bvar) =
      ![Structure.func (L := language) pairCode ![e 0,e 1],e 0,e 1] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change Structure.func (L := language) pairCode
        (Semiterm.val (L := language) ![e 0,e 1] Empty.elim ∘ ![#0,#1]) = _
      congr 1
      funext k
      refine Fin.cases rfl (fun l => ?_) k
      exact Fin.cases rfl (fun m => Fin.elim0 m) l
    · refine Fin.cases rfl (fun k => ?_) j
      exact Fin.cases rfl (fun l => Fin.elim0 l) k
  have he : (Semiterm.val (L := language) ![e 0,e 1] Empty.elim ∘
      pairRew ∘ Semiterm.fvar) =
      (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [hv,he]
  exact modelPairCodeGraph (e 0) (e 1)
end models

theorem PRA_proves_pairCodeGraph : PRA ⊢ graphSentence := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelGraphSentence
end DiophantineConsistency.PRAHistoryPairCode
