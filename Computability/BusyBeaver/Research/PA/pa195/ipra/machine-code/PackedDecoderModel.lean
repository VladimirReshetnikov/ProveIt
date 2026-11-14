import PackedRootModel
set_option autoImplicit false
namespace PackedDecoderModel
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRASelectCode PRAIsZero PRAExhaustion PRAQOrder PRAModelIOpenPairing
open TableDispatch TableModelSemantics ConfigurationStep PackedClock PackedRootModel

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem modelSubAsTsub (x y : M) :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
    Structure.func (L := language) subCode ![x,y] = x-y := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  rcases PRASubReconstruct.modelReconstruct y x with hz | hr
  · have hnot : ¬ y < x := by
      intro h
      have hn := (modelLtDifference y x).mp h
      exact hn hz
    have hle : x ≤ y := le_of_not_gt hnot
    have heq : x-y = 0 := tsub_eq_zero_of_le hle
    exact hz.trans heq.symm
  · have hr' : y + Structure.func (L := language) subCode ![x,y] = x := hr
    have heq : x-y = Structure.func (L := language) subCode ![x,y] := by
      calc
        x-y = (y + Structure.func (L := language) subCode ![x,y])-y := congrArg (fun z => z-y) hr'.symm
        _ = Structure.func (L := language) subCode ![x,y] := by simp
    exact heq.symm

theorem modelDecodeLeft (x : M) :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
    Structure.func (L := language) decodeLeft (fun _ => x) = pi₁ x := by
  classical
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  simp only [decodeLeft, lowSide, remainder, squareRoot, modelSelectAmong, modelBin,
    modelProjection, modelSelectAll]
  have hroot : Structure.func (L := language) rootCode (fun _ => x) = sqrt x := modelRootGraph x
  rw [hroot, modelSubAsTsub]
  have hm : Structure.func (L := language) mulCode ![sqrt x,sqrt x] = sqrt x * sqrt x := rfl
  rw [hm]
  have hz := modelLtZero (x - sqrt x * sqrt x) (sqrt x)
  change (Structure.func (L := language) ltBitCode ![x - sqrt x * sqrt x,sqrt x] =
    Structure.func (L := language) (Code.zero 0) Fin.elim0) ↔ ¬(x - sqrt x * sqrt x < sqrt x) at hz
  simp only [pi₁, unpair]
  by_cases h : x - sqrt x * sqrt x < sqrt x
  · have ht : Structure.func (L := language) ltBitCode ![x - sqrt x * sqrt x,sqrt x] ≠
        Structure.func (L := language) (Code.zero 0) Fin.elim0 := by
      intro he
      exact (hz.mp he) h
    simp only [ht, h, ite_false, ite_true]
  · have ht := hz.mpr h
    simp only [ht, h, ite_false, ite_true]

theorem modelDecodeRight (x : M) :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
    Structure.func (L := language) decodeRight (fun _ => x) = pi₂ x := by
  classical
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  simp only [decodeRight, lowSide, remainder, squareRoot, modelSelectAmong, modelBin,
    modelProjection, modelSelectAll]
  have hroot : Structure.func (L := language) rootCode (fun _ => x) = sqrt x := modelRootGraph x
  rw [hroot, modelSubAsTsub, modelSubAsTsub]
  have hm : Structure.func (L := language) mulCode ![sqrt x,sqrt x] = sqrt x * sqrt x := rfl
  rw [hm]
  have hz := modelLtZero (x - sqrt x * sqrt x) (sqrt x)
  change (Structure.func (L := language) ltBitCode ![x - sqrt x * sqrt x,sqrt x] =
    Structure.func (L := language) (Code.zero 0) Fin.elim0) ↔ ¬(x - sqrt x * sqrt x < sqrt x) at hz
  simp only [pi₂, unpair]
  by_cases h : x - sqrt x * sqrt x < sqrt x
  · have ht : Structure.func (L := language) ltBitCode ![x - sqrt x * sqrt x,sqrt x] ≠
        Structure.func (L := language) (Code.zero 0) Fin.elim0 := by
      intro he
      exact (hz.mp he) h
    simp only [ht, h, ite_false, ite_true]
  · have ht := hz.mpr h
    simp only [ht, h, ite_false, ite_true]

theorem modelDecodePair (a b : M) :
    Structure.func (L := language) decodeLeft
      (fun _ => Structure.func (L := language) pairCode ![a,b]) = a ∧
    Structure.func (L := language) decodeRight
      (fun _ => Structure.func (L := language) pairCode ![a,b]) = b := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  rw [modelPairCode, modelDecodeLeft, modelDecodeRight]
  exact ⟨pi₁_pair a b, pi₂_pair a b⟩

#print axioms modelDecodePair

#print axioms modelSubAsTsub
#print axioms modelDecodeLeft
#print axioms modelDecodeRight
end models
end PackedDecoderModel
