import PA194AX11HPushIteration
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
namespace PA194AX11HPushIterationExtra
open PA194AX11HPushIteration
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch PA194PathIterator
open PA194SourceControllerCode PA194SchedulerIteration PA194AX11HPushPaused PA194AX11HPushAlignedDef PA194StackCode PA194FiniteControls

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem source_orbit_base (old revised : M) :
    F pairedRun ![0,pair old revised] = pair old revised := pairedRun_base _

theorem source_orbit_succ (k old revised : M) :
    F pairedRun ![k+1,pair old revised] =
      pair (F oldPaused ![pi₁ (F pairedRun ![k,pair old revised])])
           (F newPaused ![pi₂ (F pairedRun ![k,pair old revised])]) := by
  rw [pairedRun_succ,pairedStep_model]

theorem source_orbit_aligned (k old revised : M) (h : aligned old revised) :
    aligned (pi₁ (F pairedRun ![k,pair old revised]))
            (pi₂ (F pairedRun ![k,pair old revised])) := by
  apply pairedRun_preserves (s := pair old revised) (k := k)
  simpa [alignedPair] using h

theorem aligned_exit_iff (old revised : M) (h : aligned old revised) :
    F pc ![old] = modelNumeral M 3587 ↔ F pc ![revised] = modelNumeral M 3572 := by
  obtain ⟨k,_,ho,hn,_⟩ := h
  constructor
  · intro he
    have hk : k = modelNumeral M 19 := by
      apply add_left_cancel (a := modelNumeral M 3568)
      rw [←ho,he,←modelNumeralAdd]
    rw [hn,hk,←modelNumeralAdd]
  · intro he
    have hk : k = modelNumeral M 19 := by
      apply add_left_cancel (a := modelNumeral M 3553)
      rw [←hn,he,←modelNumeralAdd]
    rw [ho,hk,←modelNumeralAdd]

theorem source_orbit_succ_live (k old revised : M) (h : aligned old revised)
    (hlive : F pc ![pi₁ (F pairedRun ![k,pair old revised])] ≠ modelNumeral M 3587) :
    F pairedRun ![k+1,pair old revised] =
      pair (F PA194SourceControllerCode.step ![pi₁ (F pairedRun ![k,pair old revised])])
           (F PA194AX11HSource.step ![pi₂ (F pairedRun ![k,pair old revised])]) := by
  have ha := source_orbit_aligned k old revised h
  have hlive2 : F pc ![pi₂ (F pairedRun ![k,pair old revised])] ≠ modelNumeral M 3572 := by
    intro he
    exact hlive ((aligned_exit_iff _ _ ha).mpr he)
  rw [source_orbit_succ, oldPaused_model, newPaused_model, if_neg hlive, if_neg hlive2]

#print axioms aligned_exit_iff
#print axioms source_orbit_succ_live
#print axioms source_orbit_base
#print axioms source_orbit_succ
#print axioms source_orbit_aligned
end models
end PA194AX11HPushIterationExtra
