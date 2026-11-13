module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.PAInterpretedFixedSeedCalibration
public import PA196.Arithmetic.Transport.FoundationRelationalSequentFixedGraph
public import PA196.Arithmetic.Transport.FoundationRelationalSequentClosedRelocation
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.ForwardRelational

namespace PA196.Arithmetic.Transport.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open Ordinal (Term Formula)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem fixedImageSeed_translate_models (p : SourceFormula 0) (hp : p∈Presentation.fixedAxioms) :
    Numeric.translate (Numeric.parameters (0:V) 0 1 (fixedImageReserve p hp))
      (⌜formula p Fin.elim0 (fun _ => (.fvar 0 : Term 0))⌝ : V)=(fixedImageNativeCode p hp:V) := by
  rw [← Semiformula.coe_quote_eq_quote]
  have he := Numeric.translate_fixed_parameters_all_models (V:=V) 0 0 1 (fixedImageReserve p hp)
    (⌜formula p Fin.elim0 (fun _ => (.fvar 0 : Term 0))⌝ : Nat)
  simpa only [Nat.cast_zero,Nat.cast_one,fixedImageSeed_translate] using he

theorem fixedImageSeed_coverage (p : SourceFormula 0) (hp : p∈Presentation.fixedAxioms) :
    Numeric.FormulaCovered (0:V)
      (Numeric.zeroEnvironment (⌜formula p Fin.elim0 (fun _ => (.fvar 0 : Term 0))⌝ : V))
      1 (fixedImageReserve p hp)
      (⌜formula p Fin.elim0 (fun _ => (.fvar 0 : Term 0))⌝ : V) := by
  let q : V := ⌜formula p Fin.elim0 (fun _ => (.fvar 0 : Term 0))⌝
  have hz : (1:V)+q≤(fixedImageReserve p hp:V) := by
    have h := fixedImageReserve_code_bound p hp
    simpa [q,Semiformula.quote_eq_encode] using (show ((1+Encodable.encode (formula p Fin.elim0 (fun _ => (.fvar 0 : Term 0)))):V)≤(fixedImageReserve p hp:V) from by exact_mod_cast h)
  have he := Numeric.zeroEnvironment_properties (V:=V) q
  refine ⟨⟨⟨by simp,?_,?_,?_⟩,hz⟩,?_,he.1.ge⟩
  · exact le_trans (by simp) hz
  · intro i hi; simp at hi
  · intro i hi
    rw [he.1] at hi
    rw [he.2 i hi]
    simp
  · simpa [q] using Semiformula.quote_isSemiformula (V:=V) (formula p Fin.elim0 (fun _ => (.fvar 0 : Term 0)))

#print axioms fixedImageSeed_translate_models
#print axioms fixedImageSeed_coverage
end PA196.Arithmetic.Transport.ForwardRelational

