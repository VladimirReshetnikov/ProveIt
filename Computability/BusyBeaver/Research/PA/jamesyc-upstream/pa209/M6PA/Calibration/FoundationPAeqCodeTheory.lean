module
public import M6PA.Theory
public import M6PA.Calibration.FoundationPAeqCodeInductionTheory
@[expose] public section
/-! Exact Delta-one classifier for the unchanged ordinaryPAeq theory.
The finite branch exposes literal host-list witnesses even in nonstandard models. -/
namespace M6.PA.FoundationPAeqCode
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

def targetFixedSentences : List (Sentence Presentation.language) :=
  Presentation.fixedAxioms.map (fun p=>p.univCl)
def targetFixedTheory : Theory Presentation.language := fun σ=>σ∈targetFixedSentences
noncomputable instance targetFixedTheory_delta1 : targetFixedTheory.Δ₁ :=
  Theory.Δ₁.ofList targetFixedSentences

theorem ordinaryPAeq_eq_union : Presentation.ordinaryPAeq=targetFixedTheory∪targetInductionTheory := by
  ext σ
  constructor
  · rintro ⟨p,hp,rfl⟩
    cases hp with
    | fixed p hp => left; exact List.mem_map.mpr ⟨p,hp,rfl⟩
    | induction p => right; exact ⟨p,rfl⟩
  · rintro (h|h)
    · obtain ⟨p,hp,rfl⟩:=List.mem_map.mp h
      exact ⟨p,.fixed p hp,rfl⟩
    · obtain ⟨p,rfl⟩:=h
      exact ⟨Presentation.inductionFormula p,.induction p,rfl⟩

noncomputable instance ordinaryPAeq_delta1 : Presentation.ordinaryPAeq.Δ₁ :=
  (Theory.Δ₁.add targetFixedTheory_delta1 targetInductionTheory_delta1).ofEq ordinaryPAeq_eq_union.symm

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem target_ofList_iff (l : List (Sentence Presentation.language)) (p : V) :
    (V ⊧/![p] (Theory.Δ₁.ofList l).ch.val) ↔ ∃ σ∈l,p=(Encodable.encode σ:V) := by
  induction l with
  | nil =>
    change (V ⊧/![p] (⊥ : ArithmeticSemisentence 1)) ↔ _
    simp
  | cons σ l ih =>
    change (V ⊧/![p] ((Theory.Δ₁.singleton σ).ch ⋎ (Theory.Δ₁.ofList l).ch).val) ↔ _
    simp only [Bounding.HierarchySymbol.Semiformula.val_or,LogicalConnective.HomClass.map_or]
    rw [ih]
    change ((V ⊧/![p] “x. x = ↑(Encodable.encode σ)”) ∨ _) ↔ _
    simp [numeral_eq_natCast]

theorem targetFixed_mem_iff (c : V) : c∈targetFixedTheory.Δ₁Class ↔
    ∃p∈Presentation.fixedAxioms,c=(Encodable.encode p.univCl:V) := by
  change (V ⊧/![c] (Theory.Δ₁.ofList targetFixedSentences).ch.val) ↔ _
  rw [target_ofList_iff]
  simp [targetFixedSentences]

theorem targetInduction_mem_iff (c : V) : c∈targetInductionTheory.Δ₁Class ↔ targetInductionR c := by
  exact targetInductionR_defined.df ![c]

theorem ordinaryPAeq_mem_iff (c : V) : c∈Presentation.ordinaryPAeq.Δ₁Class ↔
    (∃p∈Presentation.fixedAxioms,c=(Encodable.encode p.univCl:V)) ∨ targetInductionR c := by
  change c∈(targetFixedTheory∪targetInductionTheory).Δ₁Class ↔ _
  rw [Theory.Δ₁Class.mem_union,targetFixed_mem_iff,targetInduction_mem_iff]

theorem ordinaryPAeq_induction_witness {c : V}
    (hc : c∈Presentation.ordinaryPAeq.Δ₁Class)
    (hfixed : ¬∃p∈Presentation.fixedAxioms,c=(Encodable.encode p.univCl:V)) :
    ∃m≤c,∃b≤c,c=qqAlls b m ∧ IsUFormula Presentation.language b ∧
      shift Presentation.language b=b ∧ bv Presentation.language b=m ∧
      ∃k≤subst Presentation.language (fvarVec m) b,
        IsSemiformula Presentation.language 1 k ∧
        subst Presentation.language (fvarVec m) b=targetIndBody k :=
  ((ordinaryPAeq_mem_iff c).mp hc).resolve_left hfixed

#print axioms ordinaryPAeq_eq_union
#print axioms ordinaryPAeq_delta1
#print axioms target_ofList_iff
#print axioms targetFixed_mem_iff
#print axioms targetInduction_mem_iff
#print axioms ordinaryPAeq_mem_iff
#print axioms ordinaryPAeq_induction_witness
end M6.PA.FoundationPAeqCode

