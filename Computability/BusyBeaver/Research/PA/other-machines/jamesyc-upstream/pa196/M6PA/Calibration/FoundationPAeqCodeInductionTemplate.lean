module
public import M6PA.Theory
public import M6PA.Calibration.FoundationPAeqCodeInductionStep
@[expose] public section
/-! Uniform additive/successor induction-body transport for model-coded p.
This template does not yet supply a canonical closed induction axiom for p. -/
namespace M6.PA.FoundationPAeqCode
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "U" => Presentation.ordinaryPAeq
local prefix:max "#'" => Semiterm.bvar (V:=V) (L:=Presentation.language)
local prefix:max "&'" => Semiterm.fvar (V:=V) (L:=Presentation.language)

noncomputable def typedInductionBody (p : Semiformula V Presentation.language 1) : Formula V Presentation.language :=
  p.subst ![typedZero] 🡒 (∀¹(p 🡒 p.subst ![typedSucc #'0])) 🡒 ∀¹p
noncomputable def typedAdditiveInductionBody (p : Semiformula V Presentation.language 1) : Formula V Presentation.language :=
  p.subst ![typedZero] 🡒 (∀¹(p 🡒 p.subst ![typedAdd #'0 (typedSucc typedZero)])) 🡒 ∀¹p

theorem induction_step_transport (p : Semiformula V Presentation.language 1) :
    (U).internalize V ⊢
      (∀¹(p 🡒 p.subst ![typedAdd #'0 (typedSucc typedZero)])) 🡒
      (∀¹(p 🡒 p.subst ![typedSucc #'0])) := by
  have he := additive_successor (V:=V) (&'0)
  have hr := replace (V:=V) p.shift (typedAdd (&'0) (typedSucc typedZero)) (typedSucc (&'0))
  have hb : (U).internalize V ⊢
      (p.free 🡒 p.shift.subst ![typedAdd (&'0) (typedSucc typedZero)]) 🡒
      (p.free 🡒 p.shift.subst ![typedSucc (&'0)]) := by
    cl_prover [he,hr]
  have h : ([] : List (Formula V Presentation.language)) ⊢[(U).internalize V]
      (∀¹(p 🡒 p.subst ![typedAdd #'0 (typedSucc typedZero)])) 🡒
      (∀¹(p 🡒 p.subst ![typedSucc #'0])) := by
    apply TProof.all_imp_all!
    simpa [Bootstrapping.Semiformula.free,SemitermVec.q,Semiformula.shift_substs,Semiformula.substs_substs] using (FFL.Entailment.FiniteContext.of' (Γ:=[]) hb)
  exact FFL.Entailment.FiniteContext.emptyPrf h

theorem induction_body_transport (p : Semiformula V Presentation.language 1) :
    (U).internalize V ⊢ typedInductionBody p 🡒 typedAdditiveInductionBody p := by
  unfold typedInductionBody typedAdditiveInductionBody
  cl_prover [induction_step_transport (V:=V) p]

theorem induction_body_transport_numeric (p : V) (hp : IsSemiformula Presentation.language 1 p) :
    Provable U (imp Presentation.language (typedInductionBody ⟨p,by simpa using hp⟩).val
      (typedAdditiveInductionBody ⟨p,by simpa using hp⟩).val) := by
  exact (tprovable_iff_provable (T:=U)).mp (induction_body_transport ⟨p,by simpa using hp⟩)

#print axioms induction_step_transport
#print axioms induction_body_transport
#print axioms induction_body_transport_numeric
end M6.PA.FoundationPAeqCode

