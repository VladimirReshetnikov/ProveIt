module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqSequentDerivation
public import PA196.Arithmetic.Transport.NumericPAeqBottomGuardDischarge
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic

namespace PA196.Arithmetic.Transport.NumericPAeqRefutationTransport
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqFormula.Sequent NumericPAeqRepeatedEnvironment PA196.Arithmetic.Checker
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
/-- Genuine arbitrary-model ordinaryPAeq refutation transport, with no supplier
or environment premise. The proof-wide repeated environment is constructed. -/
theorem ordinary_refutation_transport (d:V) (hd:Proof Presentation.ordinaryPAeq d qqFalsum):
    ∃code:V,verifyValue code=2:=by
  let f:=environment (qqFvar 0) d
  have hb:SourceProofBudget d f:=by
    refine ⟨?_,?_⟩
    · simpa [f] using environment_valid (show IsSemiterm RelationalSource.language (0:V) (qqFvar 0) by simp) d
    · simp [f]
  have child:=ordinary_derivation_requested d f hd.2 hb
  have he:fstIdx d=({qqFalsum}:V):=hd.1
  rw [he] at child
  exact NumericPAeqBottomDomain.native_bottom_of_repeated_guard d child

theorem ordinary_provable_refutation_transport (h:Provable (V:=V) Presentation.ordinaryPAeq qqFalsum):
    ∃code:V,verifyValue code=2:=by
  obtain ⟨d,hd⟩:=h
  exact ordinary_refutation_transport d hd
#print axioms ordinary_refutation_transport
#print axioms ordinary_provable_refutation_transport
end PA196.Arithmetic.Transport.NumericPAeqRefutationTransport

