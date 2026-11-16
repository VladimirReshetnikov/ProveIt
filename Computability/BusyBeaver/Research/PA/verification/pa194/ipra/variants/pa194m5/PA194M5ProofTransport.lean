import PA194M5RecodeHeads
import PA194RadixRestrictedImplication
import PA194TargetProofLeaf
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
set_option linter.unusedSectionVars false
noncomputable section
namespace PA194M5ProofTransport
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAHerbrandSelection TableDispatch
open PA194ClockInvariantDefinable PA194RadixRecoding PA194RadixModel PA194TargetCantor
open PA194TargetLeaves PA194TargetGate PA194TargetExtendedStep PA194TargetProofLeaf
open PA194M5RecodeConstructors PA194M5RecodeHeads
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
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

/-- The exact radix-five proof rules and emitted heads needed by the transport. -/
structure FiveClosure (G : M → Prop) : Prop where
  head1 : ∀ a b, G (head1Five a b)
  head2 : ∀ a b c, G (head2Five a b c)
  head3 : ∀ a b c, G (head3Five a b c)
  head4 : ∀ a b c, G (head4Five a b c)
  head5 : ∀ a b, G (head5Five a b)
  head6 : ∀ a b c, G (head6Five a b c)
  rho8 : ∀ a b c u, u ≤ a → G (rho8Five a b c u)
  gate : ∀ a b c, c ≠ a → c ≠ b → G (gateFive a b c)
  diagonal : ∀ a, G (diagonalFive a)
  generalize : ∀ label a, G a → G (all5 label a)
  modusPonens : ∀ a b, G a → G (imp5 a b) → G b

/-- The restricted radix-five rho8 rows supply the unrestricted schema; no
monotonicity of hereditary recoding is assumed. -/
theorem unrestrictedRho8 (G : M → Prop) (h : FiveClosure G) (a b c u : M) :
    G (rho8Five a b c u) := by
  have hr : (1 : M) ≤ 5 := by norm_num
  have hp := PA194RadixRestrictedImplication.unrestrictedProved (5 : M) hr G
    (fun {x y} hf hx => h.modusPonens x y hx (by simpa [PA194RadixRestrictedImplication.implication,imp5,encode] using hf))
    (fun x y z v hv => by simpa [rho8Five,PA194RadixRestrictedImplication.implication,imp5,encode] using h.rho8 x y z v hv)
    a b c u
  simpa [rho8Five,PA194RadixRestrictedImplication.implication,imp5,encode] using hp

/-- A model-valued radix-four coded proof transports into any Σ₁-definable
radix-five proof predicate satisfying the actual constructor/rule closure.
The target predicate and closure are explicit assumptions. -/
theorem proofTransport (G : M → Prop) (hG : 𝚺₁-Predicate G) (cl : FiveClosure G)
    (program result : M) (proof : TargetProof program result) : G (lift5 result) := by
  let H : M → Prop := fun x => G (lift5 x)
  have hlift : 𝚺₁-Function₁ (lift5 : M → M) := unaryCodeDef (recode 3 4)
  have hH : 𝚺₁-Predicate H := by
    haveI := hlift
    haveI := hG
    dsimp only [H]
    definability
  apply targetProof_sound H hH ?_ ?_ ?_ ?_ program result proof
  · intro a b
    change G (lift5 (F machineHead1 ![a,b]))
    rw [machineHead1_model,lift_head1]
    exact cl.head1 _ _
  · intro label a ha
    change G (lift5 (allValue label a))
    rw [lift_all]
    exact cl.generalize _ _ ha
  · intro a b ha hab
    change G (lift5 b)
    apply cl.modusPonens (lift5 a) (lift5 b) ha
    change G (lift5 (impValue a b)) at hab
    simpa only [lift_imp] using hab
  · refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
    · intro a b c; change G (lift5 (head2Value a b c)); rw [lift_head2]; exact cl.head2 _ _ _
    · intro a b c; change G (lift5 (head3Value a b c)); rw [lift_head3]; exact cl.head3 _ _ _
    · intro a b c; change G (lift5 (head4Value a b c)); rw [lift_head4]; exact cl.head4 _ _ _
    · intro a b; change G (lift5 (head5Value a b)); rw [lift_head5]; exact cl.head5 _ _
    · intro a b c; change G (lift5 (head6Value a b c)); rw [lift_head6]; exact cl.head6 _ _ _
    · intro a b c u _; change G (lift5 (rho8Value a b c u)); rw [lift_rho8]; exact unrestrictedRho8 G cl _ _ _ _
    · intro a b c hca hcb
      change G (lift5 (oldBundleValue a b c))
      rw [lift_gate]
      apply cl.gate
      · intro he; exact hca ((lift_eq_iff c a).mp he)
      · intro he; exact hcb ((lift_eq_iff c b).mp he)
    · intro a; change G (lift5 (diagonalValue a)); rw [lift_diagonal]; exact cl.diagonal _

/-- In particular, any modeled primary target refutation transfers to G at
radix-five falsehood. -/
theorem refutationTransport (G : M → Prop) (hG : 𝚺₁-Predicate G) (cl : FiveClosure G)
    (h : TargetProvable (1 : M)) : G 1 := by
  obtain ⟨program,hp⟩ := h
  have ht := proofTransport G hG cl program 1 hp
  simpa only [lift_one] using ht
#print axioms unrestrictedRho8
#print axioms proofTransport
#print axioms refutationTransport
end models
end PA194M5ProofTransport
