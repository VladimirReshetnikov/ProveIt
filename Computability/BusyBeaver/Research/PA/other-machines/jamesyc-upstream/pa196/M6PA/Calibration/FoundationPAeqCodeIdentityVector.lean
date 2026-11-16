module
public import M6PA.Theory
public import M6PA.Calibration.FoundationPAeqCodeInductionMatrix
@[expose] public section
/-! Model-valued identity substitution vectors. Adapted from Foundation's
`fvarVec` primitive-recursion construction in Syntax/Term/Typed.lean.
Copyright Foundation contributors; Apache-2.0, as retained in the repository.
The constructors and encoding are the existing Foundation numeric syntax. -/
namespace M6.PA.FoundationPAeqCode
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def boundIdentityBlueprint : PR.Blueprint 0 where
  zero := .mkSigma “y. y = 0”
  succ := .mkSigma “y ih n. ∃ b, !qqBvarDef b n ∧ !concatDef y ih b”
noncomputable def boundIdentityConstruction : PR.Construction V boundIdentityBlueprint where
  zero := fun _=>0
  succ := fun _ n ih=>concat ih (qqBvar n)
  zero_defined := .mk fun v=>by simp [boundIdentityBlueprint]
  succ_defined := .mk fun v=>by simp [boundIdentityBlueprint]
noncomputable def boundIdentity (k : V) : V := boundIdentityConstruction.result ![] k
@[simp] theorem boundIdentity_zero : boundIdentity (0:V)=0 := by
  simp [boundIdentity,boundIdentityConstruction]
@[simp] theorem boundIdentity_succ (k : V) :
    boundIdentity (k+1)=concat (boundIdentity k) (qqBvar k) := by
  simp [boundIdentity,boundIdentityConstruction]
def boundIdentityGraph : 𝚺ᴬ₁.Semisentence 2 := boundIdentityBlueprint.resultDef
instance boundIdentity_defined : 𝚺ᴬ₁-Function₁ (boundIdentity : V→V) via boundIdentityGraph := .mk
  fun v=>by simp [boundIdentityConstruction.result_defined_iff,boundIdentityGraph]; rfl
instance boundIdentity_definable : 𝚺ᴬ₁-Function₁ (boundIdentity : V→V) := boundIdentity_defined.to_definable
@[simp] theorem boundIdentity_length (k : V) : len (boundIdentity k)=k := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih => simp [ih]
theorem boundIdentity_nth (k : V) : ∀ i<k, nth (boundIdentity k) i=qqBvar i := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih =>
    intro i hi
    rcases (lt_succ_iff_le.mp hi).lt_or_eq with hlt|rfl
    · rw [boundIdentity_succ,concat_nth_lt _ _ (by simpa using hlt)]; exact ih i hlt
    · rw [boundIdentity_succ,concat_nth_len' _ _ (by simp)]
theorem boundIdentity_valid {L : Language} [L.Encodable] [L.LORDefinable] (m : V) :
    IsSemitermVec L m m (boundIdentity m) := by
  apply IsSemitermVec.iff.mpr
  refine ⟨by simp,?_⟩
  intro i hi
  rw [boundIdentity_nth m i hi]
  simpa using hi
theorem subst_boundIdentity {L : Language} [L.Encodable] [L.LORDefinable]
    {m p : V} (hp : IsSemiformula L m p) : subst L (boundIdentity m) p=p :=
  subst_eq_self hp (boundIdentity_valid m) (boundIdentity_nth m)

#print axioms boundIdentity_defined
#print axioms boundIdentity_length
#print axioms boundIdentity_nth
#print axioms boundIdentity_valid
#print axioms subst_boundIdentity
end M6.PA.FoundationPAeqCode

