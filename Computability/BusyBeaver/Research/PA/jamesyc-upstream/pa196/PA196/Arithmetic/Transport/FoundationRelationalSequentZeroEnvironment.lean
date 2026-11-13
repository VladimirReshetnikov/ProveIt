module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.FoundationRelationalSequentProofBudget
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.RelationalSource
open M6.PA.RelationalSource.Numeric


/-! A genuine model-length HFS vector of zero labels, not a host list. -/
namespace PA196.Arithmetic.Transport.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def zeroEnvironmentBlueprint : PR.Blueprint 0 where
  zero := .mkSigma “out. out=0”
  succ := .mkSigma “out previous i. !adjoinDef out 0 previous”

noncomputable def zeroEnvironmentConstruction : PR.Construction V zeroEnvironmentBlueprint where
  zero := fun _ => 0
  succ := fun _ _ previous => 0∷previous
  zero_defined := .mk fun v => by simp [zeroEnvironmentBlueprint]
  succ_defined := .mk fun v => by simp [zeroEnvironmentBlueprint]

noncomputable def zeroEnvironment (n : V) : V := zeroEnvironmentConstruction.result ![] n
noncomputable def zeroEnvironmentGraph : 𝚺ᴬ₁.Semisentence 2 := zeroEnvironmentBlueprint.resultDef

theorem zeroEnvironment_graph (out n : V) :
    zeroEnvironmentGraph.val.Evalb ![out,n] ↔ out=zeroEnvironment n := by
  simpa [zeroEnvironmentGraph,zeroEnvironment,Matrix.comp_vecCons''] using!
    zeroEnvironmentConstruction.result_defined_iff ![out,n]

@[simp] theorem zeroEnvironment_zero : zeroEnvironment (0:V)=0 := by
  simp [zeroEnvironment,zeroEnvironmentConstruction]
@[simp] theorem zeroEnvironment_succ (n : V) : zeroEnvironment (n+1)=0∷zeroEnvironment n := by
  simp [zeroEnvironment,zeroEnvironmentConstruction]

#print axioms zeroEnvironment_graph
#print axioms zeroEnvironment_zero
#print axioms zeroEnvironment_succ
end PA196.Arithmetic.Transport.RelationalSource.Numeric

