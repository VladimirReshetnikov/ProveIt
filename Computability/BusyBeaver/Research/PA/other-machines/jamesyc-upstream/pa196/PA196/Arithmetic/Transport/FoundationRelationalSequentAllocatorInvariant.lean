module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.FoundationRelationalSequentAllocatorBounds
public import PA196.Arithmetic.Transport.FoundationRelationalSequentBinderAlphaNegative
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.RelationalSource
open M6.PA.RelationalSource.Numeric


/-! Exact paired certificate relation and explicit full-PA invariant for
changing only the source translator allocator, under both coverage guards. -/
namespace PA196.Arithmetic.Transport.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCertificateEquivalence

attribute [local irreducible] parametersGraph translateGraph biGraph
noncomputable def allocatorGraph : 𝚺ᴬ₁.Semisentence 8 := .mkSigma
  “forward backward p b f lo other z. ∃ param target a aa,
    !parametersGraph param b f lo z ∧ !parametersGraph target b f other z ∧
    !translateGraph a param p ∧ !translateGraph aa target p ∧ !biGraph forward backward a aa”

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem allocator_graph (forward backward p b f lo other z : V) :
    allocatorGraph.val.Evalb ![forward,backward,p,b,f,lo,other,z] ↔
      BiCertificates forward backward (translate (parameters b f lo z) p)
        (translate (parameters b f other z) p) := by
  simp [allocatorGraph,parameters_graph,translate_graph,bi_graph,Matrix.comp_vecCons'']

attribute [local irreducible] allocatorGraph coverageGraph
noncomputable def allocatorInvariant : ArithmeticSemisentence 1 :=
  “n. ∀ p<n, ∀ b f lo other z, !coverageGraph b f lo z p → !coverageGraph b f other z p →
    ∃ forward backward, !allocatorGraph forward backward p b f lo other z”

theorem allocator_invariant (n : V) : allocatorInvariant.Evalb ![n] ↔
    ∀ p<n, ∀ b f lo other z : V, FormulaCovered b f lo z p → FormulaCovered b f other z p →
      ∃ forward backward, BiCertificates forward backward (translate (parameters b f lo z) p)
        (translate (parameters b f other z) p) := by
  simp [allocatorInvariant,coverage_graph,allocator_graph,Matrix.comp_vecCons'']

/-- Atom translation uses the finite environments and reserve, not allocator. -/
theorem totalAtom_allocator (b f lo other z k r ts : V) :
    totalAtom (parameters b f lo z) k r ts=totalAtom (parameters b f other z) k r ts := by
  simp only [totalAtom,parameters_bound,parameters_free,parameters_reserve]

#print axioms allocator_graph
#print axioms allocator_invariant
#print axioms totalAtom_allocator
end PA196.Arithmetic.Transport.RelationalSource.Numeric

