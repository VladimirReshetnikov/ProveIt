import DiophantineConsistency.PRAMultiParameterInduction
import DiophantineConsistency.PRAPairedFiniteInduction
/-! A finite list of bounded induction instances with independent finite arities. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace DiophantineConsistency.PRAFiniteMultiParameterInduction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAOpenOneInduction
  PRAParameterPackingN PRAMultiParameterInduction PRAPairedFiniteInduction

structure Descriptor where
  arity : ℕ
  matrix : Semisentence language (3+arity)

def inductionAxioms (fs : List Descriptor) : Theory language :=
  {σ | ∃ d ∈ fs, σ = (succInd (multiSigma d.arity d.matrix)).univCl}

def packedMatrices (fs : List Descriptor) : List (Semisentence language 3) :=
  fs.map (fun d => packAll d.arity d.matrix)

theorem packedMatrices_bounded (fs : List Descriptor)
    (hfs : ∀ d ∈ fs, Hierarchy 𝚺 0 d.matrix) :
    ∀ ψ ∈ packedMatrices fs, Hierarchy 𝚺 0 ψ := by
  intro ψ hψ
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hψ
  exact packAll_bounded d.arity d.matrix (hfs d hd)

/-- Eliminate any finite list of bounded-matrix induction instances, each with
its own finite parameter arity, from an actual candidate-PRA proof of an
open-existential goal. -/
theorem PRA_proves_goal_of_finite_induction
    (fs : List Descriptor) (hfs : ∀ d ∈ fs, Hierarchy 𝚺 0 d.matrix)
    (θ : Semiproposition language 1) (hθ : θ.Open)
    (p : (PRA ∪ inductionAxioms fs) ⊢ (∃⁰ θ).univCl) :
    PRA ⊢ (∃⁰ θ).univCl := by
  have hp : (PRA ∪ PRAPairedFiniteInduction.inductionAxioms (packedMatrices fs)) ⊢
      (∃⁰ θ).univCl := by
    apply PRAOpenOneInduction.PRA_proof_of_model_theory_replacement _ _ _ ?_ p
    intro M _ _ _ _ hU
    constructor
    intro σ hσ
    obtain ⟨d,hd,rfl⟩ := hσ
    have hp' : M↓[language] ⊧ (succInd (openSigma (packAll d.arity d.matrix))).univCl :=
      hU.models _ ⟨packAll d.arity d.matrix, List.mem_map.mpr ⟨d,hd,rfl⟩,rfl⟩
    exact modelMultiInduction d.arity d.matrix hp'
  exact PRA_proves_goal_of_finite_boundedSuccInd (packedMatrices fs) (packedMatrices_bounded fs hfs) θ hθ hp
end DiophantineConsistency.PRAFiniteMultiParameterInduction
