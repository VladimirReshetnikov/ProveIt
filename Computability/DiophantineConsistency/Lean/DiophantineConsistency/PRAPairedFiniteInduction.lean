import DiophantineConsistency.PRAPairedTwoInduction
/-! A finite list of parameter-dependent bounded matrices can be nested into
one paired matrix, without primitive-recursive pairing function codes. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace DiophantineConsistency.PRAPairedFiniteInduction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAOpenOneInduction
  PRABoundedOneInduction PRAPairedInductionMatrix PRAPairedInductionSemantics

def dispatch : List (Semisentence language 3) → Semisentence language 3
  | [] => pairGraph
  | ψ :: rest => pairedMatrix ψ (dispatch rest)

theorem dispatch_bounded (fs : List (Semisentence language 3))
    (h : ∀ ψ ∈ fs, Hierarchy 𝚺 0 ψ) : Hierarchy 𝚺 0 (dispatch fs) := by
  induction fs with
  | nil => exact pairGraph_bounded
  | cons ψ rest ih =>
    exact pairedMatrix_bounded ψ (dispatch rest) (h ψ (List.mem_cons_self))
      (ih (fun φ hφ => h φ (List.mem_cons_of_mem _ hφ)))

theorem modelDispatchSuccInd {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
    [M↓[language] ⊧* PRA] (fs : List (Semisentence language 3)) (ψ : Semisentence language 3)
    (hψ : ψ ∈ fs) (h : M↓[language] ⊧ (succInd (openSigma (dispatch fs))).univCl) :
    M↓[language] ⊧ (succInd (openSigma ψ)).univCl := by
  induction fs with
  | nil => simp at hψ
  | cons a rest ih =>
    simp only [List.mem_cons] at hψ
    change M↓[language] ⊧ (succInd (openSigma (pairedMatrix a (dispatch rest)))).univCl at h
    rcases hψ with hEq | hψ
    · subst ψ
      exact modelPairedSuccInd_zero a (dispatch rest) h
    · exact ih hψ (modelPairedSuccInd_one a (dispatch rest) h)

def inductionAxioms (fs : List (Semisentence language 3)) : Theory language :=
  {σ | ∃ ψ ∈ fs, σ = (succInd (openSigma ψ)).univCl}

theorem PRA_proves_goal_of_finite_boundedSuccInd
    (fs : List (Semisentence language 3)) (hfs : ∀ ψ ∈ fs, Hierarchy 𝚺 0 ψ)
    (θ : Semiproposition language 1) (hθ : θ.Open)
    (p : (PRA ∪ inductionAxioms fs) ⊢ (∃⁰ θ).univCl) :
    PRA ⊢ (∃⁰ θ).univCl := by
  have hp : (PRA ∪ {(succInd (openSigma (dispatch fs))).univCl}) ⊢ (∃⁰ θ).univCl := by
    apply PRA_proof_of_model_axiom_replacement _ _ _ ?_ p
    intro M _ _ _ _ hdisp
    constructor
    intro σ hσ
    obtain ⟨ψ,hψ,rfl⟩ := hσ
    exact modelDispatchSuccInd fs ψ hψ hdisp
  exact PRA_proves_goal_of_boundedSuccInd (dispatch fs) (dispatch_bounded fs hfs) θ hθ hp
end DiophantineConsistency.PRAPairedFiniteInduction
