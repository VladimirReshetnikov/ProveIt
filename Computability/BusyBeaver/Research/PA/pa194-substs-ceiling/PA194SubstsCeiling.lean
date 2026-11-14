import PA194QVecCeiling
import PA196PASubstitutionWitnessComplete
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace PA194SubstsCeiling
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open StrictSigmaOneInduction
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAWitnessCalculus PA194QVecCeiling
theorem arithmetic_substs_bounded_is_sigma0 :
    Hierarchy 𝚺 0 (bnd (substsGraph ℒₒᵣ).val) :=
  hierarchy_bnd (substsGraph ℒₒᵣ).sigma_prop (by decide) (by intro _; rfl)

theorem bounded_graph_pair_is_sigma0 {n : Nat} (φ ψ : 𝚺₁.Semisentence n) :
    Hierarchy 𝚺 0 (bnd φ.val ⋏ bnd ψ.val) :=
  Hierarchy.and (hierarchy_bnd φ.sigma_prop (by decide) (by intro _; rfl))
    (hierarchy_bnd ψ.sigma_prop (by decide) (by intro _; rfl))

variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem uniform_substs_witness_bound (ceiling : M) :
    ∃ bound : M, ∀ e : Fin 3 → M, (∀ i, e i ≤ ceiling) →
      (substsGraph ℒₒᵣ).val.Eval e Empty.elim →
      (bnd (substsGraph ℒₒᵣ).val).Eval (Fin.snoc e bound) Empty.elim := by
  obtain ⟨B,hmono,hbound⟩ := PA196PASubstitutionWitnessComplete.wb_substsGraph (M := M)
  refine ⟨B (fun _ => ceiling), ?_⟩
  intro e he hgraph
  exact eval_bnd_mono _ e Empty.elim (hmono e (fun _ => ceiling) he) (hbound e hgraph)

theorem qVec_trace_and_substs_ceiling (seed limit : M) :
    ∃ qs bound : M,
      (PA196PAQVecSeqTrace.construction (V := M)).CSeq ![seed] qs ∧
      limit + 1 = lh qs ∧
      (∀ i ≤ limit, znth qs i ≤ PA196PAQVecTowerAlgebra.iter limit seed) ∧
      (∀ e : Fin 3 → M, (∀ j, e j ≤ PA196PAQVecTowerAlgebra.iter limit seed) →
        (substsGraph ℒₒᵣ).val.Eval e Empty.elim →
        (bnd (substsGraph ℒₒᵣ).val).Eval (Fin.snoc e bound) Empty.elim) := by
  obtain ⟨qs,hq,hl,htrace⟩ := bounded_trace seed limit
  obtain ⟨bound,hbound⟩ := uniform_substs_witness_bound (PA196PAQVecTowerAlgebra.iter limit seed)
  exact ⟨qs,bound,hq,hl,htrace,hbound⟩

#print axioms arithmetic_substs_bounded_is_sigma0
#print axioms bounded_graph_pair_is_sigma0
#print axioms qVec_trace_and_substs_ceiling
#print axioms uniform_substs_witness_bound
end PA194SubstsCeiling
