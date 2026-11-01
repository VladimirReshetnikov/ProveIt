import DiophantineConsistency.AdaptiveNamedValues50Coordinates
import DiophantineConsistency.AdaptiveZ46Model
import DiophantineConsistency.AdaptiveZ44Model
import DiophantineConsistency.AdaptiveZ43Model
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveVSignTransport43
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem from42 (p : Fin 4 → ℕ) (hb : (2:V)≤(p 0:V)) (v : Fin 42 → V)
    (hv : ∀ i, 0<v i)
    (hz : InternalZero (AdaptiveNamedValues42.literal (fun j => (p j:ℤ))) v)
    (hsign : v 31 < v 30) :
    ∃ u : Fin 43 → V, (∀ i,0<u i) ∧
      InternalZero (AdaptiveZ43Context.literal (fun j => (p j:ℤ))) u ∧ u 26 < u 25 := by
  have hb0 : 0<(p 0:V) := lt_of_lt_of_le (by norm_num) hb
  have gap := AdaptiveRankSeedPositive50.gap42 p v hb0 hv hz
  have hF : v 1≤1+v 0*(p 0:V) := le_trans (by simp : v 1≤v 1+v 2) (le_of_lt gap)
  let rank : V := v 2+((1+v 0*(p 0:V))-v 1)*(v 0*(p 0:V))
  have hRankRep : SignedRep (AdaptiveNamedValues50.expression1 (fun j => (p j:ℤ))) v (natural rank) :=
    AdaptiveRankSeedPositive50.rank_rep p v hF
  have hrank : 0<rank := by dsimp [rank]; exact add_pos_of_pos_of_nonneg (hv 2) (Arithmetic.zero_le _)
  obtain ⟨v50,h50,z50,he⟩ := AdaptiveNamedValues50.exists_positive_extension_with_embedding
    (fun j => (p j:ℤ)) v hv hz rank hrank hRankRep
  have h30 : v50 30 = v 30 := by
    have hh := he (30 : Fin 42)
    have hi : AdaptiveNamedValues50.embed (30 : Fin 42) = (30 : Fin 50) := by decide
    rw [hi] at hh
    exact hh
  have h31 : v50 31 = v 31 := by
    have hh := he (31 : Fin 42)
    have hi : AdaptiveNamedValues50.embed (31 : Fin 42) = (31 : Fin 50) := by decide
    rw [hi] at hh
    exact hh
  have s50 : v50 31 < v50 30 := by rw [h30,h31]; exact hsign
  let v49 := AdaptiveCombined49Model.collapse v50
  have h49 := AdaptiveCombined49Model.collapse_pos v50 h50
  have z49 := AdaptiveCombined49Model.collapse_zero _ v50 z50
  let v47 := AdaptiveNamedValues47Maps.project v49
  have h47 := AdaptiveNamedValues47Maps.project_pos v49 h49
  have z49' : InternalZero (AdaptiveNamedValues49.literal (fun j => (p j:ℤ))) v49 := by
    rw [AdaptiveNamedValues49.literal_eq]
    exact z49
  have z47 := AdaptiveNamedValues47Model.collapse_zero (fun j => (p j:ℤ)) v49 z49' 
  obtain ⟨r,hr,hmag,z46⟩ := AdaptiveZ46Model.project_zero _ v47 h47 z47
  let v46 := AdaptiveZ46Maps.project v47 r
  have h46 := AdaptiveZ46Maps.project_pos v47 r h47 hr hmag
  let v44 := AdaptiveZ44Maps.project v46
  have h44 := AdaptiveZ44Maps.project_pos p v46 h46 z46
  have z44 := AdaptiveZ44Model.project_zero p v46 h46 z46
  let v43 := AdaptiveZ43Maps.project v44
  have h43 := AdaptiveZ43Maps.project_pos p v44 hb h44 z44
  have z43 := AdaptiveZ43Model.project_zero p v44 hb h44 z44
  refine ⟨v43,h43,z43,?_⟩
  change v50 31 < v50 30
  exact s50
#print axioms from42
end DiophantineConsistency.AdaptiveVSignTransport43
