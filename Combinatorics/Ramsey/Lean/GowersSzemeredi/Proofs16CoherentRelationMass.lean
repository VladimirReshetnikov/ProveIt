import GowersSzemeredi.Proofs16CoherentRelationLevels
import GowersSzemeredi.Proofs16CoherentFrequencyFamily
import GowersSzemeredi.Proofs16DifferenceStars

/-! Dense coherent quadruples yield a dense symmetric pair relation,
partitioned exactly into graphs with a fixed index difference. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def coherentPairRelations {N ell : Nat} [NeZero N] (X B : Finset (ZMod N))
    (theta : Fin ell → ZMod N → ZMod N) (F : ZMod N → ZMod N → ZMod N)
    (sigma : Real) (i : Nat) : Finset ((ZMod N × ZMod N) × (ZMod N × ZMod N)) :=
  Finset.univ.filter fun pq => CoherentRelationLevel X B theta F sigma i pq.1 pq.2

theorem CoherentFrequencyFamily.relation_mass {N ell : Nat} [NeZero N]
    {X B : Finset (ZMod N)} {theta : Fin ell → ZMod N → ZMod N}
    {F : ZMod N → ZMod N → ZMod N} {sigma : Real} {Q : Finset (Fin 4 → ZMod N)}
    (h : CoherentFrequencyFamily X B theta F sigma Q) :
    Q.card ≤ (coherentPairRelations X B theta F sigma 1).card := by
  let code := fun a : Fin 4 → ZMod N => ((a 0,a 2),(a 3,a 1))
  have hinj : Function.Injective code := by
    intro a b hab
    funext j
    fin_cases j
    · exact congrArg (fun p : (ZMod N × ZMod N) × (ZMod N × ZMod N) => p.1.1) hab
    · exact congrArg (fun p : (ZMod N × ZMod N) × (ZMod N × ZMod N) => p.2.2) hab
    · exact congrArg (fun p : (ZMod N × ZMod N) × (ZMod N × ZMod N) => p.1.2) hab
    · exact congrArg (fun p : (ZMod N × ZMod N) × (ZMod N × ZMod N) => p.2.1) hab
  have hsub : Q.image code ⊆ coherentPairRelations X B theta F sigma 1 := by
    intro p hp
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hp
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    have hq := h.2 a ha
    refine ⟨⟨hq.2.1 0,hq.2.1 2⟩,⟨hq.2.1 3,hq.2.1 1⟩,?_,?_⟩
    · change a 0-a 2 = a 3-a 1
      linear_combination hq.1
    · simp only [coherentRelationRadius,Nat.sub_self,pow_zero,div_one]
      intro z h0 h2 h3 h1
      have he := hq.2.2 z (by intro j; fin_cases j <;> assumption)
      change F (a 0) z-F (a 2) z = F (a 3) z-F (a 1) z
      linear_combination he
  rw [← Finset.card_image_of_injective Q hinj]
  exact Finset.card_le_card hsub

def coherentDifferenceEdges {N ell : Nat} [NeZero N] (X B : Finset (ZMod N))
    (theta : Fin ell → ZMod N → ZMod N) (F : ZMod N → ZMod N → ZMod N)
    (sigma : Real) (i : Nat) (a : ZMod N) : Finset (ZMod N × ZMod N) :=
  Finset.univ.filter fun uv => CoherentRelationLevel X B theta F sigma i (uv.1+a,uv.1) (uv.2+a,uv.2)

theorem coherentDifferenceEdges_subset {N ell : Nat} [NeZero N]
    (X B : Finset (ZMod N)) (theta : Fin ell → ZMod N → ZMod N)
    (F : ZMod N → ZMod N → ZMod N) (sigma : Real) (i : Nat) (a : ZMod N) :
    coherentDifferenceEdges X B theta F sigma i a ⊆ X ×ˢ X := by
  intro uv h
  have hr := (Finset.mem_filter.mp h).2
  exact Finset.mem_product.mpr ⟨hr.1.2,hr.2.1.2⟩

theorem coherentDifferenceEdges_symm {N ell : Nat} [NeZero N]
    (X B : Finset (ZMod N)) (theta : Fin ell → ZMod N → ZMod N)
    (F : ZMod N → ZMod N → ZMod N) (sigma : Real) (i : Nat) (a : ZMod N)
    {p : ZMod N × ZMod N} (hp : p ∈ coherentDifferenceEdges X B theta F sigma i a) :
    p.swap ∈ coherentDifferenceEdges X B theta F sigma i a :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _,CoherentRelationLevel.symm (Finset.mem_filter.mp hp).2⟩

theorem coherentDifferenceEdges_sum {N ell : Nat} [NeZero N]
    (X B : Finset (ZMod N)) (theta : Fin ell → ZMod N → ZMod N)
    (F : ZMod N → ZMod N → ZMod N) (sigma : Real) (i : Nat) :
    (∑ a : ZMod N, (coherentDifferenceEdges X B theta F sigma i a).card) =
      (coherentPairRelations X B theta F sigma i).card := by
  have h := difference_relation_card (CoherentRelationLevel X B theta F sigma i) (fun p q h => h.2.2.1)
  unfold coherentPairRelations
  rw [← h]
  simp only [coherentDifferenceEdges,Finset.card_filter,Fintype.sum_prod_type,differencePair]
  simp only [add_comm]

end LeanProofs.GowersSzemeredi
