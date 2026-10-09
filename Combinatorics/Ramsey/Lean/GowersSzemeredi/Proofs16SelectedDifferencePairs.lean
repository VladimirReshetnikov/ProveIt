import GowersSzemeredi.Proofs16PopularCoherentDifferences

/-! Selecting coherent cliques in many difference fibres yields a dense
pair family. The difference coordinate makes the union disjoint. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def selectedDifferencePairs {N : Nat} (D : Finset (ZMod N)) (S : ZMod N → Finset (ZMod N)) :
    Finset (ZMod N × ZMod N) := (D.sigma S).image (fun p => (p.2+p.1,p.2))

theorem selectedDifferencePairs_card {N : Nat} (D : Finset (ZMod N)) (S : ZMod N → Finset (ZMod N)) :
    (selectedDifferencePairs D S).card = ∑ a ∈ D, (S a).card := by
  have hinj : Function.Injective (fun p : Sigma (fun _ : ZMod N => ZMod N) => (p.2+p.1,p.2)) := by
    intro p q hpq
    have hu : p.2 = q.2 := congrArg Prod.snd hpq
    have ha : p.2+p.1 = q.2+q.1 := congrArg Prod.fst hpq
    have hd : p.1 = q.1 := add_left_cancel (hu ▸ ha)
    exact Sigma.ext hd (heq_of_eq hu)
  rw [selectedDifferencePairs,Finset.card_image_of_injective _ hinj,Finset.card_sigma]

theorem CoherentBridgeSystem.dense_pairs {N ell depth : Nat} [NeZero N]
    {X B : Finset (ZMod N)} {theta : Fin ell → ZMod N → ZMod N}
    {F : ZMod N → ZMod N → ZMod N} {sigma eta kappa : Real} {Q : Finset (Fin 4 → ZMod N)}
    (h : CoherentBridgeSystem B X theta F sigma eta depth) (he : 0 < eta) (hdepth : 1 ≤ depth)
    (hfamily : CoherentFrequencyFamily X B theta F sigma Q) (hk : 0 < kappa)
    (hmass : kappa*(N : Real)^3 ≤ Q.card) (hsmall : eta ≤ kappa^2/256) :
    ∃ P : Finset (ZMod N × ZMod N), P ⊆ X ×ˢ X ∧
      (3*kappa^2/32)*(N : Real)^2 ≤ P.card ∧
      ∀ p ∈ P, ∀ q ∈ P, p.1-p.2 = q.1-q.2 → CoherentRelationLevel X B theta F sigma 3 p q := by
  let D := popularCoherentDifferences X B theta F sigma kappa
  have hD : kappa*N/2 ≤ (D.card : Real) := popularCoherentDifferences_dense hfamily hk.le hmass
  have hk1 := hfamily.density_le_one hmass
  have hcodegree : eta ≤ (kappa/2)^2/64 := by nlinarith only [hsmall]
  have hpartners : eta ≤ (kappa/2)/4 := by nlinarith [hsmall,mul_nonneg hk.le (sub_nonneg.mpr hk1)]
  have hex (a : ZMod N) : ∃ T : Finset (ZMod N), a ∈ D →
      T ⊆ X ∧ (∀ u ∈ T, u+a ∈ X) ∧ 3*(kappa/2)*N/8 ≤ (T.card : Real) ∧
      ∀ u ∈ T, ∀ v ∈ T, CoherentRelationLevel X B theta F sigma 3 (u+a,u) (v+a,v) := by
    by_cases ha : a ∈ D
    · obtain ⟨T,hTX,hTa,hT,hcl⟩ := h.fibre_clique he hdepth (half_pos hk) hcodegree hpartners a (Finset.mem_filter.mp ha).2
      exact ⟨T,fun _ => ⟨hTX,hTa,hT,hcl⟩⟩
    · exact ⟨∅,fun ha' => False.elim (ha ha')⟩
  choose S hS using hex
  refine ⟨selectedDifferencePairs D S,?_,?_,?_⟩
  · intro p hp
    obtain ⟨⟨a,u⟩,hmem,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨ha,hu⟩ := Finset.mem_sigma.mp hmem
    exact Finset.mem_product.mpr ⟨(hS a ha).2.1 u hu,(hS a ha).1 hu⟩
  · have hsum : (D.card : Real)*(3*(kappa/2)*N/8) ≤ ∑ a ∈ D, ((S a).card : Real) := by
      calc _ = ∑ _a ∈ D, (3*(kappa/2)*N/8) := by simp
        _ ≤ _ := Finset.sum_le_sum fun a ha => (hS a ha).2.2.1
    have hc : ((selectedDifferencePairs D S).card : Real) = ∑ a ∈ D, ((S a).card : Real) := by
      exact_mod_cast selectedDifferencePairs_card D S
    rw [hc]
    have hd := mul_le_mul_of_nonneg_right hD (show 0 ≤ 3*(kappa/2)*N/8 by positivity)
    nlinarith only [hd,hsum]
  · intro p hp q hq hd
    obtain ⟨⟨a,u⟩,ha,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨⟨b,v⟩,hb,rfl⟩ := Finset.mem_image.mp hq
    have hab : a = b := by simpa only [add_sub_cancel_left] using hd
    subst b
    obtain ⟨haD,hu⟩ := Finset.mem_sigma.mp ha
    obtain ⟨_,hv⟩ := Finset.mem_sigma.mp hb
    exact (hS a haD).2.2.2 u hu v hv

end LeanProofs.GowersSzemeredi
