import GowersSzemeredi.Proofs16JointSelectionState

/-! A concrete escaping map extends the common selection state. Both
improvement routes use this lemma to preserve coverage and rank growth. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem PairSelectionState.extend_joint {N d : Nat} [NeZero N]
    (s : PairSelectionState N) (T : ZMod N → Finset (ZMod N)) {delta r : Real}
    (hs : s.JointValid T delta d r) (g : PairFrequencyMap N)
    (E : Finset (ZMod N × ZMod N)) (hg : g.JointControlled delta d r)
    (hE : jointSelectionGain delta d r*(N : Real)^2 ≤ E.card)
    (hvalue : ∀ p ∈ E, p.1-p.2 ∈ g.domain ∧
      g.toFun (p.1-p.2) ∈ boundedFrequencySpan (fun a : ↥(T p.1 ∪ T p.2) => (a : ZMod N))
        (jointSelectionCutoff d r) ∧
      g.toFun (p.1-p.2) ∉ boundedFrequencySpan (fun a : s.frequencies p => (a : ZMod N)) 1) :
    ∃ s' : PairSelectionState N, s'.JointValid T delta d r ∧
      s'.maps.length = s.maps.length+1 ∧
      (∀ p, s.frequencies p ⊆ s'.frequencies p) ∧ s'.maps = g :: s.maps := by
  have hnew := extendIndependentFamily_properties s.frequencies (fun p => T p.1 ∪ T p.2)
    E (fun p => g.toFun (p.1-p.2)) (jointSelectionCutoff d r)
    (fun p => (hs.2.1 p).1) (fun p => (hs.2.1 p).2) (fun p hp => (hvalue p hp).2)
  have hsum := extendIndependentFamily_total_card s.frequencies Finset.univ E
    (fun p => g.toFun (p.1-p.2)) (Finset.subset_univ _) (fun p hp => (hvalue p hp).2.2)
  let F' := extendIndependentFamily s.frequencies E (fun p => g.toFun (p.1-p.2))
  let s' : PairSelectionState N := ⟨g :: s.maps,F'⟩
  have hvalid : s'.JointValid T delta d r := by
    refine ⟨?_,fun p => ⟨(hnew p).1,(hnew p).2.1⟩,?_,?_⟩
    · intro u hu
      rcases List.mem_cons.mp hu with rfl | hu
      · exact hg
      · exact hs.1 u hu
    · intro p v hv
      change v ∈ extendIndependentFamily s.frequencies E (fun p => g.toFun (p.1-p.2)) p at hv
      by_cases hp : p ∈ E
      · simp only [extendIndependentFamily,if_pos hp] at hv
        rcases Finset.mem_insert.mp hv with rfl | hv
        · exact ⟨g,List.mem_cons_self,(hvalue p hp).1,rfl⟩
        · obtain ⟨u,hu,hdom,hval⟩ := hs.2.2.1 p v hv
          exact ⟨u,List.mem_cons_of_mem _ hu,hdom,hval⟩
      · simp only [extendIndependentFamily,if_neg hp] at hv
        obtain ⟨u,hu,hdom,hval⟩ := hs.2.2.1 p v hv
        exact ⟨u,List.mem_cons_of_mem _ hu,hdom,hval⟩
    · have hsumR : (∑ p : ZMod N × ZMod N, ((F' p).card : Real)) =
          (∑ p : ZMod N × ZMod N, ((s.frequencies p).card : Real))+(E.card : Real) := by
        exact_mod_cast hsum
      have hold := hs.2.2.2
      change (((g :: s.maps).length : Nat) : Real)*jointSelectionGain delta d r*(N : Real)^2 ≤ _
      simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
      change ((s.maps.length : Real)+1)*jointSelectionGain delta d r*(N : Real)^2 ≤
        ∑ p : ZMod N × ZMod N, ((F' p).card : Real)
      rw [hsumR]
      nlinarith only [hold,hE]
  exact ⟨s',hvalid,rfl,fun p => (hnew p).2.2,rfl⟩


end LeanProofs.GowersSzemeredi
