import GowersSzemeredi.Proofs16PairSelectionState

/-! A dense failure family extends the recorded list by one actual
Freiman map and preserves all selection and growth invariants. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem PairSelectionState.improve {N d : Nat} [NeZero N] [Fact N.Prime]
    (s : PairSelectionState N) (C : Finset (Fin 4 → ZMod N))
    (T : ZMod N → Finset (ZMod N)) {delta r : Real}
    (hd : 0 < delta) (hr : 0 < r) (hr4 : r < 4)
    (hT : ∀ x, (T x).card ≤ d) (hadd : ∀ q ∈ C, q 0-q 1 = q 2-q 3)
    (hs : s.Valid T delta d r)
    (hbad : delta*(N : Real)^3 ≤ (pairSelectionFailures C T s d r).card) :
    ∃ s' : PairSelectionState N, s'.Valid T delta d r ∧
      s'.maps.length = s.maps.length+1 ∧
      (∀ p, s.frequencies p ⊆ s'.frequencies p) ∧
      ∃ g : PairFrequencyMap N, s'.maps = g :: s.maps := by
  let B := pairSelectionFailures C T s d r
  obtain ⟨P,a,theta,E,hPrank,hPproper,hPmass,htheta,_,hE,hvalue,hnew,hsum,_⟩ :=
    failed_pair_containments_increase_rank B T s.frequencies hr hr4 hd hbad
      (fun q hq => hadd q (Finset.mem_filter.mp hq).1) hT
      (fun p => (hs.2.1 p).1) (fun p => (hs.2.1 p).2)
      (fun q _ => pair_selection_radius_budget T s.frequencies r hT
        (fun p => (hs.2.1 p).1) (fun p => (hs.2.1 p).2) q)
      (fun q hq => (Finset.mem_filter.mp hq).2)
  let g : PairFrequencyMap N := ⟨P,a,theta⟩
  let F' := extendIndependentFamily s.frequencies E (fun p => theta (p.1-p.2))
  let s' : PairSelectionState N := ⟨g :: s.maps,F'⟩
  have hvalid : s'.Valid T delta d r := by
    refine ⟨?_,fun p => ⟨(hnew p).1,(hnew p).2.1⟩,?_,?_⟩
    · intro u hu
      rcases List.mem_cons.mp hu with rfl | hu
      · exact ⟨hPrank,hPproper,hPmass,htheta⟩
      · exact hs.1 u hu
    · intro p v hv
      change v ∈ extendIndependentFamily s.frequencies E (fun p => theta (p.1-p.2)) p at hv
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
      change pairSelectionGain delta d r*(N : Real)^2 ≤ E.card at hE
      change (((g :: s.maps).length : Nat) : Real)*pairSelectionGain delta d r*(N : Real)^2 ≤ _
      simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
      change ((s.maps.length : Real)+1)*pairSelectionGain delta d r*(N : Real)^2 ≤
        ∑ p : ZMod N × ZMod N, ((F' p).card : Real)
      rw [hsumR]
      nlinarith only [hold,hE]
  exact ⟨s',hvalid,rfl,fun p => (hnew p).2.2,g,rfl⟩

end LeanProofs.GowersSzemeredi
