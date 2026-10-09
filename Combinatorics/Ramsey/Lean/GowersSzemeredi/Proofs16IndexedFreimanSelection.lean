import GowersSzemeredi.Proofs16IndexedSelection
import GowersSzemeredi.Proofs16Lemma19Selection

/-! The indexed count removes the factor 256 in the all-new-values
selection lemma, while retaining order-eight Freiman structure. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Choose one function meeting many consistent quadruple prescriptions.
The count is on the original quadruples, rather than their support sets. -/
theorem exists_good_quad_selection {N K : Nat} [NeZero N]
    (U : ZMod N → Finset (ZMod N)) (hne : ∀ x, (U x).Nonempty)
    (hK1 : 1 ≤ K) (hK : ∀ x, (U x).card ≤ K)
    (T : Finset (Fin 4 → ZMod N)) (val : (Fin 4 → ZMod N) → Fin 4 → ZMod N)
    (hval : ∀ q ∈ T, ∀ i, val q i ∈ U (q i))
    (hcons : ∀ q ∈ T, ∀ i j, q i = q j → val q i = val q j) :
    ∃ f : ZMod N → ZMod N, (∀ x, f x ∈ U x) ∧
      T.card ≤ K^4 * (T.filter fun q => ∀ i, f (q i) = val q i).card := by
  have hr : ∀ q ∈ T, (quadRequirement val q).1.card ≤ 4 ∧
      ∀ x ∈ (quadRequirement val q).1, (quadRequirement val q).2 x ∈ U x := by
    intro q hq
    refine ⟨Finset.card_image_le.trans (by simp),?_⟩
    intro x hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    rw [quadRequirement_value (hcons q hq)]
    exact hval q hq i
  obtain ⟨f,hf,hcount⟩ := exists_good_indexed_selection U hne hK1 hK T (quadRequirement val) hr
  have hf' : ∀ x, f x ∈ U x := by simpa only [Fintype.mem_piFinset] using hf
  refine ⟨f,hf',hcount.trans (Nat.mul_le_mul_left _ ?_)⟩
  apply Finset.card_le_card
  intro q hq
  obtain ⟨hqT,hm⟩ := Finset.mem_filter.mp hq
  refine Finset.mem_filter.mpr ⟨hqT,fun i => ?_⟩
  exact (hm (q i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))).trans
    (quadRequirement_value (hcons q hqT) i)

/-- At density `delta*N^3*K^4`, obtain the same quantitative Freiman
piece that the support-image argument required `256*delta*N^3*K^4` for. -/
theorem lemma19_indexed_selection_piece_eight {N K : Nat} [NeZero N] [Fact N.Prime]
    (U W : ZMod N → Finset (ZMod N)) (hWU : ∀ x, W x ⊆ U x)
    (hne : ∀ x, (U x).Nonempty) (hK1 : 1 ≤ K) (hK : ∀ x, (U x).card ≤ K)
    (T : Finset (Fin 4 → ZMod N)) (val : (Fin 4 → ZMod N) → Fin 4 → ZMod N)
    (hadd : ∀ q ∈ T, q 0+q 1 = q 2+q 3 ∧ val q 0+val q 1 = val q 2+val q 3)
    (hW : ∀ q ∈ T, ∀ i, val q i ∈ W (q i))
    (hcons : ∀ q ∈ T, ∀ i j, q i = q j → val q i = val q j)
    {delta : Real} (hdelta : 0 < delta) (hT : delta*(N : Real)^3*K^4 ≤ T.card) :
    ∃ f : ZMod N → ZMod N, (∀ x, f x ∈ U x) ∧
      ∃ E : Finset (ZMod N), (∀ x ∈ E, f x ∈ W x) ∧
        (2 : Real)^(-(1882 : Real))*delta^1164*N ≤ E.card ∧ FreimanHom 8 E f := by
  obtain ⟨f,hf,hcount⟩ := exists_good_quad_selection U hne hK1 hK T val
    (fun q hq i => hWU _ (hW q hq i)) hcons
  let A := Finset.univ.filter fun x => f x ∈ W x
  have henergyCount : (T.filter fun q => ∀ i, f (q i) = val q i).card ≤ phiAdditiveCount A f := by
    apply Finset.card_le_card
    intro q hq
    obtain ⟨hqT,he⟩ := Finset.mem_filter.mp hq
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun i => ?_,(hadd q hqT).1,?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [he]; exact hW q hqT i⟩
    · simpa only [he] using (hadd q hqT).2
  have hcountR : (T.card : Real) ≤ (K : Real)^4*phiAdditiveCount A f := by
    exact_mod_cast hcount.trans (Nat.mul_le_mul_left _ henergyCount)
  have hKpos : (0 : Real) < (K : Real)^4 := by
    have : (0 : Real) < K := by exact_mod_cast (show 0 < K by omega)
    positivity
  have henergy : delta*(N : Real)^3 ≤
      weightedSimultaneousAdditiveEnergy A (fun _ => 1) (fun _ : Fin 1 => f) := by
    rw [energy_eq_phiAdditiveCount]
    apply le_of_mul_le_mul_right (a := (K : Real)^4) _ hKpos
    simpa only [mul_comm ((K : Real)^4)] using hT.trans hcountR
  obtain ⟨E,hEA,hE,hF⟩ := lineFreimanExtraction_eight N A f delta hdelta henergy
  exact ⟨f,hf,E,fun x hx => (Finset.mem_filter.mp (hEA hx)).2,hE,hF⟩

end LeanProofs.GowersSzemeredi
