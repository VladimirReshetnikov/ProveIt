import GowersSzemeredi.Proofs16Translations
import GowersSzemeredi.Proofs16FaceInduction

/-! Transport the selected common-base domain and its all-ones graph back
into the original relation without cardinality or cover-parameter loss.

`section16PhiOne_eq_translate` and `section16_good_domain_subrelation` are in
`Proofs16GoodDomainTransportSide`, outside the final route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem section16GoodDomain_card {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (H : Finset (Point N k))
    (Y : (h : Point N k) → Finset (Section16CubeElement B h)) (x0 : Point N k) :
    (section16GoodDomain B H Y x0).card = section16GoodInducedPairCount B H Y x0 := by
  unfold section16GoodDomain section16GoodInducedPairCount countWhere
  apply Finset.card_bij (fun z _ => (section16Init z, section16Last z))
  · intro z hz
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hz
  · intro z _ w _ heq
    have hi := congrArg Prod.fst heq
    have hl := congrArg Prod.snd heq
    dsimp only at hi hl
    have hz' : appendCoordinate (section16Init z) (section16Last z) = z := by
      rw [appendCoordinate_eq_snoc]; exact Fin.snoc_init_self z
    have hw' : appendCoordinate (section16Init w) (section16Last w) = w := by
      rw [appendCoordinate_eq_snoc]; exact Fin.snoc_init_self w
    rw [← hz', ← hw', hi, hl]
  · intro z hz
    refine ⟨appendCoordinate z.1 z.2, ?_, ?_⟩
    · simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
        section16Init_appendCoordinate, section16Last_appendCoordinate] using hz
    · simp

/-- Every translated vertex of a selected cube still lies in the original
partial-function domain. -/
theorem section16GoodDomain_vertex_mem {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (H : Finset (Point N k))
    (Y : (h : Point N k) → Finset (Section16CubeElement B h)) (x0 : Point N k)
    {z : Point N (k + 1)} (hz : z ∈ section16GoodDomain B H Y x0)
    (e : Fin k → Bool) :
    appendCoordinate (fun i => x0 i + if e i then section16Init z i else 0)
      (section16Last z) ∈ B := by
  classical
  obtain ⟨_, C, _, hbase, hx⟩ := (Finset.mem_filter.mp hz).2
  have hC := (Finset.mem_filter.mp C.property).2
  have hh := hC.2 e
  change appendCoordinate (fun i => C.val.1.base i + if e i then C.val.1.side i else 0)
    C.val.2 ∈ B at hh
  simpa only [hbase, hC.1, hx] using hh

end LeanProofs.GowersSzemeredi
