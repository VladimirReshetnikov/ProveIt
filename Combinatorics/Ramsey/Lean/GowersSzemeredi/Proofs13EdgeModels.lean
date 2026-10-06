import GowersSzemeredi.Proofs13CommonStepSelection
import GowersSzemeredi.Proofs10Main

/-! Exact transport between height arrangements and the finite multifunction
domain of vertical edges. This supplies the approximate-homomorphism input
to Theorem 10.13 from a good height in Section 13. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The actual finite type of vertical edges at a fixed height. -/
abbrev Section13Edges {N : Nat} [NeZero N] (A : Finset (Pair N)) (h : ZMod N) :=
  {z : Pair N // z ∈ verticalEdgeDomain A h}

/-- Vertical edges are indexed by their first coordinate. -/
def section13VerticalDomain {N : Nat} [NeZero N] (A : Finset (Pair N)) (h : ZMod N) :
    MultifunctionDomain N (Section13Edges A h) where
  index z := z.val.1

/-- An edge tuple with its common height, in the arrangement representation. -/
def section13EdgeArrangement {N k : Nat} [NeZero N] {A : Finset (Pair N)} {h : ZMod N}
    (x : Fin (2 * k) → Section13Edges A h) : DArrangement N k :=
  (fun i ↦ (x i).val.1, fun i ↦ (x i).val.2, h)

/-- The tuple-to-arrangement correspondence preserves any additional
predicate, so both total and respected counts transport through one bijection. -/
theorem section13_edge_tuple_count {N k : Nat} [NeZero N]
    (A : Finset (Pair N)) (h : ZMod N) (P : DArrangement N k → Prop) :
    countWhere (fun x : Fin (2 * k) → Section13Edges A h ↦
      HasEqualHalfSums (fun i ↦ (section13VerticalDomain A h).index (x i)) ∧
        P (section13EdgeArrangement x)) =
    countWhere (fun R : DArrangement N k ↦ R.IsIn A ∧ R.height = h ∧ P R) := by
  classical
  unfold countWhere
  apply Finset.card_bij (fun x _ ↦ section13EdgeArrangement x)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    obtain ⟨hxadd, hxP⟩ := hx
    refine ⟨⟨hxadd, ?_⟩, rfl, hxP⟩
    intro i
    exact (Finset.mem_filter.mp (x i).property).2
  · intro x hx y hy hxy
    funext i
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun R : DArrangement N k ↦ R.x i) hxy
    · exact congrArg (fun R : DArrangement N k ↦ R.y i) hxy
  · intro R hR
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hR
    obtain ⟨hRin, hheight, hRP⟩ := hR
    let x : Fin (2 * k) → Section13Edges A h := fun i ↦
      ⟨(R.x i, R.y i), Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (hRin.2 i).1, by simpa only [hheight] using (hRin.2 i).2⟩⟩
    have hxR : section13EdgeArrangement x = R := by
      exact Prod.ext rfl (Prod.ext rfl hheight.symm)
    refine ⟨x, ?_, hxR⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hRin.1, hxR ▸ hRP⟩

/-- The Section 10 additive count is exactly the Section 13 height count. -/
theorem section13_domain_additive_count {N : Nat} [NeZero N]
    (A : Finset (Pair N)) (h : ZMod N) (k : Nat) :
    domainAdditiveTupleCount (section13VerticalDomain A h) k =
      arrangementCountAtHeight k A h := by
  have hcount := section13_edge_tuple_count A h (fun _ : DArrangement N k ↦ True)
  simpa only [and_true, domainAdditiveTupleCount, arrangementCountAtHeight] using hcount

/-- The respected tuple count is exactly the respected height-arrangement count. -/
theorem section13_domain_respected_count {N : Nat} [NeZero N]
    (A : Finset (Pair N)) (phi : Pair N → ZMod N) (h : ZMod N) (k : Nat) :
    domainPhiAdditiveTupleCount (section13VerticalDomain A h)
      (fun z ↦ verticalPhiDifference phi h z.val) k =
      respectedArrangementCountAtHeight k A phi h := by
  exact section13_edge_tuple_count A h (fun R : DArrangement N k ↦ R.IsRespected phi)

/-- A good height has exactly the approximate-homomorphism error required
by Theorem 10.13, after converting both counts without loss. -/
theorem section13_good_height_approx {N : Nat} [NeZero N]
    (S : Section13Context N) (h : ZMod N) (hh : IsGoodHeight S h) :
    DomainApproxHomOfOrder (section13VerticalDomain S.A h)
      (fun z ↦ verticalPhiDifference S.phi h z.val) ((2 : Real) ^ (-(43 : Real))) 8 := by
  unfold DomainApproxHomOfOrder
  rw [section13_domain_additive_count, section13_domain_respected_count]
  have herror : 2 * S.eta = (2 : Real) ^ (-(43 : Real)) := by
    rw [S.eta_value]
    norm_num [Real.rpow_neg, zpow_neg]
  change (1 - 2 * S.eta) * arrangementCountAtHeight 8 S.A h ≤
    respectedArrangementCountAtHeight 8 S.A S.phi h at hh
  rwa [herror] at hh

/-- Fibre cardinalities are preserved by the edge subtype representation. -/
theorem section13_vertical_fibre_card {N : Nat} [NeZero N]
    (A : Finset (Pair N)) (h x : ZMod N) :
    ((section13VerticalDomain A h).fibre x).card = verticalEdgeFiberCount A h x := by
  classical
  unfold verticalEdgeFiberCount
  apply Finset.card_bij (fun z _ ↦ z.val)
  · intro z hz
    exact Finset.mem_filter.mpr ⟨z.property, (Finset.mem_filter.mp hz).2⟩
  · intro z hz w hw hzw
    exact Subtype.ext hzw
  · intro z hz
    obtain ⟨hzA, hzx⟩ := Finset.mem_filter.mp hz
    exact ⟨⟨z, hzA⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzx⟩, rfl⟩

/-- The multifunction Fourier input is the original vertical-edge fibre function. -/
theorem section13_vertical_fibre_function {N : Nat} [NeZero N]
    (A : Finset (Pair N)) (h : ZMod N) :
    domainFibreCountFunction (section13VerticalDomain A h) = verticalEdgeFiberFunction A h := by
  funext x
  exact congrArg (fun n : Nat ↦ (n : Complex)) (section13_vertical_fibre_card A h x)

/-- Each vertical-edge fibre contains at most one edge per second coordinate. -/
theorem section13_vertical_fibre_cap {N : Nat} [NeZero N]
    (A : Finset (Pair N)) (h x : ZMod N) :
    ((section13VerticalDomain A h).fibre x).card ≤ N := by
  classical
  suffices hle : ((section13VerticalDomain A h).fibre x).card ≤
      (Finset.univ : Finset (ZMod N)).card by simpa using hle
  apply Finset.card_le_card_of_injOn (fun z : Section13Edges A h ↦ z.val.2)
  · intro z hz
    exact Finset.mem_univ _
  · intro z hz w hw hzw
    have hxz := (Finset.mem_filter.mp hz).2
    have hxw := (Finset.mem_filter.mp hw).2
    apply Subtype.ext
    exact Prod.ext (hxz.trans hxw.symm) hzw

/-- The edge-domain spectrum is exactly the spectrum of the original
vertical-edge counting function, with the same numerical threshold. -/
theorem section13_vertical_spectrum {N : Nat} [NeZero N]
    (A : Finset (Pair N)) (h : ZMod N) (t : Real) :
    domainLargeSpectrum (section13VerticalDomain A h) t =
      Finset.univ.filter (fun r ↦ t ≤ ‖fourier (verticalEdgeFiberFunction A h) r‖) := by
  classical
  unfold domainLargeSpectrum
  rw [section13_vertical_fibre_function]

/-- Apply Theorem 10.13 to a good height at its actual normalized edge
density. The selected set is transported back to lower-endpoint pairs without
losing cardinality or changing the Fourier spectrum and Bohr radius. -/
theorem section13_good_height_bohr_model {N : Nat} [NeZero N]
    (S : Section13Context N) (h : ZMod N) (hh : IsGoodHeight S h) (beta : Real)
    (hβ : 0 < beta) (hβsixth : beta ≤ 1 / 6)
    (hcard : ((verticalEdgeDomain S.A h).card : Real) = beta * (N : Real) ^ 2) :
    let K := domainLargeSpectrum (section13VerticalDomain S.A h)
      (section10Lambda beta * N * N)
    ∃ Y : Finset (Pair N), ∃ psi : ZMod N → ZMod N,
      Y ⊆ verticalEdgeDomain S.A h ∧
      beta ^ 6 * (verticalEdgeDomain S.A h).card / 20000 ≤ Y.card ∧
      HasBohrDifferenceModel (section13EdgeIndexDomain N) (verticalPhiDifference S.phi h)
        K (section10Zeta beta) Y psi := by
  classical
  have hcard' : (Fintype.card (Section13Edges S.A h) : Real) = beta * N * N := by
    rw [Fintype.card_coe, hcard]
    ring
  have hmain := theorem_10_13_holds N N (Section13Edges S.A h)
    (section13VerticalDomain S.A h) (fun z ↦ verticalPhiDifference S.phi h z.val) beta
    hβ hβsixth (NeZero.pos N) (section13_vertical_fibre_cap S.A h) hcard'
    (section13_good_height_approx S h hh)
  obtain ⟨Y, psi, hY, hmodel⟩ := hmain.2.2
  let e : Section13Edges S.A h ↪ Pair N := ⟨Subtype.val, Subtype.val_injective⟩
  refine ⟨Y.map e, psi, ?_, ?_, hmodel.1, ?_⟩
  · intro z hz
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hz
    exact v.property
  · simpa only [Finset.card_map, Fintype.card_coe] using hY
  · intro z hz w hw hzw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hz
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hw
    exact hmodel.2 v hv u hu hzw

end LeanProofs.GowersSzemeredi
