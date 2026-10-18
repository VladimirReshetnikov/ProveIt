import GowersSzemeredi.Proofs16SinglePieceSpectrum
import GowersSzemeredi.Proofs16SinglePieceSectionsSide

/-! Declarations of `Proofs16SinglePieceSpectrum` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

section
open Classical

/-- The dimension-`k` input in relation form: a local cover with few graphs. -/
def LocalRelationCoverAt (k : Nat) (delta : Real) (Qc : Real → Nat → Real) (c : Real → Real)
    (w : Real → Nat → Nat) : Prop :=
  ∀ (N : Nat) [NeZero N] [Fact N.Prime] (theta : Real), 0 < theta → theta ≤ 1 →
    ∀ (M : Nat) (P : Box N k) (H : Finset (Point N k)) (Gamma : Finset (Point N k × ZMod N)),
      P.IsProper → H ⊆ P.carrier → theta * P.carrier.card ≤ H.card →
      RelationProductProperty delta Gamma →
      (∀ h, (Gamma.filter fun z => z.1 = h).card ≤ M) →
      ∃ (R : Box N k) (G : Finset (Point N k)) (q : Nat) (mu : Fin q → Point N k → ZMod N),
        R.IsProper ∧ R.carrier ⊆ P.carrier ∧ w theta P.width ≤ R.width ∧
        G ⊆ H ∧ G ⊆ R.carrier ∧ c theta * R.carrier.card ≤ G.card ∧
        (q : Real) ≤ Qc theta M ∧ (∀ i, IsMultilinear (mu i)) ∧
        ∀ h ∈ G, ∀ y, (h, y) ∈ Gamma → ∃ i, y = mu i h

/-- **Relation covers give function pieces.** -/
theorem LocalRelationCoverAt.localMultilinearPieceAt {k : Nat} {delta : Real}
    {Qc : Real → Nat → Real} {c : Real → Real} {w : Real → Nat → Nat}
    (hcov : LocalRelationCoverAt k delta Qc c w) (hQ : ∀ t, 1 ≤ Qc t 1) :
    LocalMultilinearPieceAt k delta (fun t => c t / Qc t 1) w := by
  intro N _ _ theta hθ hθ1 P B phi hP hB hBc hprod
  have hfib : ∀ h, ((partialGraph B phi).filter fun z => z.1 = h).card ≤ 1 := by
    intro h
    refine Finset.card_le_one.mpr fun z hz z' hz' => ?_
    obtain ⟨hzG, rfl⟩ := Finset.mem_filter.mp hz
    obtain ⟨hzG', he⟩ := Finset.mem_filter.mp hz'
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hzG
    obtain ⟨x', -, rfl⟩ := Finset.mem_image.mp hzG'
    simp only at he
    rw [he]
  obtain ⟨R, G, q, mu, hR, hRP, hRw, hGB, hGR, hGc, hq, hmu, hcover⟩ :=
    hcov N theta hθ hθ1 1 P B (partialGraph B phi) hP hB hBc
      (partialGraph_relationProductProperty hprod) hfib
  have hQpos : 0 < Qc theta 1 := lt_of_lt_of_le one_pos (hQ theta)
  -- every point of `G` lies on one of the `q` graphs
  have hcov' : ∀ h ∈ G, ∃ i, phi h = mu i h := fun h hh =>
    hcover h hh (phi h) (Finset.mem_image.mpr ⟨h, hGB hh, rfl⟩)
  have hsum : (G.card : Real) ≤ ∑ i, ((G.filter fun h => phi h = mu i h).card : Real) := by
    have hsub : G ⊆ Finset.univ.biUnion fun i => G.filter fun h => phi h = mu i h := by
      intro h hh
      obtain ⟨i, hi⟩ := hcov' h hh
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hh, hi⟩⟩
    exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  rcases Nat.eq_zero_or_pos q with hq0 | hq0
  · subst hq0
    have hG0 : (G.card : Real) ≤ 0 := by simpa using hsum
    refine ⟨R, fun _ => 0, hR, hRP, hRw, ⟨fun _ => 0, fun x => by simp⟩, ?_⟩
    have : c theta * R.carrier.card ≤ 0 := hGc.trans hG0
    calc c theta / Qc theta 1 * R.carrier.card = (c theta * R.carrier.card) / Qc theta 1 := by
          ring
      _ ≤ 0 := div_nonpos_of_nonpos_of_nonneg this hQpos.le
      _ ≤ _ := Nat.cast_nonneg _
  · have hqR : (0 : Real) < q := by exact_mod_cast hq0
    have hne : (Finset.univ : Finset (Fin q)).Nonempty := Finset.univ_nonempty_iff.mpr ⟨⟨0, hq0⟩⟩
    have hle : ∑ _i : Fin q, (G.card : Real) / q ≤
        ∑ i, ((G.filter fun h => phi h = mu i h).card : Real) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [mul_div_cancel₀ _ hqR.ne']
      exact hsum
    obtain ⟨i, -, hi⟩ := Finset.exists_le_of_sum_le hne hle
    refine ⟨R, mu i, hR, hRP, hRw, hmu i, ?_⟩
    have hsub : (G.filter fun h => phi h = mu i h) ⊆
        B.filter fun x => x ∈ R.carrier ∧ phi x = mu i x := fun h hh => by
      obtain ⟨hhG, he⟩ := Finset.mem_filter.mp hh
      exact Finset.mem_filter.mpr ⟨hGB hhG, hGR hhG, he⟩
    calc c theta / Qc theta 1 * R.carrier.card ≤ (G.card : Real) / Qc theta 1 := by
          rw [div_mul_eq_mul_div]; exact div_le_div_of_nonneg_right hGc hQpos.le
      _ ≤ (G.card : Real) / q := div_le_div_of_nonneg_left (Nat.cast_nonneg _) hqR hq
      _ ≤ _ := hi.trans (by exact_mod_cast Finset.card_le_card hsub)

/-- **One multilinear piece from a local spectrum cover provider.** The
spectrum relation `Γ` needs a local cover provider on a domain `DomG`
containing the base points of `E`; no product property or fibre bound
of `Γ` is used here. -/
theorem single_piece_of_spectrum_cover_for {k : Nat} (hk : 0 < k)
    {zeta : Real} {Qc : Real → Real} {cR : Real → Real}
    {wR : Real → Nat → Nat} {c : Real → Real} {w : Real → Nat → Nat}
    (hcR : ∀ t, 0 < t → t ≤ 1 → 0 < cR t ∧ cR t ≤ 1)
    (hc : ∀ t, 0 < t → t ≤ 1 → 0 < c t ∧ c t ≤ 1) (hw : ∀ t, Monotone (w t))
    (eps : Nat → Real) (thr : Nat → Nat)
    (hretile : ∀ q, Section16RetiledLinearityBound k q (eps q) (thr q))
    (hz : 0 < zeta) (hz2 : zeta ≤ 1 / 2)
    {N : Nat} [NeZero N] [Fact N.Prime]
    (T0 : Box N k) (J0 : ModAP N) (hT0 : T0.IsProper) (hJ0 : J0.IsProper)
    (hT0d : T0.commonDiff ≠ 0) (hJ0step : J0.step = T0.commonDiff)
    (hshort : 2 * (T0.axis ⟨0, hk⟩).length ≤ N) (hT0J0 : (T0.axis ⟨0, hk⟩).length ≤ J0.length)
    (hJ0pos : 0 < J0.length)
    (E : Finset (Point N k × ZMod N)) (hE : E ⊆ T0.carrier ×ˢ J0.carrier)
    {theta : Real} (hθ : 0 < theta) (hθ1 : theta ≤ 1)
    (hEc : theta * T0.carrier.card * J0.carrier.card ≤ E.card)
    (phi : Point N k × ZMod N → ZMod N) (f : Point N k → ZMod N → ZMod N) (s : ZMod N)
    (Mrem : Point N (k + 1) → ZMod N) (hMrem : IsMultilinear Mrem)
    (hident : ∀ p ∈ E, phi p = s * f p.1 p.2 + Mrem (appendCoordinate p.1 p.2))
    (Gamma : Finset (Point N k × ZMod N)) (DomG : Finset (Point N k))
    (hcover : LocalRelationCoverFor cR Qc wR DomG Gamma) (hEG : ∀ p ∈ E, p.1 ∈ DomG)
    (K : Point N k → Finset (ZMod N))
    (hK : ∀ h x, (h, x) ∈ E → ∀ r ∈ K h, (h, r) ∈ Gamma)
    (A : Point N k → Finset (ZMod N)) (hA : ∀ p ∈ E, p.2 ∈ A p.1)
    (hlinear : ∀ h x, (h, x) ∈ E → ∀ v : Nat, 0 < v → ∀ J : ModAP N, J.length ≤ v →
      J.step ∈ bohr (K h) (zeta / v) → LinearOn (J.carrier ∩ A h) (f h))
    (Dom : ZMod N → Finset (Point N k))
    (hsl : ∀ x ∈ J0.carrier, LocalPieceFor c w (Dom x) (fun h => phi (h, x)))
    (hDom : ∀ p ∈ E, p.1 ∈ Dom p.2)
    (m : Nat) (hm1 : 1 ≤ m) (hm : m ≤ wR (theta / 2) T0.width)
    (hpar : ∀ q : Nat, (q : Real) ≤ Qc (theta / 2) →
      thr q ≤ m ∧ 4 ≤ spectrumCellWidth zeta m (eps q) ∧
      2 ≤ spectrumPieceRho cR theta ^ 3 * spectrumCellWidth zeta m (eps q) ∧
      2 ≤ w (c (singlePieceTheta (spectrumPieceRho cR theta) 1))
        (w (singlePieceTheta (spectrumPieceRho cR theta) 1)
          ⌈spectrumCellWidth zeta m (eps q) / 8⌉₊)) :
    ∃ q : Nat, (q : Real) ≤ Qc (theta / 2) ∧
      ∃ (S : Box N (k + 1)) (mu : Point N (k + 1) → ZMod N),
        S.IsProper ∧ S.carrier ⊆ lastProductSet T0.carrier J0.carrier ∧
        Nat.sqrt (w (c (singlePieceTheta (spectrumPieceRho cR theta) 1))
          (w (singlePieceTheta (spectrumPieceRho cR theta) 1)
            ⌈spectrumCellWidth zeta m (eps q) / 8⌉₊) - 1) - 1 ≤ S.width ∧
        IsMultilinear mu ∧
        singlePieceDensity c (spectrumPieceRho cR theta) 1 * S.carrier.card ≤
          (E.filter fun p => appendCoordinate p.1 p.2 ∈ S.carrier ∧
            phi p = mu (appendCoordinate p.1 p.2)).card :=
  single_piece_of_spectrum_cover_for_scheme hk hcR eps thr hretile hz hz2 (localPieceScheme c w hc hw)
    T0 J0 hT0 hJ0 hT0d hJ0step hshort hT0J0 hJ0pos E hE hθ hθ1 hEc phi f s Mrem hMrem hident Gamma
    DomG hcover hEG K hK A hA hlinear Dom hsl hDom m hm1 hm hpar

/-- **One multilinear piece from a local spectrum cover.** Its input
`LocalRelationCoverAt` is false for growing widths (Notes L.2), so this
form is vacuous; use `single_piece_of_spectrum_cover_for`. -/
theorem single_piece_of_spectrum_cover {k : Nat} (hk : 0 < k)
    {delta zeta : Real} {Qc : Real → Nat → Real} {cR : Real → Real}
    {wR : Real → Nat → Nat} {c : Real → Real} {w : Real → Nat → Nat}
    (hcover : LocalRelationCoverAt k delta Qc cR wR)
    (hcR : ∀ t, 0 < t → t ≤ 1 → 0 < cR t ∧ cR t ≤ 1)
    (hc : ∀ t, 0 < t → t ≤ 1 → 0 < c t ∧ c t ≤ 1) (hw : ∀ t, Monotone (w t))
    (eps : Nat → Real) (thr : Nat → Nat)
    (hretile : ∀ q, Section16RetiledLinearityBound k q (eps q) (thr q))
    (hz : 0 < zeta) (hz2 : zeta ≤ 1 / 2)
    {N : Nat} [NeZero N] [Fact N.Prime]
    (T0 : Box N k) (J0 : ModAP N) (hT0 : T0.IsProper) (hJ0 : J0.IsProper)
    (hT0d : T0.commonDiff ≠ 0) (hJ0step : J0.step = T0.commonDiff)
    (hshort : 2 * (T0.axis ⟨0, hk⟩).length ≤ N) (hT0J0 : (T0.axis ⟨0, hk⟩).length ≤ J0.length)
    (hJ0pos : 0 < J0.length)
    (E : Finset (Point N k × ZMod N)) (hE : E ⊆ T0.carrier ×ˢ J0.carrier)
    {theta : Real} (hθ : 0 < theta) (hθ1 : theta ≤ 1)
    (hEc : theta * T0.carrier.card * J0.carrier.card ≤ E.card)
    (phi : Point N k × ZMod N → ZMod N) (f : Point N k → ZMod N → ZMod N) (s : ZMod N)
    (Mrem : Point N (k + 1) → ZMod N) (hMrem : IsMultilinear Mrem)
    (hident : ∀ p ∈ E, phi p = s * f p.1 p.2 + Mrem (appendCoordinate p.1 p.2))
    (Gamma : Finset (Point N k × ZMod N)) (Msp : Nat) (hGamma : RelationProductProperty delta Gamma)
    (hfib : ∀ h, (Gamma.filter fun z => z.1 = h).card ≤ Msp)
    (K : Point N k → Finset (ZMod N))
    (hK : ∀ h x, (h, x) ∈ E → ∀ r ∈ K h, (h, r) ∈ Gamma)
    (A : Point N k → Finset (ZMod N)) (hA : ∀ p ∈ E, p.2 ∈ A p.1)
    (hlinear : ∀ h x, (h, x) ∈ E → ∀ v : Nat, 0 < v → ∀ J : ModAP N, J.length ≤ v →
      J.step ∈ bohr (K h) (zeta / v) → LinearOn (J.carrier ∩ A h) (f h))
    (Dom : ZMod N → Finset (Point N k))
    (hsl : ∀ x ∈ J0.carrier, LocalPieceFor c w (Dom x) (fun h => phi (h, x)))
    (hDom : ∀ p ∈ E, p.1 ∈ Dom p.2)
    (m : Nat) (hm1 : 1 ≤ m) (hm : m ≤ wR (theta / 2) T0.width)
    (hpar : ∀ q : Nat, (q : Real) ≤ Qc (theta / 2) Msp →
      thr q ≤ m ∧ 4 ≤ spectrumCellWidth zeta m (eps q) ∧
      2 ≤ spectrumPieceRho cR theta ^ 3 * spectrumCellWidth zeta m (eps q) ∧
      2 ≤ w (c (singlePieceTheta (spectrumPieceRho cR theta) 1))
        (w (singlePieceTheta (spectrumPieceRho cR theta) 1)
          ⌈spectrumCellWidth zeta m (eps q) / 8⌉₊)) :
    ∃ q : Nat, (q : Real) ≤ Qc (theta / 2) Msp ∧
      ∃ (S : Box N (k + 1)) (mu : Point N (k + 1) → ZMod N),
        S.IsProper ∧ S.carrier ⊆ lastProductSet T0.carrier J0.carrier ∧
        Nat.sqrt (w (c (singlePieceTheta (spectrumPieceRho cR theta) 1))
          (w (singlePieceTheta (spectrumPieceRho cR theta) 1)
            ⌈spectrumCellWidth zeta m (eps q) / 8⌉₊) - 1) - 1 ≤ S.width ∧
        IsMultilinear mu ∧
        singlePieceDensity c (spectrumPieceRho cR theta) 1 * S.carrier.card ≤
          (E.filter fun p => appendCoordinate p.1 p.2 ∈ S.carrier ∧
            phi p = mu (appendCoordinate p.1 p.2)).card :=
  single_piece_of_spectrum_cover_for (Qc := fun t => Qc t Msp) hk hcR hc hw eps thr hretile
    hz hz2 T0 J0 hT0 hJ0 hT0d hJ0step hshort hT0J0 hJ0pos E hE hθ hθ1 hEc phi f s Mrem hMrem
    hident Gamma Finset.univ
    (fun t ht ht1 P H hP hHP _ hHc => hcover N t ht ht1 Msp P H Gamma hP hHP hHc hGamma hfib)
    (fun _ _ => Finset.mem_univ _) K hK A hA hlinear Dom hsl hDom m hm1 hm hpar

end

end LeanProofs.GowersSzemeredi
