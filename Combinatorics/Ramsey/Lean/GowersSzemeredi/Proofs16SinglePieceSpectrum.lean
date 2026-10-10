import GowersSzemeredi.Proofs16SinglePieceSections
import GowersSzemeredi.Proofs16RetiledLinearityBound
import GowersSzemeredi.Proofs16ShortParents
import GowersSzemeredi.Proofs16CoordinateFaces

/-! The single-piece lift, step 3 (Notes L.1): the spectrum half of a
single-piece Lemma 16.9, and its assembly with step 2.

Gowers writes `φ₁ = (−1)^k φ′ + φ″` (Lemma 16.9).
- `φ′(h, ·)` is linear on short progressions whose step lies in the Bohr set
  of the whole large spectrum `K_h`. This is a **cover** requirement: every
  frequency in `K_h` must lie on one of few multilinear graphs.
- `φ″` is a sum of cross-section terms.

So the dimension-`k` input is a relation statement, not a function
statement:
* `LocalRelationCoverAt k δ Qc c w`, a named hypothesis, not asserted. Take
  a relation `Γ` with the product property and fibres of size `≤ M`, and a
  set `H` of density `θ` in a proper box `P`. Then on one proper sub-box `R`,
  of width `≥ w θ (width P)`, a set `G ⊆ H ∩ R` with `|G| ≥ c θ·|R|` has
  every value of `Γ` on `q ≤ Qc θ M` multilinear graphs. It holds trivially
  with `w θ L = min 1 L` and `Qc θ M ≥ M` (single points). **With any
  growing width it is false** (Notes L.2). Use the per-relation provider
  `LocalRelationCoverFor` and `single_piece_of_spectrum_cover_for`.
* `LocalRelationCoverAt.localMultilinearPieceAt`: for graphs of functions
  (`M = 1`), it gives the function form `LocalMultilinearPieceAt` of
  step 2 at density `c/Qc`, by pigeonhole.

The assembly, `single_piece_of_spectrum_cover`. Take a dense set `E` in a
cell `T₀ × J₀` on which `φ = s·f + M″`, with `M″` multilinear and `f(h, ·)`
Bohr-linear for the spectrum `K_h`. Then one proper `(k+1)`-box and one
multilinear map agree with `φ` on a `singlePieceDensity c ρ 1` fraction,
`ρ = (θ/2)·c_R(θ/2)`. The proof:
1. Popular fibres; the cover hypothesis on them gives `R`, `G` and `q`
   graphs.
2. The polynomial retiled linearity bound (`Section16RetiledLinearityBound`,
   supplied by `exists_polynomial_retiled_linearity_profile` at width
   exponent `1/(2p(q+1)^(2^(k+2)))`) cuts `R × J₀` into cells on which
   `f(h, ·)` is linear for `h ∈ G`.
3. A dense cell (`exists_dense_cell`), then a short-parent sub-cell
   (`Box.short_parent_partition`).
4. There `φ(h, ·)` is affine on each fibre, so `q = 1` in step 2
   (`single_piece_on_affine_cell`).

The remainder `φ″` enters as one multilinear map `M″` on `E`. Its own
single piece is a nested product of lower-dimensional pieces of the
cross-section terms, which is the remaining part of a single-piece
Lemma 16.9. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
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

/-- A local cover provider for one relation on one domain. -/
def LocalRelationCoverFor {N k : Nat} [NeZero N] (c : Real → Real) (Qc : Real → Real)
    (w : Real → Nat → Nat) (Dom : Finset (Point N k)) (Gamma : Finset (Point N k × ZMod N)) :
    Prop :=
  ∀ theta : Real, 0 < theta → theta ≤ 1 →
    ∀ (P : Box N k) (H : Finset (Point N k)), P.IsProper → H ⊆ P.carrier → H ⊆ Dom →
      theta * P.carrier.card ≤ H.card →
      ∃ (R : Box N k) (G : Finset (Point N k)) (q : Nat) (mu : Fin q → Point N k → ZMod N),
        R.IsProper ∧ R.carrier ⊆ P.carrier ∧ w theta P.width ≤ R.width ∧
        G ⊆ H ∧ G ⊆ R.carrier ∧ c theta * R.carrier.card ≤ G.card ∧
        (q : Real) ≤ Qc theta ∧ (∀ i, IsMultilinear (mu i)) ∧
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

/-- **A dense cell.** Some cell of a partition carries at least the
average proportion of a set mapped into it. -/
theorem exists_dense_cell {X Y : Type*} [DecidableEq X] {M : Nat}
    (C : Fin M → Finset X) (S : Finset X) (hC : IsPartition C S)
    (E : Finset Y) (g : Y → X) (hg : ∀ p ∈ E, g p ∈ S) (hE : E.Nonempty)
    {ρ : Real} (hρ : ρ * S.card ≤ E.card) :
    ∃ j, ρ * (C j).card ≤ (E.filter fun p => g p ∈ C j).card := by
  have hpart : IsPartition (fun j => E.filter fun p => g p ∈ C j) E := by
    refine ⟨fun p => ⟨fun hp => ?_, fun ⟨j, hj⟩ => (Finset.mem_filter.mp hj).1⟩, ?_⟩
    · obtain ⟨j, hj⟩ := (hC.1 _).mp (hg p hp)
      exact ⟨j, Finset.mem_filter.mpr ⟨hp, hj⟩⟩
    · intro j j' hjj'
      refine Finset.disjoint_left.mpr fun p hp hp' => ?_
      exact Finset.disjoint_left.mp (hC.2 j j' hjj') (Finset.mem_filter.mp hp).2
        (Finset.mem_filter.mp hp').2
  have hEsum : ∑ j, ((E.filter fun p => g p ∈ C j).card : Real) = E.card := by
    exact_mod_cast hpart.sum_card
  have hSsum : ∑ j, ((C j).card : Real) = S.card := by exact_mod_cast hC.sum_card
  obtain ⟨p, hp⟩ := hE
  obtain ⟨j0, -⟩ := (hC.1 _).mp (hg p hp)
  have hne : (Finset.univ : Finset (Fin M)).Nonempty := ⟨j0, Finset.mem_univ _⟩
  have hle : ∑ j, ρ * ((C j).card : Real) ≤ ∑ j, ((E.filter fun p => g p ∈ C j).card : Real) := by
    rw [← Finset.mul_sum, hSsum, hEsum]; exact hρ
  obtain ⟨j, -, hj⟩ := Finset.exists_le_of_sum_le hne hle
  exact ⟨j, hj⟩

/-- **Step 2 with affine fibres** (one class, `q = 1`). -/
theorem single_piece_on_affine_cell {k : Nat} (hk : 0 < k)
    {c : Real → Real} {w : Real → Nat → Nat}
    (hc : ∀ t, 0 < t → t ≤ 1 → 0 < c t ∧ c t ≤ 1) (hw : ∀ t, Monotone (w t))
    {N : Nat} [NeZero N] [Fact N.Prime]
    (T : Box N k) (J : ModAP N) (hT : T.IsProper) (hJ : J.IsProper) (hTne : T.carrier.Nonempty)
    (hTd : T.commonDiff ≠ 0) (hJstep : J.step = T.commonDiff)
    (hshort : 2 * (T.axis ⟨0, hk⟩).length ≤ N) (hTJ : (T.axis ⟨0, hk⟩).length ≤ J.length)
    (D : Finset (Point N k × ZMod N)) (hD : D ⊆ T.carrier ×ˢ J.carrier)
    {theta : Real} (hθ : 0 < theta) (hθ1 : theta ≤ 1)
    (hDc : theta * T.carrier.card * J.carrier.card ≤ D.card)
    (hJq : 2 ≤ theta ^ 3 * J.length)
    (phi : Point N k × ZMod N → ZMod N)
    (haff : ∀ h, ∃ a b : ZMod N, ∀ x, (h, x) ∈ D → phi (h, x) = a * x + b)
    (Dom : ZMod N → Finset (Point N k))
    (hsl : ∀ x ∈ J.carrier, LocalPieceFor c w (Dom x) (fun h => phi (h, x)))
    (hDom : ∀ p ∈ D, p.1 ∈ Dom p.2)
    (hwidth : 2 ≤ w (c (singlePieceTheta theta 1)) (w (singlePieceTheta theta 1) T.width)) :
    ∃ (S : Box N (k + 1)) (R : Box N k) (I : ModAP N) (mu : Point N (k + 1) → ZMod N),
      S.IsProper ∧ IsLastCoordinateBoxProduct S R I ∧ R.carrier ⊆ T.carrier ∧
      S.carrier ⊆ lastProductSet T.carrier J.carrier ∧
      Nat.sqrt (w (c (singlePieceTheta theta 1)) (w (singlePieceTheta theta 1) T.width) - 1) - 1
        ≤ S.width ∧
      IsMultilinear mu ∧
      singlePieceDensity c theta 1 * S.carrier.card ≤
        (D.filter fun p => appendCoordinate p.1 p.2 ∈ S.carrier ∧
          phi p = mu (appendCoordinate p.1 p.2)).card := by
  choose a b hab using haff
  refine single_piece_on_line_cell_of_slices hk hc hw T J hT hJ hTne hTd hJstep hshort hTJ D hD
    hθ hθ1 one_pos hDc (by simpa using hJq) (fun _ => (0 : Fin 1)) phi
    (fun h _ x => a h * x + b h) (fun h _ => ⟨a h, b h, fun _ _ => rfl⟩) ?_ Dom hsl hDom hwidth
  rintro ⟨h, x⟩ hp
  exact hab h x hp

/-- The density after the spectrum cover: `ρ = (θ/2)·c_R(θ/2)`. -/
def spectrumPieceRho (cR : Real → Real) (theta : Real) : Real :=
  theta / 2 * cR (theta / 2)

/-- The cell width after the retiled linearity bound. -/
def spectrumCellWidth (zeta : Real) (m : Nat) (e : Real) : Real :=
  zeta / 2 * Real.sqrt ((m : Real) ^ e)

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
            phi p = mu (appendCoordinate p.1 p.2)).card := by
  set ρ := spectrumPieceRho cR theta with hρdef
  have hθ2 : 0 < theta / 2 := by positivity
  have hθ21 : theta / 2 ≤ 1 := by linarith
  obtain ⟨hcRpos, hcRle⟩ := hcR (theta / 2) hθ2 hθ21
  have hρpos : 0 < ρ := by rw [hρdef, spectrumPieceRho]; positivity
  have hρle : ρ ≤ 1 := by
    rw [hρdef, spectrumPieceRho]
    calc theta / 2 * cR (theta / 2) ≤ 1 * 1 :=
          mul_le_mul hθ21 hcRle hcRpos.le zero_le_one
      _ = 1 := one_mul 1
  have hJ0card : J0.carrier.card = J0.length := hJ0
  have hJ0posR : (0 : Real) < J0.carrier.card := by rw [hJ0card]; exact_mod_cast hJ0pos
  -- 1. popular fibres and the local spectrum cover
  set H1 := T0.carrier.filter fun h =>
    theta / 2 * J0.carrier.card ≤ ((E.filter fun p => p.1 = h).card : Real) with hH1def
  have hH1 : theta / 2 * T0.carrier.card ≤ H1.card :=
    popular_fibres T0.carrier J0.carrier E hE (by exact_mod_cast hJ0posR) hθ2.le
      (by linarith)
  obtain ⟨R, G, q, mu, hR, hRT, hRw, hGH, hGR, hGc, hq, hmu, hGcov⟩ :=
    hcover (theta / 2) hθ2 hθ21 T0 H1 hT0 (Finset.filter_subset _ _) (fun h hh => by
      have h1 := (Finset.mem_filter.mp hh).2
      have hpos : 0 < (E.filter fun p => p.1 = h).card :=
        Nat.cast_pos.mp (lt_of_lt_of_le (mul_pos hθ2 hJ0posR) h1)
      obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
      obtain ⟨hpE, rfl⟩ := Finset.mem_filter.mp hp
      exact hEG p hpE) hH1
  obtain ⟨hthr, hcell4, hcellJ, hcellw⟩ := hpar q hq
  have hGE : ∀ h ∈ G, ∃ x, (h, x) ∈ E := by
    intro h hh
    have h1 := (Finset.mem_filter.mp (hGH hh)).2
    have hpos : 0 < (E.filter fun p => p.1 = h).card := by
      have : (0 : Real) < (E.filter fun p => p.1 = h).card :=
        lt_of_lt_of_le (mul_pos hθ2 hJ0posR) h1
      exact Nat.cast_pos.mp this
    obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
    obtain ⟨hpE, rfl⟩ := Finset.mem_filter.mp hp
    exact ⟨p.2, hpE⟩
  -- 2. retiled linearity on `R × J₀`
  set i : Fin k := ⟨0, hk⟩
  have hRwidth : m ≤ R.width := hm.trans hRw
  have hRne : R.carrier.Nonempty :=
    R.carrier_nonempty_of_axis_pos fun j => lt_of_lt_of_le (by omega) (hRwidth.trans
      (R.width_le_axis_length j))
  have hsub : (R.axis i).carrier ⊆ (T0.axis i).carrier :=
    R.axis_carrier_subset_of_carrier_subset T0 hRne hRT i
  have hlarge : 1 < spectrumCellWidth zeta m (eps q) := by linarith
  obtain ⟨M, S, T, J, hSpart, hSprop, hSprod, hSlin⟩ :=
    hretile q N m R (T0.axis i) J0 i (Units.mk0 T0.commonDiff hT0d) hR hJ0
      (by rw [Units.val_mk0, T0.axis_step i]) (hJ0step.trans (T0.axis_step i).symm) hsub hshort
      hT0J0 mu hmu hthr hRwidth K G A f zeta hz hz2
      (fun x _ hxG r hr => hGcov x hxG r (hK x _ (hGE x hxG).choose_spec r hr))
      (fun x hxG v hv J hJ hd => hlinear x _ (hGE x hxG).choose_spec v hv J hJ hd) hlarge
  -- 3. a dense cell
  set EG := E.filter fun p => p.1 ∈ G with hEGdef
  have hEGcard : ρ * (lastProductSet R.carrier J0.carrier).card ≤ EG.card := by
    have h := fibre_sum_ge E G (s := theta / 2 * J0.carrier.card) fun h hh =>
      (Finset.mem_filter.mp (hGH hh)).2
    rw [lastProductSet_card]
    push_cast
    calc ρ * ((R.carrier.card : Real) * J0.carrier.card) =
        cR (theta / 2) * R.carrier.card * (theta / 2 * J0.carrier.card) := by
          rw [hρdef, spectrumPieceRho]; ring
      _ ≤ G.card * (theta / 2 * J0.carrier.card) :=
          mul_le_mul_of_nonneg_right hGc (by positivity)
      _ ≤ _ := h
  have hEGin : ∀ p ∈ EG, appendCoordinate p.1 p.2 ∈ lastProductSet R.carrier J0.carrier := by
    intro p hp
    obtain ⟨hpE, hpG⟩ := Finset.mem_filter.mp hp
    simp only [lastProductSet, Finset.mem_filter, Finset.mem_univ, true_and,
      section16Init_appendCoordinate, section16Last_appendCoordinate]
    exact ⟨hGR hpG, (Finset.mem_product.mp (hE hpE)).2⟩
  have hRcard : (0 : Real) < R.carrier.card := by exact_mod_cast hRne.card_pos
  have hEGne : EG.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : Real) < EG.card := lt_of_lt_of_le (by
      rw [lastProductSet_card]; push_cast; positivity) hEGcard
    exact_mod_cast this
  obtain ⟨j, hj⟩ := exists_dense_cell (fun j => (S j).carrier) _ hSpart EG
    (fun p => appendCoordinate p.1 p.2) hEGin hEGne hEGcard
  set Dj := EG.filter fun p => appendCoordinate p.1 p.2 ∈ (S j).carrier with hDjdef
  have hSw : spectrumCellWidth zeta m (eps q) ≤ (S j).width := (hSprop j).2
  have hSw4 : 4 ≤ (S j).width := by
    have : (4 : Real) ≤ (S j).width := hcell4.trans hSw
    exact_mod_cast this
  -- 4. a short-parent sub-cell
  set I := (S j).axis (Fin.last k) with hIdef
  have hSjprop := (hSprop j).1
  have hI : I.IsProper := hSjprop (Fin.last k)
  have hIlen : (S j).width ≤ I.length := (S j).width_le_axis_length (Fin.last k)
  obtain ⟨L, Q, hQpart, hQprop, hQaxes, hQstep⟩ :=
    (boxInit (S j)).short_parent_partition I (boxInit_isProper _ hSjprop) hI hk hSw4
      (boxInit_width _ hk) hIlen
  have hSjcarrier : (S j).carrier = lastProductSet (boxInit (S j)).carrier I.carrier :=
    (boxInit_last_product (S j)).1
  have hDjin : ∀ p ∈ Dj, appendCoordinate p.1 p.2 ∈
      lastProductSet (boxInit (S j)).carrier I.carrier := by
    intro p hp
    rw [← hSjcarrier]
    exact (Finset.mem_filter.mp hp).2
  have hSjcard : (0 : Real) < (S j).carrier.card := by
    have hne : (S j).carrier.Nonempty :=
      (S j).carrier_nonempty_of_axis_pos fun z =>
        lt_of_lt_of_le (by omega) ((S j).width_le_axis_length z)
    exact_mod_cast hne.card_pos
  have hDjne : Dj.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : Real) < Dj.card := lt_of_lt_of_le (by positivity) hj
    exact_mod_cast this
  obtain ⟨l, hl⟩ := exists_dense_cell (fun l => lastProductSet (Q l).carrier I.carrier) _
    (lastProductSet_partition _ _ _ hQpart) Dj (fun p => appendCoordinate p.1 p.2) hDjin hDjne
    (by rw [← hSjcarrier]; exact hj)
  set D := Dj.filter fun p => appendCoordinate p.1 p.2 ∈ lastProductSet (Q l).carrier I.carrier
    with hDdef
  -- membership facts for `D`
  have hDmem : ∀ p ∈ D, p ∈ E ∧ p.1 ∈ G ∧ appendCoordinate p.1 p.2 ∈ (S j).carrier ∧
      p.1 ∈ (Q l).carrier ∧ p.2 ∈ I.carrier := by
    intro p hp
    obtain ⟨hpDj, hpQ⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpEG, hpS⟩ := Finset.mem_filter.mp hpDj
    obtain ⟨hpE, hpG⟩ := Finset.mem_filter.mp hpEG
    simp only [lastProductSet, Finset.mem_filter, Finset.mem_univ, true_and,
      section16Init_appendCoordinate, section16Last_appendCoordinate] at hpQ
    exact ⟨hpE, hpG, hpS, hpQ.1, hpQ.2⟩
  have hDsub : D ⊆ (Q l).carrier ×ˢ I.carrier := fun p hp =>
    Finset.mem_product.mpr ⟨(hDmem p hp).2.2.2.1, (hDmem p hp).2.2.2.2⟩
  have hQcard : ((lastProductSet (Q l).carrier I.carrier).card : Real) =
      (Q l).carrier.card * I.carrier.card := by
    rw [lastProductSet_card]; push_cast; ring
  have hDc : ρ * (Q l).carrier.card * I.carrier.card ≤ D.card := by
    rw [mul_assoc, ← hQcard]; exact hl
  have hDne : D.Nonempty := by
    rw [← Finset.card_pos]
    have hQne : (Q l).carrier.Nonempty := by
      have h8 : ((S j).width : Real) / 8 ≤ (Q l).width := (hQprop l).2
      have h1 : 1 ≤ (Q l).width := by
        have : (4 : Real) / 8 ≤ (Q l).width :=
          le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hSw4) (by norm_num)) h8
        have : (0 : Real) < (Q l).width := lt_of_lt_of_le (by norm_num) this
        exact_mod_cast this
      exact (Q l).carrier_nonempty_of_axis_pos fun z =>
        lt_of_lt_of_le one_pos (h1.trans ((Q l).width_le_axis_length z))
    have hIne : (0 : Real) < I.carrier.card := by
      rw [show I.carrier.card = I.length from hI]
      exact_mod_cast (show 0 < I.length by omega)
    have hQc : (0 : Real) < (Q l).carrier.card := by exact_mod_cast hQne.card_pos
    have : (0 : Real) < D.card := lt_of_lt_of_le (mul_pos (mul_pos hρpos hQc) hIne) hDc
    exact Nat.cast_pos.mp this
  -- the fibres of `φ` on `D` are affine
  have haff : ∀ h, ∃ a b : ZMod N, ∀ x, (h, x) ∈ D → phi (h, x) = a * x + b := by
    intro h
    by_cases hh : ∃ x, (h, x) ∈ D
    · obtain ⟨x0, hx0⟩ := hh
      obtain ⟨-, hG0, hS0, -, -⟩ := hDmem _ hx0
      have hT0' : h ∈ (T j).carrier := by
        have := hS0
        rw [(hSprod j).1] at this
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          section16Init_appendCoordinate] at this
        exact this.1
      obtain ⟨a, b, hab⟩ := hSlin j h hT0' hG0
      obtain ⟨α, β, hαβ⟩ := hMrem.linearOn_last_fibre h
      refine ⟨s * a + α, s * b + β, fun x hx => ?_⟩
      obtain ⟨hxE, -, hxS, -, -⟩ := hDmem _ hx
      have hxJ : x ∈ (J j).carrier := by
        have := hxS
        rw [(hSprod j).1] at this
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          section16Last_appendCoordinate] at this
        exact this.2
      have e1 : phi (h, x) = s * f h x + Mrem (appendCoordinate h x) := hident _ hxE
      have e2 : f h x = a * x + b := hab x (Finset.mem_inter.mpr ⟨hxJ, hA _ hxE⟩)
      have e3 : Mrem (appendCoordinate h x) = α * x + β := hαβ x (Finset.mem_univ _)
      rw [e1, e2, e3]
      ring
    · simp only [not_exists] at hh
      exact ⟨0, 0, fun x hx => absurd hx (hh x)⟩
  -- the final axis lies in `J₀`
  have hIJ0 : ∀ x ∈ I.carrier, x ∈ J0.carrier := by
    intro x hx
    obtain ⟨p, hp⟩ := hDne
    have ht := (hDmem p hp).2.2.2.1
    have htS : (Fin.snoc p.1 x : Point N (k + 1)) ∈ (S j).carrier :=
      (mem_boxInit_snoc (S j) p.1 x).mpr
        ⟨IsPartition.cell_subset hQpart l ht, hx⟩
    have := IsPartition.cell_subset hSpart j htS
    simp only [lastProductSet, Finset.mem_filter, Finset.mem_univ, true_and] at this
    simpa [section16Last] using this.2
  -- 5. step 2 on the cell `Q l × I`
  have hQd : (Q l).commonDiff ≠ 0 := by
    rw [hQstep l]
    have hu := I.step_isUnit_of_prime hI (by omega)
    rw [show I.step = (S j).commonDiff from (S j).axis_step _] at hu
    exact hu.ne_zero
  have hQw : ⌈spectrumCellWidth zeta m (eps q) / 8⌉₊ ≤ (Q l).width := by
    apply Nat.ceil_le.mpr
    have h8 : ((S j).width : Real) / 8 ≤ (Q l).width := (hQprop l).2
    exact le_trans (div_le_div_of_nonneg_right hSw (by norm_num)) h8
  have hwidth : 2 ≤ w (c (singlePieceTheta ρ 1)) (w (singlePieceTheta ρ 1) (Q l).width) :=
    hcellw.trans (hw _ (hw _ hQw))
  obtain ⟨S', R', I', mu', hS'prop, -, -, hS'sub, hS'w, hmu', hcount⟩ :=
    single_piece_on_affine_cell hk hc hw (Q l) I (hQprop l).1 hI ⟨_, (hDmem _
      hDne.choose_spec).2.2.2.1⟩ hQd (by rw [hQstep l]; exact (S j).axis_step _)
      ((hQaxes l i).2.1) ((hQaxes l i).2.2) D hDsub hρpos hρle hDc
      (by
        have : spectrumCellWidth zeta m (eps q) ≤ I.length := hSw.trans (by exact_mod_cast hIlen)
        calc (2 : Real) ≤ ρ ^ 3 * spectrumCellWidth zeta m (eps q) := hcellJ
          _ ≤ ρ ^ 3 * I.length := mul_le_mul_of_nonneg_left this (by positivity))
      phi haff
      Dom (fun x hx => hsl x (hIJ0 x hx)) (fun p hp => hDom p (hDmem p hp).1) hwidth
  refine ⟨q, hq, S', mu', hS'prop, ?_, ?_, hmu', ?_⟩
  · intro z hz
    have hz' := hS'sub hz
    simp only [lastProductSet, Finset.mem_filter, Finset.mem_univ, true_and] at hz' ⊢
    have hzS : (Fin.snoc (section16Init z) (section16Last z) : Point N (k + 1)) ∈
        (S j).carrier :=
      (mem_boxInit_snoc (S j) _ _).mpr ⟨IsPartition.cell_subset hQpart l hz'.1, hz'.2⟩
    have := IsPartition.cell_subset hSpart j hzS
    simp only [lastProductSet, Finset.mem_filter, Finset.mem_univ, true_and,
      section16Init_snoc] at this
    exact ⟨hRT this.1, by simpa [section16Last] using this.2⟩
  · have hsq := Nat.sqrt_le_sqrt (Nat.sub_le_sub_right
      (hw (c (singlePieceTheta ρ 1)) (hw (singlePieceTheta ρ 1) hQw)) 1)
    omega
  · refine hcount.trans ?_
    exact_mod_cast Finset.card_le_card fun p hp => by
      obtain ⟨hpD, hpS⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨(hDmem p hpD).1, hpS⟩

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

end LeanProofs.GowersSzemeredi
