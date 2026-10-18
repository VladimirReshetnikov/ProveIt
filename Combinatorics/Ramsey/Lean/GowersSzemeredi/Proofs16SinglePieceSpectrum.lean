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
   (`single_piece_on_affine_cell_of_scheme`).

The remainder `φ″` enters as one multilinear map `M″` on `E`. Its own
single piece is a nested product of lower-dimensional pieces of the
cross-section terms, which is the remaining part of a single-piece
Lemma 16.9.

`LocalRelationCoverAt`, `LocalRelationCoverAt.localMultilinearPieceAt`,
`single_piece_of_spectrum_cover` and `single_piece_of_spectrum_cover_for` are in
`Proofs16SinglePieceSpectrumSide`, outside the final route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

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

/-- **Step 2 with affine fibres** (one class, `q = 1`), for a slice scheme. -/
theorem single_piece_on_affine_cell_of_scheme {k : Nat} (hk : 0 < k)
    {N : Nat} [NeZero N] [Fact N.Prime] (Sc : SliceScheme N k)
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
    (hsl : ∀ x ∈ J.carrier, Sc.SL (Dom x) (fun h => phi (h, x)))
    (hDom : ∀ p ∈ D, p.1 ∈ Dom p.2)
    (hwidth : 2 ≤ Sc.wid (singlePieceTheta theta 1) T.width) :
    ∃ (S : Box N (k + 1)) (R : Box N k) (I : ModAP N) (mu : Point N (k + 1) → ZMod N),
      S.IsProper ∧ IsLastCoordinateBoxProduct S R I ∧ R.carrier ⊆ T.carrier ∧
      S.carrier ⊆ lastProductSet T.carrier J.carrier ∧
      Nat.sqrt (Sc.wid (singlePieceTheta theta 1) T.width - 1) - 1 ≤ S.width ∧
      IsMultilinear mu ∧
      singlePieceTheta theta 1 * Sc.dens (singlePieceTheta theta 1) * S.carrier.card ≤
        (D.filter fun p => appendCoordinate p.1 p.2 ∈ S.carrier ∧
          phi p = mu (appendCoordinate p.1 p.2)).card := by
  choose a b hab using haff
  refine single_piece_on_line_cell_of_scheme hk Sc T J hT hJ hTne hTd hJstep hshort hTJ D hD
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
theorem single_piece_of_spectrum_cover_for_scheme {k : Nat} (hk : 0 < k)
    {zeta : Real} {Qc : Real → Real} {cR : Real → Real}
    {wR : Real → Nat → Nat}
    (hcR : ∀ t, 0 < t → t ≤ 1 → 0 < cR t ∧ cR t ≤ 1)
    (eps : Nat → Real) (thr : Nat → Nat)
    (hretile : ∀ q, Section16RetiledLinearityBound k q (eps q) (thr q))
    (hz : 0 < zeta) (hz2 : zeta ≤ 1 / 2)
    {N : Nat} [NeZero N] [Fact N.Prime] (Sc : SliceScheme N k)
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
    (hsl : ∀ x ∈ J0.carrier, Sc.SL (Dom x) (fun h => phi (h, x)))
    (hDom : ∀ p ∈ E, p.1 ∈ Dom p.2)
    (m : Nat) (hm1 : 1 ≤ m) (hm : m ≤ wR (theta / 2) T0.width)
    (hpar : ∀ q : Nat, (q : Real) ≤ Qc (theta / 2) →
      thr q ≤ m ∧ 4 ≤ spectrumCellWidth zeta m (eps q) ∧
      2 ≤ spectrumPieceRho cR theta ^ 3 * spectrumCellWidth zeta m (eps q) ∧
      2 ≤ Sc.wid (singlePieceTheta (spectrumPieceRho cR theta) 1)
        ⌈spectrumCellWidth zeta m (eps q) / 8⌉₊) :
    ∃ q : Nat, (q : Real) ≤ Qc (theta / 2) ∧
      ∃ (S : Box N (k + 1)) (mu : Point N (k + 1) → ZMod N),
        S.IsProper ∧ S.carrier ⊆ lastProductSet T0.carrier J0.carrier ∧
        Nat.sqrt (Sc.wid (singlePieceTheta (spectrumPieceRho cR theta) 1)
          ⌈spectrumCellWidth zeta m (eps q) / 8⌉₊ - 1) - 1 ≤ S.width ∧
        IsMultilinear mu ∧
        singlePieceTheta (spectrumPieceRho cR theta) 1 *
            Sc.dens (singlePieceTheta (spectrumPieceRho cR theta) 1) * S.carrier.card ≤
          (E.filter fun p => appendCoordinate p.1 p.2 ∈ S.carrier ∧
            phi p = mu (appendCoordinate p.1 p.2)).card := by
  set ρ := spectrumPieceRho cR theta with hρdef
  have hθ2 : 0 < theta / 2 := by positivity
  have hθ21 : theta / 2 ≤ 1 := by linarith
  obtain ⟨hcRpos, hcRle⟩ := hcR (theta / 2) hθ2 hθ21
  have hρpos : 0 < ρ := mul_pos hθ2 hcRpos
  have hρle : ρ ≤ 1 := mul_le_one₀ hθ21 hcRpos.le hcRle
  have hJ0posR : (0 : Real) < J0.carrier.card := by
    rw [show J0.carrier.card = J0.length from hJ0]; exact_mod_cast hJ0pos
  -- 1. popular fibres and the local spectrum cover
  set H1 := T0.carrier.filter fun h =>
    theta / 2 * J0.carrier.card ≤ ((E.filter fun p => p.1 = h).card : Real)
  have hH1 : theta / 2 * T0.carrier.card ≤ H1.card :=
    popular_fibres T0.carrier J0.carrier E hE (by exact_mod_cast hJ0posR) hθ2.le
      (by linarith)
  -- a popular fibre is nonempty
  have hH1E : ∀ h ∈ H1, ∃ x, (h, x) ∈ E := fun h hh => by
    obtain ⟨p, hp⟩ := Finset.card_pos.mp (Nat.cast_pos.mp
      ((mul_pos hθ2 hJ0posR).trans_le (Finset.mem_filter.mp hh).2))
    obtain ⟨hpE, rfl⟩ := Finset.mem_filter.mp hp
    exact ⟨p.2, hpE⟩
  obtain ⟨R, G, q, mu, hR, hRT, hRw, hGH, hGR, hGc, hq, hmu, hGcov⟩ :=
    hcover (theta / 2) hθ2 hθ21 T0 H1 hT0 (Finset.filter_subset _ _)
      (fun h hh => hEG _ (hH1E h hh).choose_spec) hH1
  obtain ⟨hthr, hcell4, hcellJ, hcellw⟩ := hpar q hq
  -- 2. retiled linearity on `R × J₀`
  set i : Fin k := ⟨0, hk⟩
  have hRwidth : m ≤ R.width := hm.trans hRw
  have hRne : R.carrier.Nonempty := R.carrier_nonempty_of_axis_pos fun j =>
    lt_of_lt_of_le (by omega) (hRwidth.trans (R.width_le_axis_length j))
  obtain ⟨M, S, T, J, hSpart, hSprop, hSprod, hSlin⟩ :=
    hretile q N m R (T0.axis i) J0 i (Units.mk0 T0.commonDiff hT0d) hR hJ0 (T0.axis_step i)
      (hJ0step.trans (T0.axis_step i).symm)
      (R.axis_carrier_subset_of_carrier_subset T0 hRne hRT i) hshort hT0J0 mu hmu hthr hRwidth
      K G A f zeta hz hz2
      (fun x _ hxG r hr => hGcov x hxG r (hK x _ (hH1E x (hGH hxG)).choose_spec r hr))
      (fun x hxG v hv J hJ hd => hlinear x _ (hH1E x (hGH hxG)).choose_spec v hv J hJ hd)
      (lt_of_lt_of_le (by norm_num) hcell4)
  -- 3. a dense cell
  set EG := E.filter fun p => p.1 ∈ G
  have hEGcard : ρ * (lastProductSet R.carrier J0.carrier).card ≤ EG.card := by
    rw [lastProductSet_card, hρdef, spectrumPieceRho]; push_cast
    calc theta / 2 * cR (theta / 2) * ((R.carrier.card : Real) * J0.carrier.card) =
        cR (theta / 2) * R.carrier.card * (theta / 2 * J0.carrier.card) := by ring
      _ ≤ G.card * (theta / 2 * J0.carrier.card) := by gcongr
      _ ≤ EG.card := fibre_sum_ge E G fun h hh => (Finset.mem_filter.mp (hGH hh)).2
  have hEGin : ∀ p ∈ EG, appendCoordinate p.1 p.2 ∈ lastProductSet R.carrier J0.carrier :=
    fun p hp => by
      obtain ⟨hpE, hpG⟩ := Finset.mem_filter.mp hp
      simpa [lastProductSet] using And.intro (hGR hpG) (Finset.mem_product.mp (hE hpE)).2
  have hRcard : (0 : Real) < R.carrier.card := by exact_mod_cast hRne.card_pos
  have hEGne : EG.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp (lt_of_lt_of_le
    (by rw [lastProductSet_card]; push_cast; positivity) hEGcard))
  obtain ⟨j, hj⟩ := exists_dense_cell (fun j => (S j).carrier) _ hSpart EG
    (fun p => appendCoordinate p.1 p.2) hEGin hEGne hEGcard
  set Dj := EG.filter fun p => appendCoordinate p.1 p.2 ∈ (S j).carrier
  have hSw : spectrumCellWidth zeta m (eps q) ≤ (S j).width := (hSprop j).2
  have hSw4 : 4 ≤ (S j).width := by exact_mod_cast hcell4.trans hSw
  -- 4. a short-parent sub-cell
  set I := (S j).axis (Fin.last k)
  have hI : I.IsProper := (hSprop j).1 (Fin.last k)
  have hIlen : (S j).width ≤ I.length := (S j).width_le_axis_length (Fin.last k)
  obtain ⟨L, Q, hQpart, hQprop, hQaxes, hQstep⟩ :=
    (boxInit (S j)).short_parent_partition I (boxInit_isProper _ (hSprop j).1) hI hk hSw4
      (boxInit_width _ hk) hIlen
  have hSjcarrier : (S j).carrier = lastProductSet (boxInit (S j)).carrier I.carrier :=
    (boxInit_last_product (S j)).1
  have hSjne : (S j).carrier.Nonempty := (S j).carrier_nonempty_of_axis_pos fun z =>
    lt_of_lt_of_le (by omega) ((S j).width_le_axis_length z)
  have hDjne : Dj.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp (lt_of_lt_of_le
    (mul_pos hρpos (by exact_mod_cast hSjne.card_pos)) hj))
  obtain ⟨l, hl⟩ := exists_dense_cell (fun l => lastProductSet (Q l).carrier I.carrier) _
    (lastProductSet_partition _ _ _ hQpart) Dj (fun p => appendCoordinate p.1 p.2)
    (fun p hp => hSjcarrier ▸ (Finset.mem_filter.mp hp).2) hDjne (hSjcarrier ▸ hj)
  set D := Dj.filter fun p => appendCoordinate p.1 p.2 ∈ lastProductSet (Q l).carrier I.carrier
  have hDmem : ∀ p ∈ D, p ∈ E ∧ p.1 ∈ G ∧ appendCoordinate p.1 p.2 ∈ (S j).carrier ∧
      p.1 ∈ (Q l).carrier ∧ p.2 ∈ I.carrier := fun p hp => by
    simp only [D, Dj, EG, lastProductSet, Finset.mem_filter, Finset.mem_univ, true_and,
      section16Init_appendCoordinate, section16Last_appendCoordinate] at hp
    exact ⟨hp.1.1.1, hp.1.1.2, hp.1.2, hp.2⟩
  have hDc : ρ * (Q l).carrier.card * I.carrier.card ≤ D.card := by
    simpa only [lastProductSet_card, Nat.cast_mul, mul_assoc] using hl
  have hQne : (Q l).carrier.Nonempty :=
    (Q l).carrier_nonempty_of_axis_pos fun z => (hQaxes l z).1
  -- the fibres of `φ` on `D` are affine
  have hST : ∀ h x, appendCoordinate h x ∈ (S j).carrier →
      h ∈ (T j).carrier ∧ x ∈ (J j).carrier := fun h x hx => by
    simpa [(hSprod j).1] using hx
  have haff : ∀ h, ∃ a b : ZMod N, ∀ x, (h, x) ∈ D → phi (h, x) = a * x + b := by
    intro h
    by_cases hh : ∃ x, (h, x) ∈ D
    · obtain ⟨-, hG0, hS0, -, -⟩ := hDmem _ hh.choose_spec
      obtain ⟨a, b, hab⟩ := hSlin j h (hST _ _ hS0).1 hG0
      obtain ⟨α, β, hαβ⟩ := hMrem.linearOn_last_fibre h
      refine ⟨s * a + α, s * b + β, fun x hx => ?_⟩
      obtain ⟨hxE, -, hxS, -, -⟩ := hDmem _ hx
      have e1 : phi (h, x) = s * f h x + Mrem (appendCoordinate h x) := hident _ hxE
      have e3 : Mrem (appendCoordinate h x) = α * x + β := hαβ x (Finset.mem_univ _)
      rw [e1, e3, hab x (Finset.mem_inter.mpr ⟨(hST _ _ hxS).2, hA _ hxE⟩)]
      ring
    · exact ⟨0, 0, fun x hx => absurd ⟨x, hx⟩ hh⟩
  -- the cell `Q l × I` lies in `T₀ × J₀`
  have hQI : ∀ t ∈ (Q l).carrier, ∀ x ∈ I.carrier, t ∈ T0.carrier ∧ x ∈ J0.carrier := by
    intro t ht x hx
    have := IsPartition.cell_subset hSpart j
      ((mem_boxInit_snoc (S j) t x).mpr ⟨IsPartition.cell_subset hQpart l ht, hx⟩)
    simp only [lastProductSet, Finset.mem_filter, Finset.mem_univ, true_and,
      section16Init_snoc, section16Last, Fin.snoc_last] at this
    exact ⟨hRT this.1, this.2⟩
  -- 5. step 2 on the cell `Q l × I`
  have hIstep : I.step = (Q l).commonDiff := ((S j).axis_step _).trans (hQstep l).symm
  have hmono := Sc.wid_mono _ (singlePieceTheta_pos hρpos one_pos)
    (singlePieceTheta_le_one hρpos hρle one_pos)
    (Nat.ceil_le.mpr ((div_le_div_of_nonneg_right hSw (by norm_num)).trans (hQprop l).2))
  obtain ⟨S', R', I', mu', hS'prop, -, -, hS'sub, hS'w, hmu', hcount⟩ :=
    single_piece_on_affine_cell_of_scheme hk Sc (Q l) I (hQprop l).1 hI hQne
      (hIstep ▸ (I.step_isUnit_of_prime hI (by omega)).ne_zero) hIstep (hQaxes l i).2.1
      (hQaxes l i).2.2 D (fun p hp => Finset.mem_product.mpr (hDmem p hp).2.2.2) hρpos hρle hDc
      (hcellJ.trans (mul_le_mul_of_nonneg_left (hSw.trans (by exact_mod_cast hIlen))
        (by positivity)))
      phi haff Dom (fun x hx => hsl x (hQI _ hQne.choose_spec x hx).2)
      (fun p hp => hDom p (hDmem p hp).1) (hcellw.trans hmono)
  refine ⟨q, hq, S', mu', hS'prop, fun z hz => ?_,
    (Nat.sub_le_sub_right (Nat.sqrt_le_sqrt (Nat.sub_le_sub_right hmono 1)) 1).trans hS'w, hmu',
    hcount.trans ?_⟩
  · obtain ⟨-, hzQ, hzI⟩ := Finset.mem_filter.mp (hS'sub hz)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hQI _ hzQ _ hzI⟩
  · exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ fun p hp => (hDmem p hp).1)

end LeanProofs.GowersSzemeredi
