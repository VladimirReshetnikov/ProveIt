import GowersSzemeredi.Proofs16SinglePieceAnchor
import GowersSzemeredi.Proofs16RetiledRecurrence
import GowersSzemeredi.Proofs16Interpolation
import GowersSzemeredi.Proofs16FibreGeometry

/-! The single-piece lift, step 2 (Notes L.1): one `(k+1)`-multilinear
piece on a line-covered cell, from a dimension-`k` **local piece** input.

`LocalMultilinearPieceAt k γ c w` is the dimension-`k` input. Take a set `B`
of density `θ` in a proper box `P`, carrying a function with the product
property. The input asks for one proper sub-box `R`, of width
`≥ w θ (width P)`, and one multilinear map that agrees with the function
on `c θ·|R|` points of `B ∩ R`. It is a named hypothesis, not asserted. With
`w θ L = min 1 L` and `c ≤ 1` it holds trivially, through single-point boxes
(an empty box forces `w θ 0 = 0`). **With any growing width it is false**
(Notes L.2, `not_localMultilinearPieceAt_of_quadratic`): the product
property is normalized by the whole modulus, so it holds automatically on
short boxes. Theorems assuming it with growing widths are vacuous; use
the provider forms (`single_piece_on_line_cell_of_slices`, `LocalPieceFor`).

`single_piece_on_line_cell` takes a cell `T × J` and a set `D` of density `θ`
in it. Each fibre of `D` is split into at most `q` classes, and `φ(h, ·)` is
affine on each class: the form of Lemma 16.9's line cover. It returns one
proper `(k+1)`-box `S ⊆ T × J` and one multilinear `μ` that agrees with `φ`
on `θ₁·c(c(θ₁))·|S|` points of `D ∩ S`, where `θ₁ = θ³/(4q²)`. Width:
`width S ≥ ⌊√(w(c θ₁)(w θ₁ (width T)) − 1)⌋ − 1`. The proof:
1. `exists_anchor_pair_capture` picks one anchor pair `a ≠ b`, capturing a
   set `W` with `|W| ≥ 2θ₁|T||J|` (`capture_density`).
2. Popular fibres: `θ₁|T|` base points carry `≥ θ₁|J|` captured points each
   (`popular_fibres`).
3. The input, applied to the cross-section `φ(·, a)` on them, then again
   to `φ(·, b)` on the agreement set inside the first box.
4. `anchor_reconstruction`: on the doubly agreeing fibres,
   `φ = section16TwoAnchorLift a b μ_a μ_b`.
5. The corpus's synchronized retiling (`box_product_tiling_of_contained_axis`)
   cuts `R × J` into proper common-step boxes; one of them is dense.

With `c t = t^D` the density is `θ₁^(D²+1)`: polynomial in `θ` and `1/q`. Gowers's
lift unites `r²` anchor pairs and loses `p = 4r²γ⁻²s` in the exponent; that
union does not arise here.

`LocalMultilinearPieceAt`, `LocalMultilinearPieceAt.localPieceFor`,
`singlePieceDensity`, `single_piece_on_line_cell` and
`single_piece_on_line_cell_of_slices` are in `Proofs16SinglePieceSectionsSide`,
outside the final route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- A local piece provider for one function on a domain. -/
def LocalPieceFor {N d : Nat} [NeZero N] (c : Real → Real) (w : Real → Nat → Nat)
    (Dom : Finset (Point N d)) (g : Point N d → ZMod N) : Prop :=
  ∀ theta : Real, 0 < theta → theta ≤ 1 →
    ∀ (P : Box N d) (H : Finset (Point N d)), P.IsProper → H ⊆ P.carrier → H ⊆ Dom →
      theta * P.carrier.card ≤ H.card →
      ∃ (R : Box N d) (mu : Point N d → ZMod N),
        R.IsProper ∧ R.carrier ⊆ P.carrier ∧ w theta P.width ≤ R.width ∧ IsMultilinear mu ∧
        c theta * R.carrier.card ≤ (H.filter fun x => x ∈ R.carrier ∧ g x = mu x).card

/-- The density of the popular fibres: `θ³/(4q²)`. -/
def singlePieceTheta (theta : Real) (q : Nat) : Real :=
  theta ^ 3 / (4 * (q : Real) ^ 2)

theorem singlePieceTheta_pos {theta : Real} (hθ : 0 < theta) {q : Nat} (hq : 0 < q) :
    0 < singlePieceTheta theta q := by
  have : (0 : Real) < q := by exact_mod_cast hq
  unfold singlePieceTheta; positivity

theorem singlePieceTheta_le_one {theta : Real} (hθ : 0 < theta) (hθ1 : theta ≤ 1) {q : Nat}
    (hq : 0 < q) : singlePieceTheta theta q ≤ 1 := by
  have hqR : (1 : Real) ≤ q := by exact_mod_cast hq
  unfold singlePieceTheta
  rw [div_le_one (by positivity)]
  have h3 : theta ^ 3 ≤ 1 := pow_le_one₀ hθ.le hθ1
  nlinarith

/-- The anchor capture estimate, solved for the captured set. -/
theorem capture_density {θ q t j d w : Real} (hθ : 0 < θ) (hq : 1 ≤ q) (ht : 0 < t)
    (hj : 0 < j) (hd : θ * t * j ≤ d) (hdle : d ≤ t * j)
    (hcap : d ^ 3 ≤ (q * t) ^ 2 * (j ^ 2 * w + j * d)) (hjq : 2 * q ^ 2 ≤ θ ^ 3 * j) :
    θ ^ 3 / (2 * q ^ 2) * t * j ≤ w := by
  have key : θ ^ 3 * t * j ≤ q ^ 2 * (w + t) := by
    have h : (t ^ 2 * j ^ 2) * (θ ^ 3 * t * j) ≤ (t ^ 2 * j ^ 2) * (q ^ 2 * (w + t)) := by
      calc (t ^ 2 * j ^ 2) * (θ ^ 3 * t * j) = (θ * t * j) ^ 3 := by ring
        _ ≤ d ^ 3 := pow_le_pow_left₀ (by positivity) hd 3
        _ ≤ (q * t) ^ 2 * (j ^ 2 * w + j * d) := hcap
        _ ≤ (q * t) ^ 2 * (j ^ 2 * w + j * (t * j)) := by gcongr
        _ = (t ^ 2 * j ^ 2) * (q ^ 2 * (w + t)) := by ring
    exact le_of_mul_le_mul_left h (by positivity)
  have hjqt : 2 * q ^ 2 * t ≤ θ ^ 3 * j * t := mul_le_mul_of_nonneg_right hjq ht.le
  have hq2 : 0 < 2 * q ^ 2 := by positivity
  rw [show θ ^ 3 / (2 * q ^ 2) * t * j = (θ ^ 3 * t * j) / (2 * q ^ 2) by ring,
    div_le_iff₀ hq2]
  nlinarith

variable {A : Type*} [DecidableEq A] {N : Nat}

/-- **Popular fibres.** If `W ⊆ T × J` has `|W| ≥ 2t|T||J|`, then at least
`t|T|` base points carry `≥ t|J|` points of `W` each. -/
theorem popular_fibres (T : Finset A) (J : Finset (ZMod N)) (W : Finset (A × ZMod N))
    (hW : W ⊆ T ×ˢ J) (hJ : 0 < J.card) {t : Real} (ht : 0 ≤ t)
    (hWc : 2 * t * T.card * J.card ≤ W.card) :
    t * T.card ≤ (T.filter fun h => t * J.card ≤ (W.filter fun p => p.1 = h).card).card := by
  let f : A → Real := fun h => ((W.filter fun p => p.1 = h).card : Real)
  have hsum : (W.card : Real) = ∑ h ∈ T, f h := by
    rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst)
      (fun p hp => (Finset.mem_product.mp (hW hp)).1)]
    push_cast; rfl
  rw [← Finset.sum_filter_add_sum_filter_not T fun h => t * J.card ≤ f h] at hsum
  -- popular fibres have at most `|J|` points, the others fewer than `t|J|`
  have h1 := Finset.sum_le_card_nsmul (T.filter fun h => t * J.card ≤ f h) f J.card fun h _ =>
    show ((W.filter fun p => p.1 = h).card : Real) ≤ J.card from Nat.cast_le.mpr <|
      Finset.card_le_card_of_injOn Prod.snd
        (fun p hp => (Finset.mem_product.mp (hW (Finset.mem_filter.mp hp).1)).2)
        fun p hp p' hp' he =>
          Prod.ext ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hp').2.symm) he
  have h2 := Finset.sum_le_card_nsmul (T.filter fun h => ¬ t * J.card ≤ f h) f (t * J.card)
    fun h hh => (not_le.mp (Finset.mem_filter.mp hh).2).le
  have h3 : ((T.filter fun h => ¬ t * J.card ≤ f h).card : Real) ≤ T.card := by
    exact_mod_cast Finset.card_filter_le _ _
  rw [nsmul_eq_mul] at h1 h2
  have hmain : t * T.card * J.card ≤ (T.filter fun h => t * J.card ≤ f h).card * J.card := by
    linarith [mul_le_mul_of_nonneg_right h3 (by positivity : (0 : Real) ≤ t * J.card)]
  exact le_of_mul_le_mul_right hmain (by exact_mod_cast hJ)

/-- Fibres of size `≥ t|J|` over `H` give `|H|·t|J|` points. -/
theorem fibre_sum_ge (W : Finset (A × ZMod N)) (H : Finset A) {s : Real}
    (hH : ∀ h ∈ H, s ≤ (W.filter fun p => p.1 = h).card) :
    (H.card : Real) * s ≤ (W.filter fun p => p.1 ∈ H).card := by
  have hfw := Finset.card_eq_sum_card_fiberwise (f := Prod.fst)
    (s := W.filter fun p => p.1 ∈ H) (t := H) (fun p hp => (Finset.mem_filter.mp hp).2)
  rw [hfw]
  push_cast
  calc (H.card : Real) * s = ∑ _h ∈ H, s := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
      refine Finset.sum_le_sum fun h hh => ?_
      have he : ((W.filter fun p => p.1 ∈ H).filter fun p => p.1 = h) =
          W.filter fun p => p.1 = h := by
        ext p
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨⟨hp, -⟩, he⟩; exact ⟨hp, he⟩
        · rintro ⟨hp, he⟩; exact ⟨⟨hp, he ▸ hh⟩, he⟩
      rw [he]; exact hH h hh

/-! ### Slice schemes

The line-cell argument uses the cross-sections `φ(·, x)` in one step only: on
a dense set `H` of a box `T` whose sections at two anchors satisfy the slice
condition, it needs a sub-box on which a fixed fraction of `H` agrees with a
multilinear function at both anchors (Notes L.16q). A slice scheme packages
that step together with its width and density. `localPieceScheme` uses local
piece providers, one section after the other; `jointSliceScheme`
(`Proofs16JointSliceCell`) covers both sections at once. -/

/-- A slice condition with the width and the density of its two-section step. -/
structure SliceScheme (N k : Nat) [NeZero N] where
  /-- The condition on a cross-section `g` with domain `D`. -/
  SL : Finset (Point N k) → (Point N k → ZMod N) → Prop
  /-- The width of the two-section box at density `θ`, from the width `L` of the box. -/
  wid : Real → Nat → Nat
  /-- The fraction of the dense set that agrees at both sections. -/
  dens : Real → Real
  wid_mono : ∀ θ : Real, 0 < θ → θ ≤ 1 → Monotone (wid θ)
  dens_pos : ∀ θ : Real, 0 < θ → θ ≤ 1 → 0 < dens θ
  step : ∀ θ : Real, 0 < θ → θ ≤ 1 → ∀ (T : Box N k) (H Da Db : Finset (Point N k))
    (ga gb : Point N k → ZMod N), T.IsProper → T.carrier.Nonempty → H ⊆ T.carrier → H ⊆ Da →
    H ⊆ Db → θ * T.carrier.card ≤ H.card → SL Da ga → SL Db gb →
    ∃ (R : Box N k) (ma mb : Point N k → ZMod N), R.IsProper ∧ R.carrier ⊆ T.carrier ∧
      wid θ T.width ≤ R.width ∧ IsMultilinear ma ∧ IsMultilinear mb ∧
      dens θ * R.carrier.card ≤
        (H.filter fun x => x ∈ R.carrier ∧ ga x = ma x ∧ gb x = mb x).card

theorem SliceScheme.congr {N k : Nat} [NeZero N] (Sc : SliceScheme N k)
    {D : Finset (Point N k)} {g g' : Point N k → ZMod N} (h : Sc.SL D g)
    (hg : ∀ x, g' x = g x) : Sc.SL D g' := by
  obtain rfl : g' = g := funext hg
  exact h

/-- Local piece providers, applied to the first section and then, inside its
agreement set, to the second: width `w (c θ) (w θ L)`, density `c (c θ)`. -/
def localPieceScheme {N k : Nat} [NeZero N] (c : Real → Real) (w : Real → Nat → Nat)
    (hc : ∀ t, 0 < t → t ≤ 1 → 0 < c t ∧ c t ≤ 1) (hw : ∀ t, Monotone (w t)) :
    SliceScheme N k where
  SL := LocalPieceFor c w
  wid θ L := w (c θ) (w θ L)
  dens θ := c (c θ)
  wid_mono θ _ _ := (hw _).comp (hw θ)
  dens_pos θ hθ hθ1 := (hc _ (hc θ hθ hθ1).1 (hc θ hθ hθ1).2).1
  step θ hθ hθ1 T H Da Db ga gb hT _ hHT hHa hHb hHc ha hb := by
    obtain ⟨R1, mua, hR1, hR1T, hR1w, hmua, hR1c⟩ := ha θ hθ hθ1 T H hT hHT hHa hHc
    obtain ⟨hcpos, hcle⟩ := hc θ hθ hθ1
    obtain ⟨R2, mub, hR2, hR2R1, hR2w, hmub, hR2c⟩ := hb (c θ) hcpos hcle R1
      (H.filter fun x => x ∈ R1.carrier ∧ ga x = mua x) hR1
      (fun x hx => (Finset.mem_filter.mp hx).2.1)
      (fun x hx => hHb (Finset.filter_subset _ _ hx)) hR1c
    refine ⟨R2, mua, mub, hR2, hR2R1.trans hR1T, (hw _ hR1w).trans hR2w, hmua, hmub,
      hR2c.trans ?_⟩
    exact_mod_cast Finset.card_le_card fun x hx => by
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1.1, hx.2.1, hx.1.2.2, hx.2.2⟩

/-- **One multilinear piece on a line-covered cell**, for cross-sections
`φ(·, x)` satisfying the slice condition of a scheme. -/
theorem single_piece_on_line_cell_of_scheme {k q : Nat} (hk : 0 < k)
    {N : Nat} [NeZero N] [Fact N.Prime] (Sc : SliceScheme N k)
    (T : Box N k) (J : ModAP N) (hT : T.IsProper) (hJ : J.IsProper) (hTne : T.carrier.Nonempty)
    (hTd : T.commonDiff ≠ 0) (hJstep : J.step = T.commonDiff)
    (hshort : 2 * (T.axis ⟨0, hk⟩).length ≤ N) (hTJ : (T.axis ⟨0, hk⟩).length ≤ J.length)
    (D : Finset (Point N k × ZMod N)) (hD : D ⊆ T.carrier ×ˢ J.carrier)
    {theta : Real} (hθ : 0 < theta) (hθ1 : theta ≤ 1) (hq : 0 < q)
    (hDc : theta * T.carrier.card * J.carrier.card ≤ D.card)
    (hJq : 2 * (q : Real) ^ 2 ≤ theta ^ 3 * J.length)
    (cls : Point N k × ZMod N → Fin q) (phi : Point N k × ZMod N → ZMod N)
    (ell : Point N k → Fin q → ZMod N → ZMod N) (hell : ∀ h i, LinearOn Finset.univ (ell h i))
    (hphi : ∀ p ∈ D, phi p = ell p.1 (cls p) p.2)
    (Dom : ZMod N → Finset (Point N k))
    (hsl : ∀ x ∈ J.carrier, Sc.SL (Dom x) (fun h => phi (h, x)))
    (hDom : ∀ p ∈ D, p.1 ∈ Dom p.2)
    (hwidth : 2 ≤ Sc.wid (singlePieceTheta theta q) T.width) :
    ∃ (S : Box N (k + 1)) (R : Box N k) (I : ModAP N) (mu : Point N (k + 1) → ZMod N),
      S.IsProper ∧ IsLastCoordinateBoxProduct S R I ∧ R.carrier ⊆ T.carrier ∧
      S.carrier ⊆ lastProductSet T.carrier J.carrier ∧
      Nat.sqrt (Sc.wid (singlePieceTheta theta q) T.width - 1) - 1 ≤ S.width ∧
      IsMultilinear mu ∧
      singlePieceTheta theta q * Sc.dens (singlePieceTheta theta q) * S.carrier.card ≤
        (D.filter fun p => appendCoordinate p.1 p.2 ∈ S.carrier ∧
          phi p = mu (appendCoordinate p.1 p.2)).card := by
  set θ1 := singlePieceTheta theta q with hθ1def
  have hθ1pos : 0 < θ1 := singlePieceTheta_pos hθ hq
  have hθ1le : θ1 ≤ 1 := singlePieceTheta_le_one hθ hθ1 hq
  have hqR : (1 : Real) ≤ q := by exact_mod_cast hq
  have hJcard : J.carrier.card = J.length := hJ
  have hJpos : (0 : Real) < J.carrier.card := by rw [hJcard]; nlinarith [pow_pos hθ 3]
  have hTpos : (0 : Real) < T.carrier.card := by exact_mod_cast hTne.card_pos
  -- 1. one anchor pair, capturing `W` with `|W| ≥ 2θ₁|T||J|`
  obtain ⟨a, ha, b, hb, hcap⟩ := exists_anchor_pair_capture T.carrier J.carrier D hD
    (Finset.card_pos.mp (by exact_mod_cast (by positivity : (0 : Real) <
      theta * T.carrier.card * J.carrier.card).trans_le hDc)) cls
  set W := anchorCapture D cls a b
  have hWD : W ⊆ D := Finset.filter_subset _ _
  have hWc : 2 * θ1 * T.carrier.card * J.carrier.card ≤ W.card :=
    (le_of_eq (by rw [hθ1def, singlePieceTheta]; ring)).trans <| capture_density hθ hqR hTpos
      hJpos hDc (by exact_mod_cast (Finset.card_le_card hD).trans (Finset.card_product _ _).le)
      hcap (by rw [hJcard]; exact hJq)
  -- 2. popular fibres: `θ₁|T|` base points carry `θ₁|J|` captured points each
  set H1 := T.carrier.filter fun h =>
    θ1 * J.carrier.card ≤ ((W.filter fun p => p.1 = h).card : Real)
  have hH1 : θ1 * T.carrier.card ≤ H1.card :=
    popular_fibres T.carrier J.carrier W (hWD.trans hD) (by exact_mod_cast hJpos) hθ1pos.le hWc
  have hslice : ∀ h ∈ H1, (h, a) ∈ D ∧ (h, b) ∈ D := by
    intro h hh
    obtain ⟨p, hp⟩ : (W.filter fun p => p.1 = h).Nonempty := Finset.card_pos.mp <| by
      exact_mod_cast (by positivity : (0 : Real) < θ1 * J.carrier.card).trans_le
        (Finset.mem_filter.mp hh).2
    obtain ⟨hpW, rfl⟩ := Finset.mem_filter.mp hp
    obtain ⟨-, -, hpa, hpb⟩ := Finset.mem_filter.mp hpW
    exact ⟨(Finset.mem_filter.mp hpa).1, (Finset.mem_filter.mp hpb).1⟩
  -- 3. both cross-sections, by the scheme
  obtain ⟨R2, mua, mub, hR2, hR2T, hR2width, hmua, hmub, hR2c⟩ :=
    Sc.step θ1 hθ1pos hθ1le T H1 (Dom a) (Dom b) _ _ hT hTne (Finset.filter_subset _ _)
      (fun h hh => hDom _ (hslice h hh).1) (fun h hh => hDom _ (hslice h hh).2) hH1
      (hsl a ha) (hsl b hb)
  set H3 := H1.filter fun x => x ∈ R2.carrier ∧ phi (x, a) = mua x ∧ phi (x, b) = mub x
  have hR2c : Sc.dens θ1 * R2.carrier.card ≤ H3.card := hR2c
  have hR2two : 2 ≤ R2.width := hwidth.trans hR2width
  -- 4. reconstruction on the doubly agreeing fibres
  set mu := section16TwoAnchorLift a b mua mub with hmudef
  set G := W.filter fun p => p.1 ∈ H3
  have hGagree : ∀ p ∈ G, phi p = mu (appendCoordinate p.1 p.2) := by
    intro p hp
    obtain ⟨hpW, hpH3⟩ := Finset.mem_filter.mp hp
    obtain ⟨-, -, ha', hb'⟩ := Finset.mem_filter.mp hpH3
    have : a - b ≠ 0 := sub_ne_zero.mpr (Finset.mem_filter.mp hpW).2.1
    rw [anchor_reconstruction D cls phi ell hell hphi hpW, ha', hb']
    simp only [hmudef, section16TwoAnchorLift, appendCoordinate_eq_snoc, Fin.init_snoc,
      Fin.snoc_last]
    field_simp
    ring
  have hGcard : Sc.dens θ1 * R2.carrier.card * (θ1 * J.carrier.card) ≤ G.card :=
    (mul_le_mul_of_nonneg_right hR2c (by positivity)).trans <| fibre_sum_ge W H3
      (s := θ1 * J.carrier.card) fun h hh => (Finset.mem_filter.mp (Finset.filter_subset _ _ hh)).2
  -- 5. synchronized retiling of `R2 × J`; one cell carries its share of `G`
  set i : Fin k := ⟨0, hk⟩
  have hR2ne : R2.carrier.Nonempty :=
    R2.carrier_nonempty_of_axis_pos fun j => lt_of_lt_of_le (by omega) (R2.width_le_axis_length j)
  obtain ⟨M, S, I, hSpart, hSprop, hSprod, -⟩ :=
    box_product_tiling_of_contained_axis R2 (T.axis i) J i (Units.mk0 T.commonDiff hTd) hR2 hJ
      (by rw [Units.val_mk0, T.axis_step i]) (hJstep.trans (T.axis_step i).symm)
      (R2.axis_carrier_subset_of_carrier_subset T hR2ne hR2T i) hshort hTJ
      (Nat.le_sqrt.mpr (by omega)) (Nat.sqrt_le' _)
  let Z : Fin M → Finset (Point N k × ZMod N) := fun j => D.filter fun p =>
    appendCoordinate p.1 p.2 ∈ (S j).carrier ∧ phi p = mu (appendCoordinate p.1 p.2)
  have hsub : G ⊆ Finset.univ.biUnion Z := by
    intro p hp
    obtain ⟨hpW, hpH3⟩ := Finset.mem_filter.mp hp
    obtain ⟨j, hj⟩ := (hSpart.1 (appendCoordinate p.1 p.2)).mp <| by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, section16Init_appendCoordinate,
        section16Last_appendCoordinate]
      exact ⟨(Finset.mem_filter.mp hpH3).2.1, (Finset.mem_product.mp (hD (hWD hpW))).2⟩
    exact Finset.mem_biUnion.mpr
      ⟨j, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hWD hpW, hj, hGagree p hp⟩⟩
  have hZ : (G.card : Real) ≤ ∑ j, ((Z j).card : Real) := by
    exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hSsum : ∑ j, ((S j).carrier.card : Real) = R2.carrier.card * J.carrier.card := by
    exact_mod_cast hSpart.sum_card.trans (lastProductSet_card R2.carrier J.carrier)
  have hle : ∑ j, θ1 * Sc.dens θ1 * (S j).carrier.card ≤ ∑ j, ((Z j).card : Real) := by
    rw [← Finset.mul_sum, hSsum]
    linarith
  obtain ⟨j, -, hj⟩ := Finset.exists_le_of_sum_le (Finset.nonempty_of_sum_ne_zero
    (hSsum.trans_ne (mul_pos (by exact_mod_cast hR2ne.card_pos) hJpos).ne')) hle
  refine ⟨S j, R2, I j, mu, (hSprop j).1, hSprod j, hR2T, (hSpart.cell_subset j).trans
    fun x hx => ?_, (Nat.sub_le_sub_right (Nat.sqrt_le_sqrt (Nat.sub_le_sub_right hR2width 1))
      1).trans (hSprop j).2, section16TwoAnchorLift_multilinear a b hmua hmub, hj⟩
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, hR2T (Finset.mem_filter.mp hx).2.1, (Finset.mem_filter.mp hx).2.2⟩

end LeanProofs.GowersSzemeredi
