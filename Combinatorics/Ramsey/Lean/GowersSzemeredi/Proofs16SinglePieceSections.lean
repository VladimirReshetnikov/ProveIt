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
union does not arise here. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- The dimension-`k` input: one dense multilinear piece on a proper sub-box. -/
def LocalMultilinearPieceAt (k : Nat) (gamma : Real) (c : Real → Real)
    (w : Real → Nat → Nat) : Prop :=
  ∀ (N : Nat) [NeZero N] [Fact N.Prime] (theta : Real), 0 < theta → theta ≤ 1 →
    ∀ (P : Box N k) (B : Finset (Point N k)) (phi : Point N k → ZMod N),
      P.IsProper → B ⊆ P.carrier → theta * P.carrier.card ≤ B.card →
      HasProductProperty B phi gamma →
      ∃ (R : Box N k) (mu : Point N k → ZMod N),
        R.IsProper ∧ R.carrier ⊆ P.carrier ∧ w theta P.width ≤ R.width ∧ IsMultilinear mu ∧
        c theta * R.carrier.card ≤ (B.filter fun x => x ∈ R.carrier ∧ phi x = mu x).card

/-- A local piece provider for one function on a domain. -/
def LocalPieceFor {N d : Nat} [NeZero N] (c : Real → Real) (w : Real → Nat → Nat)
    (Dom : Finset (Point N d)) (g : Point N d → ZMod N) : Prop :=
  ∀ theta : Real, 0 < theta → theta ≤ 1 →
    ∀ (P : Box N d) (H : Finset (Point N d)), P.IsProper → H ⊆ P.carrier → H ⊆ Dom →
      theta * P.carrier.card ≤ H.card →
      ∃ (R : Box N d) (mu : Point N d → ZMod N),
        R.IsProper ∧ R.carrier ⊆ P.carrier ∧ w theta P.width ≤ R.width ∧ IsMultilinear mu ∧
        c theta * R.carrier.card ≤ (H.filter fun x => x ∈ R.carrier ∧ g x = mu x).card

/-- **The input gives providers.** -/
theorem LocalMultilinearPieceAt.localPieceFor {d : Nat} {gamma : Real} {c : Real → Real}
    {w : Real → Nat → Nat} (hprov : LocalMultilinearPieceAt d gamma c w)
    {N : Nat} [NeZero N] [Fact N.Prime] {Dom : Finset (Point N d)} {g : Point N d → ZMod N}
    (hprod : ∀ B ⊆ Dom, HasProductProperty B g gamma) : LocalPieceFor c w Dom g :=
  fun theta hθ hθ1 P H hP hHP hHD hHc =>
    hprov N theta hθ hθ1 P H g hP hHP hHc (hprod H hHD)

/-- The density of the popular fibres: `θ³/(4q²)`. -/
def singlePieceTheta (theta : Real) (q : Nat) : Real :=
  theta ^ 3 / (4 * (q : Real) ^ 2)

/-- The density of the lifted piece. -/
def singlePieceDensity (c : Real → Real) (theta : Real) (q : Nat) : Real :=
  singlePieceTheta theta q * c (c (singlePieceTheta theta q))

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
  have hd0 : 0 ≤ d := le_trans (by positivity) hd
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
  set f : A → Real := fun h => ((W.filter fun p => p.1 = h).card : Real) with hf
  set H := T.filter fun h => t * J.card ≤ f h with hH
  have hsum : (W.card : Real) = ∑ h ∈ T, f h := by
    rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst)
      (fun p hp => (Finset.mem_product.mp (hW hp)).1)]
    push_cast; rfl
  have hfib : ∀ h, f h ≤ J.card := by
    intro h
    simp only [hf]
    have hc : (W.filter fun p => p.1 = h).card ≤ J.card := by
      refine Finset.card_le_card_of_injOn (fun p : A × ZMod N => p.2) ?_ ?_
      · intro p hp
        exact (Finset.mem_product.mp (hW (Finset.mem_filter.mp hp).1)).2
      · intro p hp p' hp' he
        have e1 : p.1 = h := (Finset.mem_filter.mp hp).2
        have e2 : p'.1 = h := (Finset.mem_filter.mp hp').2
        exact Prod.ext (e1.trans e2.symm) he
    exact_mod_cast hc
  have hsplit := Finset.sum_filter_add_sum_filter_not T (fun h => t * J.card ≤ f h) f
  have h1 : ∑ h ∈ H, f h ≤ H.card * J.card := by
    calc ∑ h ∈ H, f h ≤ ∑ _h ∈ H, (J.card : Real) := Finset.sum_le_sum fun h _ => hfib h
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have h2 : ∑ h ∈ T.filter (fun h => ¬ t * J.card ≤ f h), f h ≤ T.card * (t * J.card) := by
    calc ∑ h ∈ T.filter (fun h => ¬ t * J.card ≤ f h), f h
        ≤ ∑ _h ∈ T.filter (fun h => ¬ t * J.card ≤ f h), t * (J.card : Real) :=
          Finset.sum_le_sum fun h hh => le_of_lt (not_le.mp (Finset.mem_filter.mp hh).2)
      _ ≤ ∑ _h ∈ T, t * (J.card : Real) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => by positivity)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hJR : (0 : Real) < J.card := by exact_mod_cast hJ
  have hmain : t * T.card * J.card ≤ H.card * J.card := by
    have hW' : (W.card : Real) = (∑ h ∈ H, f h) +
        ∑ h ∈ T.filter (fun h => ¬ t * J.card ≤ f h), f h := hsum.trans hsplit.symm
    nlinarith
  exact le_of_mul_le_mul_right hmain hJR

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

/-- **One multilinear piece on a line-covered cell**, from providers for the
cross-sections `φ(·, x)`. -/
theorem single_piece_on_line_cell_of_slices {k q : Nat} (hk : 0 < k)
    {c : Real → Real} {w : Real → Nat → Nat}
    (hc : ∀ t, 0 < t → t ≤ 1 → 0 < c t ∧ c t ≤ 1) (hw : ∀ t, Monotone (w t))
    {N : Nat} [NeZero N] [Fact N.Prime]
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
    (hsl : ∀ x ∈ J.carrier, LocalPieceFor c w (Dom x) (fun h => phi (h, x)))
    (hDom : ∀ p ∈ D, p.1 ∈ Dom p.2)
    (hwidth : 2 ≤ w (c (singlePieceTheta theta q)) (w (singlePieceTheta theta q) T.width)) :
    ∃ (S : Box N (k + 1)) (R : Box N k) (I : ModAP N) (mu : Point N (k + 1) → ZMod N),
      S.IsProper ∧ IsLastCoordinateBoxProduct S R I ∧ R.carrier ⊆ T.carrier ∧
      S.carrier ⊆ lastProductSet T.carrier J.carrier ∧
      Nat.sqrt (w (c (singlePieceTheta theta q)) (w (singlePieceTheta theta q) T.width) - 1) - 1
        ≤ S.width ∧
      IsMultilinear mu ∧
      singlePieceDensity c theta q * S.carrier.card ≤
        (D.filter fun p => appendCoordinate p.1 p.2 ∈ S.carrier ∧
          phi p = mu (appendCoordinate p.1 p.2)).card := by
  set θ1 := singlePieceTheta theta q with hθ1def
  have hθ1pos : 0 < θ1 := singlePieceTheta_pos hθ hq
  have hθ1le : θ1 ≤ 1 := singlePieceTheta_le_one hθ hθ1 hq
  have hqR : (1 : Real) ≤ q := by exact_mod_cast hq
  have hJcard : J.carrier.card = J.length := hJ
  have hJpos : (0 : Real) < J.carrier.card := by
    rw [hJcard]
    have h0 : (0 : Real) < theta ^ 3 * J.length := by nlinarith
    exact pos_of_mul_pos_right h0 (by positivity)
  have hTpos : (0 : Real) < T.carrier.card := by exact_mod_cast hTne.card_pos
  -- 1. one anchor pair
  have hDne : D.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : Real) < D.card := lt_of_lt_of_le (by positivity) hDc
    exact_mod_cast this
  obtain ⟨a, ha, b, hb, hcap⟩ := exists_anchor_pair_capture T.carrier J.carrier D hD hDne cls
  set W := anchorCapture D cls a b with hWdef
  have hWD : W ⊆ D := Finset.filter_subset _ _
  have hDle : (D.card : Real) ≤ T.carrier.card * J.carrier.card := by
    exact_mod_cast (Finset.card_le_card hD).trans (Finset.card_product _ _).le
  have hWc : 2 * θ1 * T.carrier.card * J.carrier.card ≤ W.card := by
    have h := capture_density hθ hqR hTpos hJpos hDc hDle hcap (by rw [hJcard]; exact hJq)
    calc 2 * θ1 * (T.carrier.card : Real) * J.carrier.card =
        theta ^ 3 / (2 * q ^ 2) * T.carrier.card * J.carrier.card := by
          rw [hθ1def, singlePieceTheta]; ring
      _ ≤ _ := h
  -- 2. popular fibres
  set H1 := T.carrier.filter fun h =>
    θ1 * J.carrier.card ≤ ((W.filter fun p => p.1 = h).card : Real) with hH1def
  have hH1 : θ1 * T.carrier.card ≤ H1.card :=
    popular_fibres T.carrier J.carrier W (hWD.trans hD) (by exact_mod_cast hJpos) hθ1pos.le hWc
  have hslice : ∀ h ∈ H1, (h, a) ∈ D ∧ (h, b) ∈ D := by
    intro h hh
    have hpos : 0 < (W.filter fun p => p.1 = h).card := by
      have h1 := (Finset.mem_filter.mp hh).2
      have : (0 : Real) < (W.filter fun p => p.1 = h).card :=
        lt_of_lt_of_le (by positivity) h1
      exact_mod_cast this
    obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
    obtain ⟨hpW, rfl⟩ := Finset.mem_filter.mp hp
    obtain ⟨-, -, hpa, hpb⟩ := Finset.mem_filter.mp hpW
    exact ⟨(Finset.mem_filter.mp hpa).1, (Finset.mem_filter.mp hpb).1⟩
  -- 3. the cross-section at `a`, then at `b`
  obtain ⟨R1, mua, hR1, hR1T, hR1w, hmua, hR1c⟩ := hsl a ha θ1 hθ1pos hθ1le T H1 hT
    (Finset.filter_subset _ _) (fun h hh => hDom _ (hslice h hh).1) hH1
  set H2 := H1.filter fun x => x ∈ R1.carrier ∧ phi (x, a) = mua x with hH2def
  obtain ⟨hcpos, hcle⟩ := hc θ1 hθ1pos hθ1le
  obtain ⟨R2, mub, hR2, hR2R1, hR2w, hmub, hR2c⟩ := hsl b hb (c θ1) hcpos hcle R1 H2 hR1
    (fun x hx => (Finset.mem_filter.mp hx).2.1)
    (fun h hh => hDom _ (hslice h (Finset.filter_subset _ _ hh)).2) hR1c
  set H3 := H2.filter fun x => x ∈ R2.carrier ∧ phi (x, b) = mub x with hH3def
  have hR2width : w (c θ1) (w θ1 T.width) ≤ R2.width := (hw _ hR1w).trans hR2w
  have hR2two : 2 ≤ R2.width := hwidth.trans hR2width
  -- 4. reconstruction on the doubly agreeing fibres
  set mu := section16TwoAnchorLift a b mua mub with hmudef
  have hmu : IsMultilinear mu := section16TwoAnchorLift_multilinear a b hmua hmub
  set G := W.filter fun p => p.1 ∈ H3 with hGdef
  have hGagree : ∀ p ∈ G, phi p = mu (appendCoordinate p.1 p.2) := by
    intro p hp
    obtain ⟨hpW, hpH3⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpH2, -, hb'⟩ := Finset.mem_filter.mp hpH3
    obtain ⟨-, -, ha'⟩ := Finset.mem_filter.mp hpH2
    have hne : a ≠ b := (Finset.mem_filter.mp hpW).2.1
    rw [anchor_reconstruction D cls phi ell hell hphi hpW, ha', hb']
    simp only [hmudef, section16TwoAnchorLift, appendCoordinate_eq_snoc, Fin.init_snoc,
      Fin.snoc_last]
    have : a - b ≠ 0 := sub_ne_zero.mpr hne
    field_simp
    ring
  have hGcard : c (c θ1) * R2.carrier.card * (θ1 * J.carrier.card) ≤ G.card := by
    have h := fibre_sum_ge W H3 (s := θ1 * J.carrier.card) fun h hh =>
      (Finset.mem_filter.mp (Finset.filter_subset _ _ (Finset.filter_subset _ _ hh))).2
    exact (mul_le_mul_of_nonneg_right hR2c (by positivity)).trans h
  -- 5. synchronized retiling of `R2 × J`
  set i : Fin k := ⟨0, hk⟩
  have hR2ne : R2.carrier.Nonempty :=
    R2.carrier_nonempty_of_axis_pos fun j => lt_of_lt_of_le (by omega) (R2.width_le_axis_length j)
  have hsub : (R2.axis i).carrier ⊆ (T.axis i).carrier :=
    R2.axis_carrier_subset_of_carrier_subset T hR2ne (hR2R1.trans hR1T) i
  set v := Nat.sqrt (R2.width - 1) with hvdef
  have hv : 1 ≤ v := Nat.le_sqrt.mpr (by omega)
  have hfit : v ^ 2 ≤ R2.width - 1 := Nat.sqrt_le' _
  obtain ⟨M, S, I, hSpart, hSprop, hSprod, -⟩ :=
    box_product_tiling_of_contained_axis R2 (T.axis i) J i (Units.mk0 T.commonDiff hTd) hR2 hJ
      (by rw [Units.val_mk0, T.axis_step i]) (hJstep.trans (T.axis_step i).symm) hsub hshort
      hTJ hv hfit
  -- the agreement points split along the cells
  have hGin : ∀ p ∈ G, appendCoordinate p.1 p.2 ∈ lastProductSet R2.carrier J.carrier := by
    intro p hp
    obtain ⟨hpW, hpH3⟩ := Finset.mem_filter.mp hp
    simp only [lastProductSet, Finset.mem_filter, Finset.mem_univ, true_and,
      section16Init_appendCoordinate, section16Last_appendCoordinate]
    exact ⟨(Finset.mem_filter.mp hpH3).2.1, (Finset.mem_product.mp (hD (hWD hpW))).2⟩
  let Gj : Fin M → Finset (Point N k × ZMod N) := fun j =>
    G.filter fun p => appendCoordinate p.1 p.2 ∈ (S j).carrier
  have hGpart : IsPartition Gj G := by
    refine ⟨fun p => ⟨fun hp => ?_, fun ⟨j, hj⟩ => (Finset.mem_filter.mp hj).1⟩, ?_⟩
    · obtain ⟨j, hj⟩ := (hSpart.1 _).mp (hGin p hp)
      exact ⟨j, Finset.mem_filter.mpr ⟨hp, hj⟩⟩
    · intro j j' hjj'
      refine Finset.disjoint_left.mpr fun p hp hp' => ?_
      exact Finset.disjoint_left.mp (hSpart.2 j j' hjj') (Finset.mem_filter.mp hp).2
        (Finset.mem_filter.mp hp').2
  have hGsum : ∑ j, ((Gj j).card : Real) = G.card := by exact_mod_cast hGpart.sum_card
  have hSsum : ∑ j, ((S j).carrier.card : Real) = R2.carrier.card * J.carrier.card := by
    have h := hSpart.sum_card
    have h' : (Finset.univ.filter fun x : Point N (k + 1) =>
        section16Init x ∈ R2.carrier ∧ section16Last x ∈ J.carrier).card =
        R2.carrier.card * J.carrier.card := lastProductSet_card R2.carrier J.carrier
    rw [h'] at h
    exact_mod_cast h
  have hMne : (Finset.univ : Finset (Fin M)).Nonempty := by
    have hRpos : (0 : Real) < R2.carrier.card := by exact_mod_cast hR2ne.card_pos
    have hc2pos := (hc (c θ1) hcpos hcle).1
    have hGpos : 0 < G.card := by
      have : (0 : Real) < G.card :=
        lt_of_lt_of_le (mul_pos (mul_pos hc2pos hRpos) (mul_pos hθ1pos hJpos)) hGcard
      exact_mod_cast this
    obtain ⟨p, hp⟩ := Finset.card_pos.mp hGpos
    obtain ⟨j, -⟩ := (hSpart.1 _).mp (hGin p hp)
    exact ⟨j, Finset.mem_univ j⟩
  have hle : ∑ j, singlePieceDensity c theta q * (S j).carrier.card ≤ ∑ j, ((Gj j).card : Real) := by
    rw [← Finset.mul_sum, hSsum, hGsum]
    calc singlePieceDensity c theta q * (R2.carrier.card * J.carrier.card) =
        c (c θ1) * R2.carrier.card * (θ1 * J.carrier.card) := by
          rw [singlePieceDensity, ← hθ1def]; ring
      _ ≤ _ := hGcard
  obtain ⟨j, -, hj⟩ := Finset.exists_le_of_sum_le hMne hle
  refine ⟨S j, R2, I j, mu, (hSprop j).1, hSprod j, hR2R1.trans hR1T, ?_, ?_, hmu, ?_⟩
  · intro x hx
    have hx' := IsPartition.cell_subset hSpart j hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx'
    simp only [lastProductSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hR1T (hR2R1 hx'.1), hx'.2⟩
  · have hsq : Nat.sqrt (w (c θ1) (w θ1 T.width) - 1) ≤ v :=
      Nat.sqrt_le_sqrt (Nat.sub_le_sub_right hR2width 1)
    have := (hSprop j).2
    omega
  · refine hj.trans ?_
    exact_mod_cast Finset.card_le_card fun p hp => by
      obtain ⟨hpG, hpS⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨hWD (Finset.mem_filter.mp hpG).1, hpS, hGagree p hpG⟩


/-- **One multilinear piece on a line-covered cell**, from the dimension-`k`
input and the product property of the cross-sections. -/
theorem single_piece_on_line_cell {k q : Nat} (hk : 0 < k) {gamma : Real}
    {c : Real → Real} {w : Real → Nat → Nat} (hprov : LocalMultilinearPieceAt k gamma c w)
    (hc : ∀ t, 0 < t → t ≤ 1 → 0 < c t ∧ c t ≤ 1) (hw : ∀ t, Monotone (w t))
    {N : Nat} [NeZero N] [Fact N.Prime]
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
    (hprod : ∀ x ∈ J.carrier, ∀ B : Finset (Point N k), (∀ h ∈ B, (h, x) ∈ D) →
      HasProductProperty B (fun h => phi (h, x)) gamma)
    (hwidth : 2 ≤ w (c (singlePieceTheta theta q)) (w (singlePieceTheta theta q) T.width)) :
    ∃ (S : Box N (k + 1)) (R : Box N k) (I : ModAP N) (mu : Point N (k + 1) → ZMod N),
      S.IsProper ∧ IsLastCoordinateBoxProduct S R I ∧ R.carrier ⊆ T.carrier ∧
      S.carrier ⊆ lastProductSet T.carrier J.carrier ∧
      Nat.sqrt (w (c (singlePieceTheta theta q)) (w (singlePieceTheta theta q) T.width) - 1) - 1
        ≤ S.width ∧
      IsMultilinear mu ∧
      singlePieceDensity c theta q * S.carrier.card ≤
        (D.filter fun p => appendCoordinate p.1 p.2 ∈ S.carrier ∧
          phi p = mu (appendCoordinate p.1 p.2)).card :=
  single_piece_on_line_cell_of_slices hk hc hw T J hT hJ hTne hTd hJstep hshort hTJ D hD
    hθ hθ1 hq hDc hJq cls phi ell hell hphi (fun x => Finset.univ.filter fun h => (h, x) ∈ D)
    (fun x hx => hprov.localPieceFor fun B hB =>
      hprod x hx B fun h hh => (Finset.mem_filter.mp (hB hh)).2)
    (fun p hp => Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using hp⟩) hwidth

end LeanProofs.GowersSzemeredi
