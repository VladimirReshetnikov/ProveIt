import GowersSzemeredi.Proofs16WithLemma9

/-! Lemma 16.9 at every scale with arbitrary remainder controls, for an
abstract linearity width.

`AllScalePolynomialLemma169At` takes the cross-section remainder
`φ − φ₁` with Gowers's printed `(γ, R)` controls, where
`R = section16Lemma9R θ γ k` is of size `(1/θγ)^(2^128)`. Its graph count
`section16Lemma9QBound` and its width exponent `multipleC(σ/2R,γ,k+1)^R`
are the first of the non-polynomial losses listed in Notes L.3.

The proof uses the remainder only through one cover at loss `σ/2`, so any
controls `(Qr, Er)` can be used. The count is then `Qr (σ/2)` and the width
exponent `Er (σ/2) · Eb (σ/2)`.

The all-scale Lemma 16.6 enters only through its statement. That statement
is copied here with the linearity width abstracted to `W m q a ζ`
(`AllScaleLemma166WidthAt`). This keeps the module off the import closure of
the polynomial recurrence, which builds the OpenAI Schmidt stack.
`AllScalePolynomialLemma166At k C p` is definitionally the instance
`W = section16PolynomialLinearityWidth · k C p`.
* `AllScaleLemma166WidthAt`, `AllScaleLemma169WithAt`.
* `allScaleLemma169SubdomainAt_of`: Lemma 16.9 from Lemma 16.6 for any width
  that transfers along cell refinements (`Section16WidthTransfer`), with the
  remainder covered on any sub-domain `D ⊆ B₁` (`AllScaleLemma169SubdomainAt`);
  `allScaleLemma169WithAt_of` is the case `D = B₁`.
* `allScaleLemma169WithAt_printed`: the specialization to the printed
  remainder controls, in the form of `AllScalePolynomialLemma169At`. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- Lemma 16.6 at every scale, for an abstract linearity width `W m q a ζ`
(input width `m`, spectrum count `q`, spectrum width exponent `a`). -/
def AllScaleLemma166WidthAt (k : Nat) (W : Nat → Nat → Real → Real → Real) : Prop :=
  ∀ (N m : Nat) [NeZero N] [Fact N.Prime], 1 ≤ k →
    ∀ (theta gamma sigma : Real),
    0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 →
    0 < sigma → sigma ≤ 1 →
    ∀ (Qb Eb : Real → Real), 0 ≤ Qb sigma → 0 < Eb sigma → Eb sigma ≤ 1 →
    ∀ (B : Finset (Point N (k + 1)))
      (phi : Point N (k + 1) → ZMod N)
      (H Jbase H1 : Finset (Point N k))
      (Y : (h : Point N k) → Finset (Section16CubeElement B h))
      (phiPrime : Point N k → ZMod N → ZMod N),
    let theta1 := section16ThetaOne theta gamma k
    let delta := section16Delta theta1
    let zeta := section16Zeta theta gamma k
    H1 = H ∩ Jbase →
    MultiplyLinearWith Qb Eb
      (restrictRelation (section16SpectrumRelation B delta) Jbase) →
    Section16InducedSelection B phi H Y
      (fun h => section16LargeSpectrum B h delta) zeta phiPrime →
    ∀ (P : Box N (k + 1)) (Q : Box N k) (I : ModAP N),
      P.IsProper → IsLastCoordinateBoxProduct P Q I → m ≤ P.width →
      ∃ G : Finset (Point N k), ∃ M : Nat,
          ∃ S : Fin M → Box N (k + 1),
            ∃ T : Fin M → Box N k, ∃ A : Fin M → ModAP N,
              G ⊆ Q.carrier ∧
              (1 - sigma) * Q.carrier.card ≤ G.card ∧
              IsBoxPartition S P ∧ (∀ u, (S u).IsProper) ∧
              (∀ u, IsLastCoordinateBoxProduct (S u) (T u) (A u)) ∧
              (∀ u, W m (Nat.floor (Qb sigma)) (Eb sigma) zeta ≤ (S u).width) ∧
              ∀ u h, h ∈ G → h ∈ H1 → h ∈ (T u).carrier →
                LinearOn ((A u).carrier.filter fun x =>
                  (h, x) ∈ section16InducedDomain B H Y) (phiPrime h)

/-- A width transfers along cell refinements: a cell of width at least `m^c`
inherits the guarantee at width exponent `c * a`. -/
def Section16WidthTransfer (W : Nat → Nat → Real → Real → Real) : Prop :=
  ∀ (m n q : Nat) (a c zeta : Real), 0 ≤ zeta → 0 ≤ a → 0 ≤ c →
    (m : Real) ^ c ≤ n → W m q (c * a) zeta ≤ W n q a zeta

/-- Lemma 16.9 at every scale, for the linearity width `W` and arbitrary
remainder controls `(Qr, Er)`. -/
def AllScaleLemma169WithAt (k : Nat) (W : Nat → Nat → Real → Real → Real) : Prop :=
  ∀ (N m : Nat) [NeZero N] [Fact N.Prime], 1 ≤ k →
    ∀ (theta gamma sigma : Real),
    0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 →
    0 < sigma → sigma ≤ 1 →
    ∀ (Qb Eb Qr Er : Real → Real), 0 ≤ Qb (sigma / 2) → 0 < Eb (sigma / 2) →
      Eb (sigma / 2) ≤ 1 → 0 ≤ Er (sigma / 2) →
    ∀ (B : Finset (Point N (k + 1)))
      (phi : Point N (k + 1) → ZMod N)
      (H Jbase H1 : Finset (Point N k))
      (Y : (h : Point N k) → Finset (Section16CubeElement B h))
      (phiPrime : Point N k → ZMod N → ZMod N) (x0 : Point N k),
    let theta1 := section16ThetaOne theta gamma k
    let delta := section16Delta theta1
    let zeta := section16Zeta theta gamma k
    let B1 := section16GoodDomain B H1 Y x0
    H1 = H ∩ Jbase →
    MultiplyLinearWith Qb Eb
      (restrictRelation (section16SpectrumRelation B delta) Jbase) →
    Section16InducedSelection B phi H Y
      (fun h => section16LargeSpectrum B h delta) zeta phiPrime →
    Section16PhiOneIdentity B1 phi x0 phiPrime →
    MultiplyLinearWith Qr Er (partialGraph B1 (section16PhiRemainder phi x0)) →
    ∀ P : Box N (k + 1), P.IsProper → m ≤ P.width →
      ∃ qGamma : Nat,
        (qGamma : Real) ≤ Qr (sigma / 2) ∧
        Section16LineCover P B1 (section16PhiOne phi x0) sigma
          (W m (Nat.floor (Qb (sigma / 2))) (Er (sigma / 2) * Eb (sigma / 2)) zeta)
          qGamma

/-- Lemma 16.9 at every scale, for the linearity width `W`, arbitrary
remainder controls `(Qr, Er)`, and a remainder cover on any sub-domain
`D ⊆ B₁`. The line cover then covers `φ₁` on `D`. Covers from `PolyCoverAt`
exist only on good sets, so `D` is `B₁` minus a global deletion. -/
def AllScaleLemma169SubdomainAt (k : Nat) (W : Nat → Nat → Real → Real → Real) : Prop :=
  ∀ (N m : Nat) [NeZero N] [Fact N.Prime], 1 ≤ k →
    ∀ (theta gamma sigma : Real),
    0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 →
    0 < sigma → sigma ≤ 1 →
    ∀ (Qb Eb Qr Er : Real → Real), 0 ≤ Qb (sigma / 2) → 0 < Eb (sigma / 2) →
      Eb (sigma / 2) ≤ 1 → 0 ≤ Er (sigma / 2) →
    ∀ (B : Finset (Point N (k + 1)))
      (phi : Point N (k + 1) → ZMod N)
      (H Jbase H1 : Finset (Point N k))
      (Y : (h : Point N k) → Finset (Section16CubeElement B h))
      (phiPrime : Point N k → ZMod N → ZMod N) (x0 : Point N k),
    let theta1 := section16ThetaOne theta gamma k
    let delta := section16Delta theta1
    let zeta := section16Zeta theta gamma k
    let B1 := section16GoodDomain B H1 Y x0
    H1 = H ∩ Jbase →
    MultiplyLinearWith Qb Eb
      (restrictRelation (section16SpectrumRelation B delta) Jbase) →
    Section16InducedSelection B phi H Y
      (fun h => section16LargeSpectrum B h delta) zeta phiPrime →
    Section16PhiOneIdentity B1 phi x0 phiPrime →
    ∀ D : Finset (Point N (k + 1)), D ⊆ B1 →
    MultiplyLinearWith Qr Er (partialGraph D (section16PhiRemainder phi x0)) →
    ∀ P : Box N (k + 1), P.IsProper → m ≤ P.width →
      ∃ qGamma : Nat,
        (qGamma : Real) ≤ Qr (sigma / 2) ∧
        Section16LineCover P D (section16PhiOne phi x0) sigma
          (W m (Nat.floor (Qb (sigma / 2))) (Er (sigma / 2) * Eb (sigma / 2)) zeta)
          qGamma

/-- The sub-domain Lemma 16.9 from the all-scale Lemma 16.6. -/
theorem allScaleLemma169SubdomainAt_of (k : Nat) {W : Nat → Nat → Real → Real → Real}
    (hW : Section16WidthTransfer W)
    (hlemma6 : AllScaleLemma166WidthAt k W) : AllScaleLemma169SubdomainAt k W := by
  unfold AllScaleLemma169SubdomainAt
  intro N m _ _ hk theta gamma sigma ht ht1 hg hg1 hs hs1 Qb Eb Qr Er hQ ha ha1 hEr
    B phi H Jbase H1 Y phiPrime x0
  dsimp only
  intro hH1 hML hselection hidentity D hD hrem P hP hmP
  classical
  let zeta := section16Zeta theta gamma k
  let B1 := section16GoodDomain B H1 Y x0
  have hsHalf : 0 < sigma / 2 := by positivity
  have hsHalf1 : sigma / 2 ≤ 1 := by linarith
  obtain ⟨M, qGamma, F, R, mu, hFsub, hFmass, hRpart, hRproper, hqGamma,
      hRwidth, hmu, hremCover⟩ := hrem (sigma / 2) hsHalf hsHalf1 P hP
  have hlocal (j : Fin M) := hlemma6 N (R j).width hk theta gamma (sigma / 2)
    ht ht1 hg hg1 hsHalf hsHalf1 Qb Eb hQ ha ha1 B phi H Jbase H1 Y phiPrime hH1 hML hselection
    (R j) (boxInit (R j)) ((R j).axis (Fin.last k)) (hRproper j) (boxInit_last_product (R j)) le_rfl
  choose G L S T J hGsub hGmass hSpart hSproper hSproduct hSwidth hSlin using hlocal
  let qDelta := Nat.floor (Qb (sigma / 2))
  have hz : 0 ≤ zeta := (section16Zeta_pos_le_half k ht ht1 hg hg1).1.le
  have hwidth (j : Fin M) (a : Fin (L j)) :
      W m qDelta (Er (sigma / 2) * Eb (sigma / 2)) zeta ≤ (S j a).width := by
    have hcell : (m : Real) ^ (Er (sigma / 2)) ≤ (R j).width :=
      (Real.rpow_le_rpow (Nat.cast_nonneg m) (by exact_mod_cast hmP) hEr).trans (hRwidth j)
    exact (hW m (R j).width qDelta (Eb (sigma / 2)) (Er (sigma / 2)) zeta hz ha.le hEr hcell).trans
      (hSwidth j a)
  let U (j : Fin M) := lastProductSet (G j) ((R j).axis (Fin.last k)).carrier
  have hU (j : Fin M) : U j ⊆ (R j).carrier ∧
      (1 - sigma / 2) * ((R j).carrier.card : Real) ≤ (U j).card := by
    have h := lastProductSet_good_mass (boxInit (R j)).carrier (G j)
      ((R j).axis (Fin.last k)).carrier (sigma / 2) (hGsub j) (hGmass j)
    simpa only [U, (boxInit_last_product (R j)).1, lastProductSet] using h
  let V := Finset.univ.biUnion U
  have hV := IsPartition.good_union hRpart U (sigma / 2) (fun j => (hU j).1) (fun j => (hU j).2)
  let E := F ∩ V
  have hEsub : E ⊆ P.carrier := Finset.Subset.trans Finset.inter_subset_left hFsub
  have hEmass : (1 - sigma) * (P.carrier.card : Real) ≤ E.card := by
    have h := good_intersection_mass P.carrier F V (sigma / 2) (sigma / 2) hFsub hV.1 hFmass hV.2
    convert h using 1; ring
  have hext (j : Fin M) (a : Fin (L j)) (h : Point N k) :
      ∃ ell : ZMod N → ZMod N, LinearOn Finset.univ ell ∧
        (h ∈ G j ∧ h ∈ H1 ∧ h ∈ (T j a).carrier →
          ∀ x ∈ (J j a).carrier.filter (fun x => (h, x) ∈ section16InducedDomain B H Y),
            phiPrime h x = ell x) :=
    conditional_affine_extension _ _ _ (fun hh => hSlin j a h hh.1 hh.2.1 hh.2.2)
  choose ell hell hellEq using hext
  let e := section5NatFlattenEquiv L
  let lines (j : Fin M) (a : Fin (L j)) (h : Point N k) (i : Fin qGamma) (x : ZMod N) :=
    (-1 : ZMod N) ^ k * ell j a h x + mu j i (appendCoordinate h x)
  refine ⟨qGamma, hqGamma, E, ∑ j, L j, boxFlatten L S,
    (fun a => T (e.symm a).1 (e.symm a).2),
    (fun a => J (e.symm a).1 (e.symm a).2),
    (fun a => lines (e.symm a).1 (e.symm a).2), hEsub, hEmass,
    boxFlatten_partition P R L S hRpart hSpart, (fun a => hSproper _ _), ?_, ?_, ?_, ?_⟩
  · intro a
    exact hSproduct _ _
  · intro a
    exact hwidth _ _
  · intro a h i
    exact affine_plus_multilinear_fibres (mu (e.symm a).1) (hmu (e.symm a).1) h
      (ell (e.symm a).1 (e.symm a).2 h) (hell _ _ _) ((-1 : ZMod N) ^ k) i
  · intro a h x hhT hzB hzE hzS
    let j := (e.symm a).1
    let b := (e.symm a).2
    change appendCoordinate h x ∈ (S j b).carrier at hzS
    have hzR : appendCoordinate h x ∈ (R j).carrier := IsPartition.cell_subset (hSpart j) b hzS
    have hzF : appendCoordinate h x ∈ F := (Finset.mem_inter.mp hzE).1
    have hzV : appendCoordinate h x ∈ V := (Finset.mem_inter.mp hzE).2
    have hzU := (IsPartition.good_union_mem_iff hRpart U (fun j => (hU j).1) j hzR).mp hzV
    have hhG : h ∈ G j := by
      have h := (Finset.mem_filter.mp hzU).2.1
      simpa only [section16Init_appendCoordinate] using h
    have hHsub : H1 ⊆ H := by rw [hH1]; exact Finset.inter_subset_left
    have hdomain := section16GoodDomain_fibre_mem B H H1 Y x0 h x hHsub (hD hzB)
    have hxJ : x ∈ (J j b).carrier := by
      have h := ((hSproduct j b).mem_snoc h x).mp (by simpa only [appendCoordinate_eq_snoc] using hzS)
      exact h.2
    have hphi := hellEq j b h ⟨hhG, hdomain.1, hhT⟩ x (Finset.mem_filter.mpr ⟨hxJ, hdomain.2⟩)
    have hgraph : (appendCoordinate h x, section16PhiRemainder phi x0 (appendCoordinate h x)) ∈
        partialGraph D (section16PhiRemainder phi x0) :=
      Finset.mem_image.mpr ⟨appendCoordinate h x, hzB, rfl⟩
    obtain ⟨i, hi⟩ := hremCover j (appendCoordinate h x) hzR hzF _ hgraph
    refine ⟨i, ?_⟩
    have hid := hidentity (appendCoordinate h x) (hD hzB)
    simp only [section16PhiPrimeLift, section16Init_appendCoordinate, section16Last_appendCoordinate] at hid
    change _ = lines j b h i x
    dsimp only [lines]
    rw [hid, hphi, hi]

/-- The remainder-controlled Lemma 16.9 from the all-scale Lemma 16.6. -/
theorem allScaleLemma169WithAt_of (k : Nat) {W : Nat → Nat → Real → Real → Real}
    (hW : Section16WidthTransfer W)
    (hlemma6 : AllScaleLemma166WidthAt k W) : AllScaleLemma169WithAt k W := by
  unfold AllScaleLemma169WithAt
  intro N m _ _ hk theta gamma sigma ht ht1 hg hg1 hs hs1 Qb Eb Qr Er hQ ha ha1 hEr
    B phi H Jbase H1 Y phiPrime x0
  dsimp only
  intro hH1 hML hselection hidentity hrem P hP hmP
  exact allScaleLemma169SubdomainAt_of k hW hlemma6 N m hk theta gamma sigma ht ht1 hg hg1
    hs hs1 Qb Eb Qr Er hQ ha ha1 hEr B phi H Jbase H1 Y phiPrime x0 hH1 hML hselection hidentity
    _ Finset.Subset.rfl hrem P hP hmP

/-- The specialization to Gowers's printed remainder controls
`(multipleQ (θ/r) γ (k+1))^r` and `(multipleC (θ/r) γ (k+1))^r`, in the form
of `AllScalePolynomialLemma169At`. -/
theorem allScaleLemma169WithAt_printed (k : Nat) {W : Nat → Nat → Real → Real → Real}
    (hwith : AllScaleLemma169WithAt k W) :
  ∀ (N m : Nat) [NeZero N] [Fact N.Prime], 1 ≤ k →
    ∀ (theta gamma sigma : Real),
    0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 →
    0 < sigma → sigma ≤ 1 →
    ∀ (Qb Eb : Real → Real), 0 ≤ Qb (sigma / 2) → 0 < Eb (sigma / 2) →
      Eb (sigma / 2) ≤ 1 →
    ∀ (B : Finset (Point N (k + 1)))
      (phi : Point N (k + 1) → ZMod N)
      (H Jbase H1 : Finset (Point N k))
      (Y : (h : Point N k) → Finset (Section16CubeElement B h))
      (phiPrime : Point N k → ZMod N → ZMod N) (x0 : Point N k),
    let theta1 := section16ThetaOne theta gamma k
    let delta := section16Delta theta1
    let zeta := section16Zeta theta gamma k
    let r := section16Lemma9R theta gamma k
    let B1 := section16GoodDomain B H1 Y x0
    H1 = H ∩ Jbase →
    MultiplyLinearWith Qb Eb
      (restrictRelation (section16SpectrumRelation B delta) Jbase) →
    Section16InducedSelection B phi H Y
      (fun h => section16LargeSpectrum B h delta) zeta phiPrime →
    Section16PhiOneIdentity B1 phi x0 phiPrime →
    MultiplyLinearFunction gamma r B1 (section16PhiRemainder phi x0) →
    ∀ P : Box N (k + 1), P.IsProper → m ≤ P.width →
      ∃ qGamma : Nat,
        (qGamma : Real) ≤ section16Lemma9QBound sigma theta gamma k ∧
        Section16LineCover P B1 (section16PhiOne phi x0) sigma
          (W m (Nat.floor (Qb (sigma / 2)))
            (((multipleC (sigma / (2 * r)) gamma (k + 1)) ^ r) * Eb (sigma / 2)) zeta)
          qGamma := by
  intro N m _ _ hk theta gamma sigma ht ht1 hg hg1 hs hs1 Qb Eb hQ ha ha1
    B phi H Jbase H1 Y phiPrime x0
  dsimp only
  intro hH1 hML hselection hidentity hrem P hP hmP
  let r := section16Lemma9R theta gamma k
  have harg (s : Real) : s⁻¹ * (sigma / 2) = sigma / (2 * s) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hc : 0 ≤ multipleC (r⁻¹ * (sigma / 2)) gamma (k + 1) :=
    (even_two.pow_of_ne_zero (by positivity : (2 : Nat) ^ (k + 1 + 8) ≠ 0)).pow_nonneg _
  have hexp : 0 ≤ (multipleC (r⁻¹ * (sigma / 2)) gamma (k + 1)) ^ r := Real.rpow_nonneg hc _
  obtain ⟨qGamma, hq, hcover⟩ := hwith N m hk theta gamma sigma ht ht1 hg hg1 hs hs1 Qb Eb
    (fun s => (multipleQ (r⁻¹ * s) gamma (k + 1)) ^ r)
    (fun s => (multipleC (r⁻¹ * s) gamma (k + 1)) ^ r) hQ ha ha1 hexp
    B phi H Jbase H1 Y phiPrime x0 hH1 hML hselection hidentity hrem P hP hmP
  refine ⟨qGamma, ?_, ?_⟩
  · simpa only [section16Lemma9QBound, harg] using hq
  · simpa only [harg] using hcover

end LeanProofs.GowersSzemeredi
