import GowersSzemeredi.Proofs16FamilyPieceCover

/-! The simultaneous union for abstract pieces, in one common frame.

`Proofs16FamilyLemma6` through `Proofs16FamilyPieceCover` state the family
results for Gowers's data `(B, H, Y, φ′, x₀)`. That data lives in the
shifted frame `(h, x) ↦ (x₀ + h, x)`. Pieces with different `x₀` cannot be
translated back to the original frame together.

The proofs never use the frame. They only use, per member `c`:
* a frequency map `K c` with a common covering relation `Γ`;
* Bohr-linearity of `f c x` on `A c x` for `x ∈ H1 c`;
* a domain `D c` and the identity `φ c = (−1)^k f c + rem c` on it;
* a common relation `Γr` containing every remainder graph.

Here they are restated over these abstract members. A piece produced in
its own frame enters in the original frame with every ingredient
translated by `x₀`: `K(· − x₀)`, `A(· − x₀)`, `f(· − x₀)`, `H1 + x₀`. Its
frequencies are then covered by translated multilinear graphs.
* `AbstractFamilyLemma166At`, `abstractFamilyLemma166At_of`.
* `AbstractFamilyLemma169At`, `abstractFamilyLemma169At_of`.
* `abstract_family_piece_large_box_profile`,
  `abstract_family_piece_cover_with`. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- **Lemma 16.6 for abstract members, at every scale.** -/
def AbstractFamilyLemma166At (k : Nat) (W : Nat → Nat → Real → Real → Real) : Prop :=
  ∀ (N m : Nat) [NeZero N] [Fact N.Prime], 1 ≤ k →
    ∀ (zeta sigma : Real), 0 < zeta → zeta ≤ 1 / 2 → 0 < sigma → sigma ≤ 1 →
    ∀ (Qb Eb : Real → Real), 0 ≤ Qb sigma → 0 < Eb sigma → Eb sigma ≤ 1 →
    ∀ (Gamma : Finset (Point N k × ZMod N)), MultiplyLinearWith Qb Eb Gamma →
    ∀ (ι : Type) (H1 : ι → Finset (Point N k)) (K A : ι → Point N k → Finset (ZMod N))
      (f : ι → Point N k → ZMod N → ZMod N),
    (∀ c, ∀ x ∈ H1 c, ∀ r ∈ K c x, (x, r) ∈ Gamma) →
    (∀ c, ∀ x ∈ H1 c, ∀ v : Nat, 0 < v → ∀ J : ModAP N, J.length ≤ v →
      J.step ∈ bohr (K c x) (zeta / v) → LinearOn (J.carrier ∩ A c x) (f c x)) →
    ∀ (P : Box N (k + 1)) (Q : Box N k) (I : ModAP N),
      P.IsProper → IsLastCoordinateBoxProduct P Q I → m ≤ P.width →
      ∃ G : Finset (Point N k), ∃ M : Nat,
          ∃ S : Fin M → Box N (k + 1),
            ∃ T : Fin M → Box N k, ∃ J : Fin M → ModAP N,
              G ⊆ Q.carrier ∧
              (1 - sigma) * Q.carrier.card ≤ G.card ∧
              IsBoxPartition S P ∧ (∀ u, (S u).IsProper) ∧
              (∀ u, IsLastCoordinateBoxProduct (S u) (T u) (J u)) ∧
              (∀ u, W m (Nat.floor (Qb sigma)) (Eb sigma) zeta ≤ (S u).width) ∧
              ∀ c u x, x ∈ G → x ∈ H1 c → x ∈ (T u).carrier →
                LinearOn ((J u).carrier ∩ A c x) (f c x)

/-- The abstract family Lemma 16.6 from the recurrence profile. -/
theorem abstractFamilyLemma166At_of (k : Nat) {C p : Nat} (hC : 2 ≤ C) (hp : 0 < p)
    (hrec : Section16RecurrenceProfileWith k (familyRecThr k C p) (familyRecExp k p)) :
    AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor C) (familyWidthDivisor k p)) := by
  unfold AbstractFamilyLemma166At
  intro N m _ _ hk zeta sigma hz hzHalf hs hs1 Qb Eb hQ ha ha1 Gamma hML
    ι H1 K A f hfreq hlinear P Q I hP hproduct hmP
  classical
  have hfam := hrec.retiled_family (fun q => familyRecThr_pos (by omega) q)
  let q := Nat.floor (Qb sigma)
  let b := C * (q + 1)
  let E := 2 * (p * (q + 1) ^ (2 * (2 ^ (k + 1))))
  let l := section16PowerWidth (familyWidthPrefactor C) (familyWidthDivisor k p) m q (Eb sigma) zeta
  have hlval : l = (zeta / (4 * (b : Real))) * (m : Real) ^ (Eb sigma / (4 * (E : Real))) := rfl
  by_cases hl : l ≤ 1
  · obtain ⟨M, x, hpart⟩ := box_singleton_partition P
    refine ⟨Q.carrier, M, fun j => pointSingletonBox (x j),
      (fun j => boxInit (pointSingletonBox (x j))),
      (fun j => (pointSingletonBox (x j)).axis (Fin.last k)), Finset.Subset.refl _, ?_, hpart,
      fun j => pointSingletonBox_isProper _,
      (fun j => boxInit_last_product (pointSingletonBox (x j))), ?_, ?_⟩
    · have hcard : (0 : Real) ≤ Q.carrier.card := Nat.cast_nonneg _
      nlinarith
    · intro j
      simpa only [pointSingletonBox_width (by omega : 0 < k + 1), Nat.cast_one] using hl
    · intro c j h _ _ _
      apply LinearOn.of_subset_singleton _ _ ((x j) (Fin.last k))
      intro y hy
      simpa only [pointSingletonBox_axis_carrier] using (Finset.mem_inter.mp hy).1
  · have hlarge : 1 < l := lt_of_not_ge hl
    have hb : 2 ≤ b := hC.trans (Nat.le_mul_of_pos_right C (by omega))
    have hE : 0 < E := by dsimp [E]; positivity
    rw [hlval] at hlarge
    have hm : 1 ≤ m := by
      by_contra hm
      have hm0 : m = 0 := by omega
      have he : 0 < Eb sigma / (4 * (E : Real)) := by positivity
      rw [hm0, Nat.cast_zero, Real.zero_rpow he.ne', mul_zero] at hlarge
      norm_num at hlarge
    obtain ⟨n, hm4, hn, hnscale, hnthreshold, htarget⟩ :=
      section16_rounded_recurrence_scale hm hb hE ha ha1 hz hzHalf hlarge
    have hwidthpos : 0 < P.width := by omega
    have hcanon := hproduct.canonical_factors hwidthpos
    let Q' := boxInit P
    let I' := P.axis (Fin.last k)
    have hQ' : Q'.IsProper := boxInit_isProper P hP
    have hI' : I'.IsProper := hP (Fin.last k)
    have hmQ' : m ≤ Q'.width := hmP.trans (boxInit_width P (by omega))
    have hmI' : m ≤ I'.length := hmP.trans (P.width_le_axis_length (Fin.last k))
    obtain ⟨u, hu⟩ := I'.step_isUnit_of_prime hI' (by omega)
    have hu' : I'.step = (↑u : ZMod N) := hu.symm
    have hstep : I'.step = Q'.commonDiff := P.axis_step (Fin.last k)
    obtain ⟨q', G, bb, Bp, cnt, R, mu, hq', hGsub, hGmass, hBpart, hBproper,
        hBaxes, hBstep, hRpart, hRproper, hRwidth, hmu, hcover⟩ :=
      hML.short_parent_cover sigma hs hs1 hQ ha.le Q' I' hQ' hI' (by omega) hm4 hmQ' hmI'
    have hq'q : q' ≤ q := Nat.le_floor hq'
    have hthreshold : familyRecThr k C p q' ≤ n :=
      (familyRecThr_mono (by omega) hq'q).trans hnthreshold
    let lcell := (zeta / 2) * Real.sqrt ((n : Real) ^ familyRecExp k p q')
    have htarget' : (zeta / (4 * (b : Real))) * (m : Real) ^ (Eb sigma / (4 * (E : Real))) ≤
        lcell := by
      refine htarget.trans ?_
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.sqrt_le_sqrt
      have hn1 : (1 : Real) ≤ n := by exact_mod_cast hn
      have hEq : ((E : Nat) : Real)⁻¹ = familyRecExp k p q := rfl
      rw [hEq]
      exact Real.rpow_le_rpow_of_exponent_le hn1 (familyRecExp_antitone hp hq'q)
    have hlcell : 1 < lcell := hlarge.trans_le htarget'
    let e := section5NatFlattenEquiv cnt
    let R' := boxFlatten cnt R
    have hR'part : IsBoxPartition R' Q' := boxFlatten_partition Q' Bp cnt R hBpart hRpart
    let i : Fin k := ⟨0, by omega⟩
    have hnR (j : Fin (∑ z, cnt z)) : n ≤ (R' j).width := by
      exact_mod_cast hnscale.trans (hRwidth (e.symm j).1 (e.symm j).2)
    have hne (j : Fin (∑ z, cnt z)) : (R' j).carrier.Nonempty := by
      apply Box.carrier_nonempty_of_axis_pos
      intro z
      exact hn.trans_le ((hnR j).trans ((R' j).width_le_axis_length z))
    have hsub (j : Fin (∑ z, cnt z)) :
        ((R' j).axis i).carrier ⊆ ((Bp (e.symm j).1).axis i).carrier :=
      (R' j).axis_carrier_subset_of_carrier_subset (Bp (e.symm j).1) (hne j)
        (IsPartition.cell_subset (hRpart (e.symm j).1) (e.symm j).2) i
    have hBunit (j : Fin (∑ z, cnt z)) :
        ((Bp (e.symm j).1).axis i).step = (↑u : ZMod N) := by
      rw [(Bp _).axis_step, hBstep, ← hstep, hu']
    have hIparallel (j : Fin (∑ z, cnt z)) : I'.step = ((Bp (e.symm j).1).axis i).step := by
      rw [(Bp _).axis_step, hBstep, hstep]
    have hlocal (j : Fin (∑ z, cnt z)) :
        ∃ M : Nat, ∃ S : Fin M → Box N (k + 1), ∃ T : Fin M → Box N k,
          ∃ J : Fin M → ModAP N,
          IsPartition (fun z => (S z).carrier) (lastProductSet (R' j).carrier I'.carrier) ∧
          (∀ z, (S z).IsProper ∧ lcell ≤ (S z).width) ∧
          (∀ z, IsLastCoordinateBoxProduct (S z) (T z) (J z)) ∧
          ∀ c z x, x ∈ (T z).carrier → x ∈ G ∩ H1 c →
            LinearOn ((J z).carrier ∩ A c x) (f c x) := by
      apply hfam q' N n (R' j) ((Bp (e.symm j).1).axis i) I' i u
        (hRproper _ _) hI' (hBunit j) (hIparallel j) (hsub j)
        (hBaxes _ i).2.1 (hBaxes _ i).2.2 (mu (e.symm j).1 (e.symm j).2)
        (hmu _ _) hthreshold (hnR j) ι K (fun c => G ∩ H1 c) A f zeta hz hzHalf
      · intro c x hx hxGH r hr
        exact hcover (e.symm j).1 (e.symm j).2 x hx (Finset.mem_inter.mp hxGH).1 r
          (hfreq c x (Finset.mem_inter.mp hxGH).2 r hr)
      · intro c x hxGH v hv J hJ hd
        exact hlinear c x (Finset.mem_inter.mp hxGH).2 v hv J hJ hd
      · exact hlcell
    choose L S T J hSpart hSproper hSproduct hSlin using hlocal
    let fidx := section5NatFlattenEquiv L
    have hpartQ : IsPartition (fun z => (boxFlatten L S z).carrier)
        (lastProductSet Q'.carrier I'.carrier) :=
      finsetPartition_flatten L (fun j => lastProductSet (R' j).carrier I'.carrier)
        (lastProductSet Q'.carrier I'.carrier) (fun j z => (S j z).carrier)
        (lastProductSet_partition _ _ _ hR'part) hSpart
    refine ⟨G, ∑ j, L j, boxFlatten L S,
      (fun j => T (fidx.symm j).1 (fidx.symm j).2),
      (fun j => J (fidx.symm j).1 (fidx.symm j).2), ?_, ?_, ?_,
      (fun j => (hSproper _ _).1), (fun j => hSproduct _ _), ?_, ?_⟩
    · simpa only [Q', hcanon.1] using hGsub
    · simpa only [Q', hcanon.1] using hGmass
    · change IsPartition (fun j => (boxFlatten L S j).carrier) P.carrier
      simpa only [(boxInit_last_product P).1, lastProductSet, Q', I'] using hpartQ
    · intro j
      have hw := (hSproper (fidx.symm j).1 (fidx.symm j).2).2
      exact (le_of_eq hlval).trans (htarget'.trans hw)
    · intro c j h hhG hhH hhT
      exact hSlin (fidx.symm j).1 c (fidx.symm j).2 h hhT (Finset.mem_inter.mpr ⟨hhG, hhH⟩)

/-- **Lemma 16.9 for abstract members.** -/
def AbstractFamilyLemma169At (k : Nat) (W : Nat → Nat → Real → Real → Real) : Prop :=
  ∀ (N m : Nat) [NeZero N] [Fact N.Prime], 1 ≤ k →
    ∀ (zeta sigma : Real), 0 < zeta → zeta ≤ 1 / 2 → 0 < sigma → sigma ≤ 1 →
    ∀ (Qb Eb Qr Er : Real → Real), 0 ≤ Qb (sigma / 2) → 0 < Eb (sigma / 2) →
      Eb (sigma / 2) ≤ 1 → 0 ≤ Er (sigma / 2) →
    ∀ (Gamma : Finset (Point N k × ZMod N)), MultiplyLinearWith Qb Eb Gamma →
    ∀ (Gr : Finset (Point N (k + 1) × ZMod N)), MultiplyLinearWith Qr Er Gr →
    ∀ (ι : Type) (H1 : ι → Finset (Point N k)) (K A : ι → Point N k → Finset (ZMod N))
      (f : ι → Point N k → ZMod N → ZMod N) (D : ι → Finset (Point N (k + 1)))
      (phi rem : ι → Point N (k + 1) → ZMod N),
    (∀ c, ∀ x ∈ H1 c, ∀ r ∈ K c x, (x, r) ∈ Gamma) →
    (∀ c, ∀ x ∈ H1 c, ∀ v : Nat, 0 < v → ∀ J : ModAP N, J.length ≤ v →
      J.step ∈ bohr (K c x) (zeta / v) → LinearOn (J.carrier ∩ A c x) (f c x)) →
    (∀ c, ∀ z ∈ D c, section16Init z ∈ H1 c ∧ section16Last z ∈ A c (section16Init z)) →
    (∀ c, ∀ z ∈ D c,
      phi c z = (-1 : ZMod N) ^ k * f c (section16Init z) (section16Last z) + rem c z) →
    (∀ c, ∀ z ∈ D c, (z, rem c z) ∈ Gr) →
    ∀ P : Box N (k + 1), P.IsProper → m ≤ P.width →
      ∃ qGamma : Nat,
        (qGamma : Real) ≤ Qr (sigma / 2) ∧
        Section16LineCoverFamily P D phi sigma
          (W m (Nat.floor (Qb (sigma / 2))) (Er (sigma / 2) * Eb (sigma / 2)) zeta) qGamma

/-- The abstract family Lemma 16.9 from the abstract family Lemma 16.6. -/
theorem abstractFamilyLemma169At_of (k : Nat) {W : Nat → Nat → Real → Real → Real}
    (hW : Section16WidthTransfer W)
    (hlemma6 : AbstractFamilyLemma166At k W) : AbstractFamilyLemma169At k W := by
  unfold AbstractFamilyLemma169At
  intro N m _ _ hk zeta sigma hz hzHalf hs hs1 Qb Eb Qr Er hQ ha ha1 hEr
    Gamma hML Gr hrem ι H1 K A f D phi rem hfreq hlinear hdom hid hGr P hP hmP
  classical
  have hsHalf : 0 < sigma / 2 := by positivity
  have hsHalf1 : sigma / 2 ≤ 1 := by linarith
  obtain ⟨M, qGamma, F, R, mu, hFsub, hFmass, hRpart, hRproper, hqGamma,
      hRwidth, hmu, hremCover⟩ := hrem (sigma / 2) hsHalf hsHalf1 P hP
  have hlocal (j : Fin M) := hlemma6 N (R j).width hk zeta (sigma / 2) hz hzHalf
    hsHalf hsHalf1 Qb Eb hQ ha ha1 Gamma hML ι H1 K A f hfreq hlinear
    (R j) (boxInit (R j)) ((R j).axis (Fin.last k)) (hRproper j) (boxInit_last_product (R j)) le_rfl
  choose G L S T J hGsub hGmass hSpart hSproper hSproduct hSwidth hSlin using hlocal
  let qDelta := Nat.floor (Qb (sigma / 2))
  have hwidth (j : Fin M) (a : Fin (L j)) :
      W m qDelta (Er (sigma / 2) * Eb (sigma / 2)) zeta ≤ (S j a).width := by
    have hcell : (m : Real) ^ (Er (sigma / 2)) ≤ (R j).width :=
      (Real.rpow_le_rpow (Nat.cast_nonneg m) (by exact_mod_cast hmP) hEr).trans (hRwidth j)
    exact (hW m (R j).width qDelta (Eb (sigma / 2)) (Er (sigma / 2)) zeta hz.le ha.le hEr
      hcell).trans (hSwidth j a)
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
  have hext (c : ι) (j : Fin M) (a : Fin (L j)) (h : Point N k) :
      ∃ ell : ZMod N → ZMod N, LinearOn Finset.univ ell ∧
        (h ∈ G j ∧ h ∈ H1 c ∧ h ∈ (T j a).carrier →
          ∀ x ∈ (J j a).carrier ∩ A c h, f c h x = ell x) :=
    conditional_affine_extension _ _ _ (fun hh => hSlin j c a h hh.1 hh.2.1 hh.2.2)
  choose ell hell hellEq using hext
  let e := section5NatFlattenEquiv L
  let lines (c : ι) (j : Fin M) (a : Fin (L j)) (h : Point N k) (i : Fin qGamma) (x : ZMod N) :=
    (-1 : ZMod N) ^ k * ell c j a h x + mu j i (appendCoordinate h x)
  refine ⟨qGamma, hqGamma, E, ∑ j, L j, boxFlatten L S,
    (fun a => T (e.symm a).1 (e.symm a).2),
    (fun a => J (e.symm a).1 (e.symm a).2),
    (fun c a => lines c (e.symm a).1 (e.symm a).2), hEsub, hEmass,
    boxFlatten_partition P R L S hRpart hSpart, (fun a => hSproper _ _), ?_, ?_, ?_, ?_⟩
  · intro a
    exact hSproduct _ _
  · intro a
    exact hwidth _ _
  · intro c a h i
    exact affine_plus_multilinear_fibres (mu (e.symm a).1) (hmu (e.symm a).1) h
      (ell c (e.symm a).1 (e.symm a).2 h) (hell _ _ _ _) ((-1 : ZMod N) ^ k) i
  · intro c a h x hhT hzD hzE hzS
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
    have hdomain := hdom c _ hzD
    simp only [section16Init_appendCoordinate, section16Last_appendCoordinate] at hdomain
    have hxJ : x ∈ (J j b).carrier := by
      have h := ((hSproduct j b).mem_snoc h x).mp (by simpa only [appendCoordinate_eq_snoc] using hzS)
      exact h.2
    have hphi := hellEq c j b h ⟨hhG, hdomain.1, hhT⟩ x (Finset.mem_inter.mpr ⟨hxJ, hdomain.2⟩)
    obtain ⟨i, hi⟩ := hremCover j (appendCoordinate h x) hzR hzF _ (hGr c _ hzD)
    refine ⟨i, ?_⟩
    have hidz := hid c _ hzD
    simp only [section16Init_appendCoordinate, section16Last_appendCoordinate] at hidz
    change _ = lines c j b h i x
    dsimp only [lines]
    rw [hidz, hphi, hi]


/-- **The large-box profile of a family of abstract pieces.** -/
theorem abstract_family_piece_large_box_profile {k : Nat} (hk : 1 ≤ k)
    {A Bq : Nat → Real} (hA : ∀ q, 0 < A q) (hB : ∀ q, 0 < Bq q)
    (hlemma6 : AbstractFamilyLemma166At k (section16PowerWidth A Bq))
    {N : Nat} [NeZero N] [Fact N.Prime] {zeta : Real} (hz : 0 < zeta) (hzHalf : zeta ≤ 1 / 2)
    {Qb Eb Qr Er : Real → Real}
    (hQb : ∀ s, 0 < s → s ≤ 1 → 0 ≤ Qb s ∧ 0 < Eb s ∧ Eb s ≤ 1)
    (hEr : ∀ s, 0 < s → s ≤ 1 → 0 < Er s)
    {Gamma : Finset (Point N k × ZMod N)} (hML : MultiplyLinearWith Qb Eb Gamma)
    {Gr : Finset (Point N (k + 1) × ZMod N)} (hrem : MultiplyLinearWith Qr Er Gr)
    {ι : Type} [Fintype ι] {H1 : ι → Finset (Point N k)} {K Adom : ι → Point N k → Finset (ZMod N)}
    {f : ι → Point N k → ZMod N → ZMod N} {D : ι → Finset (Point N (k + 1))}
    {phi rem : ι → Point N (k + 1) → ZMod N}
    (hfreq : ∀ c, ∀ x ∈ H1 c, ∀ r ∈ K c x, (x, r) ∈ Gamma)
    (hlinear : ∀ c, ∀ x ∈ H1 c, ∀ v : Nat, 0 < v → ∀ J : ModAP N, J.length ≤ v →
      J.step ∈ bohr (K c x) (zeta / v) → LinearOn (J.carrier ∩ Adom c x) (f c x))
    (hdom : ∀ c, ∀ z ∈ D c, section16Init z ∈ H1 c ∧ section16Last z ∈ Adom c (section16Init z))
    (hid : ∀ c, ∀ z ∈ D c,
      phi c z = (-1 : ZMod N) ^ k * f c (section16Init z) (section16Last z) + rem c z)
    (hGr : ∀ c, ∀ z ∈ D c, (z, rem c z) ∈ Gr)
    {Pb Es : Nat → Real → Real}
    (Gs : (r : Nat) → (ι → Fin r → ZMod N) → Finset (Point N k × ZMod N))
    (hslice : ∀ r sample, MultiplyLinearWith (Pb r) (Es r) (Gs r sample))
    (hGs : ∀ r sample c h i, appendCoordinate h (sample c i) ∈ D c →
      (h, phi c (appendCoordinate h (sample c i))) ∈ Gs r sample)
    (hranges : Section16SliceProviderRanges Pb Es)
    (hPb : ∀ ε, Monotone (fun r => Pb r ε)) (hEs : ∀ ε, 0 < ε → Antitone (fun r => Es r ε)) :
    ∀ rho : Real, 0 < rho → rho ≤ 1 →
      LargeBoxMultilinearCover
        (Finset.univ.biUnion fun c => partialGraph (D c) (phi c)) rho
        (famPieceGraphBound Qr Pb (Fintype.card ι) rho)
        (pieceLineExponent Bq Qb Eb Er rho * famPieceSliceExponent Qr Es (Fintype.card ι) rho / 4)
        (section16RoundedPowerThreshold (pieceWidthScale A Qb zeta rho)
          (pieceLineExponent Bq Qb Eb Er rho) (famPieceSliceExponent Qr Es (Fintype.card ι) rho)) := by
  classical
  intro rho hrho hrho1 P hP hlarge
  let sigma := rho / 4
  have hs : 0 < sigma := by dsimp [sigma]; positivity
  have hs1 : sigma ≤ 1 := by dsimp [sigma]; linarith
  have hhalf : sigma / 2 = rho / 8 := by dsimp [sigma]; ring
  have h8 : 0 < rho / 8 := by positivity
  have h81 : rho / 8 ≤ 1 := by linarith
  obtain ⟨hQ, ha, ha1⟩ := hQb (rho / 8) h8 h81
  have hEr8 := hEr (rho / 8) h8 h81
  have hsub := abstractFamilyLemma169At_of k (section16PowerWidth_transfer hA hB) hlemma6
  obtain ⟨qGamma, hqGamma, hcover⟩ := hsub N P.width hk zeta sigma hz hzHalf hs hs1
    Qb Eb Qr Er (by rw [hhalf]; exact hQ) (by rw [hhalf]; exact ha) (by rw [hhalf]; exact ha1)
    (by rw [hhalf]; exact hEr8.le) Gamma hML Gr hrem ι H1 K Adom f D phi rem
    hfreq hlinear hdom hid hGr P hP le_rfl
  rw [hhalf] at hcover hqGamma
  let l := section16PowerWidth A Bq P.width ⌊Qb (rho / 8)⌋₊ (Er (rho / 8) * Eb (rho / 8)) zeta
  have hl : 0 ≤ l := by
    have := hA ⌊Qb (rho / 8)⌋₊
    dsimp only [l, section16PowerWidth]
    positivity
  obtain ⟨n, Hc, L, Q, mu, hn, hH, hmass, hpart, hproper, hw, hmu, hcov⟩ :=
    hcover.global_affine_lift_rounded_family Gs hslice hGs hranges (by omega) hl
      sigma sigma hs hs1 hs hs1
  set r := ⌈6 * (max 1 qGamma : Real) * ((max 1 (Fintype.card ι) : Nat) : Real) / sigma⌉₊
    with hr
  set S := famPieceSamples Qr (Fintype.card ι) rho with hS
  have hrS : r ≤ S := by
    rw [hr, hS, famPieceSamples]
    apply Nat.ceil_mono
    apply div_le_div_of_nonneg_right _ hs.le
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact max_le_max le_rfl hqGamma
  have hSpos : 0 < S := famPieceSamples_pos hrho
  obtain ⟨hPbS, hEsS, hEsS1⟩ := hranges S sigma hSpos hs hs1
  have hPbr : Pb r sigma ≤ Pb S sigma := hPb sigma hrS
  have hEsr : Es S sigma ≤ Es r sigma := hEs sigma hs hrS
  have hrpos : 0 < r := by
    rw [hr]
    apply Nat.ceil_pos.mpr
    have h1 : (0 : Real) < max 1 (qGamma : Real) := lt_of_lt_of_le one_pos (le_max_left _ _)
    have h2 : (0 : Real) < ((max 1 (Fintype.card ι) : Nat) : Real) := by
      have : 0 < max 1 (Fintype.card ι) := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
      exact_mod_cast this
    positivity
  have hPbr1 := (hranges r sigma hrpos hs hs1).1
  have he : 0 < pieceLineExponent Bq Qb Eb Er rho := by
    have := hB ⌊Qb (rho / 8)⌋₊
    unfold pieceLineExponent
    positivity
  have hzA : 0 < pieceWidthScale A Qb zeta rho := by
    have := hA ⌊Qb (rho / 8)⌋₊
    unfold pieceWidthScale
    positivity
  have hlpow : pieceWidthScale A Qb zeta rho * (P.width : Real) ^ pieceLineExponent Bq Qb Eb Er rho
      ≤ l := le_of_eq rfl
  obtain ⟨hbase, hpow⟩ := section16_rounded_power_width hzA he hEsS hlpow hlarge
  refine ⟨L, n, Hc, Q, mu, hH, ?_, hpart, hproper, ?_, ?_, hmu, ?_⟩
  · have hm : 1 - sigma - 2 * sigma - sigma = 1 - rho := by dsimp [sigma]; ring
    simpa only [hm] using hmass
  · refine hn.trans ?_
    unfold famPieceGraphBound
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    refine max_le_max hPbr ?_
    have hch : ((r.choose 2 : Nat) : Real) ≤ ((S.choose 2 : Nat) : Real) := by
      exact_mod_cast Nat.choose_le_choose 2 hrS
    have h0 : (0 : Real) ≤ Pb r sigma := zero_le_one.trans hPbr1
    calc ((r.choose 2 : Nat) : Real) * Pb r sigma * Pb r sigma
        ≤ ((S.choose 2 : Nat) : Real) * Pb S sigma * Pb S sigma := by
          apply mul_le_mul (mul_le_mul hch hPbr h0 (Nat.cast_nonneg _)) hPbr h0
          exact mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans hPbS)
      _ = _ := rfl
  · intro j
    refine hpow.trans (le_trans ?_ (hw j))
    apply div_le_div_of_nonneg_right _ (by norm_num)
    apply Real.sqrt_le_sqrt
    exact Real.rpow_le_rpow_of_exponent_le hbase hEsr
  · intro j x hx hh y hxy
    obtain ⟨c, -, hc⟩ := Finset.mem_biUnion.mp hxy
    obtain ⟨z, hz, heq⟩ := Finset.mem_image.mp hc
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    exact hcov c j z hx hz hh

/-- **The simultaneous union of a family of abstract pieces, at every scale.** -/
theorem abstract_family_piece_cover_with {k : Nat} (hk : 1 ≤ k)
    {A Bq : Nat → Real} (hA : ∀ q, 0 < A q) (hB : ∀ q, 0 < Bq q)
    (hlemma6 : AbstractFamilyLemma166At k (section16PowerWidth A Bq))
    {N : Nat} [NeZero N] [Fact N.Prime] {zeta : Real} (hz : 0 < zeta) (hzHalf : zeta ≤ 1 / 2)
    {Qb Eb Qr Er : Real → Real}
    (hQb : ∀ s, 0 < s → s ≤ 1 → 0 ≤ Qb s ∧ 0 < Eb s ∧ Eb s ≤ 1)
    (hEr : ∀ s, 0 < s → s ≤ 1 → 0 < Er s)
    {Gamma : Finset (Point N k × ZMod N)} (hML : MultiplyLinearWith Qb Eb Gamma)
    {Gr : Finset (Point N (k + 1) × ZMod N)} (hrem : MultiplyLinearWith Qr Er Gr)
    {ι : Type} [Fintype ι] {H1 : ι → Finset (Point N k)} {K Adom : ι → Point N k → Finset (ZMod N)}
    {f : ι → Point N k → ZMod N → ZMod N} {D : ι → Finset (Point N (k + 1))}
    {phi rem : ι → Point N (k + 1) → ZMod N}
    (hfreq : ∀ c, ∀ x ∈ H1 c, ∀ r ∈ K c x, (x, r) ∈ Gamma)
    (hlinear : ∀ c, ∀ x ∈ H1 c, ∀ v : Nat, 0 < v → ∀ J : ModAP N, J.length ≤ v →
      J.step ∈ bohr (K c x) (zeta / v) → LinearOn (J.carrier ∩ Adom c x) (f c x))
    (hdom : ∀ c, ∀ z ∈ D c, section16Init z ∈ H1 c ∧ section16Last z ∈ Adom c (section16Init z))
    (hid : ∀ c, ∀ z ∈ D c,
      phi c z = (-1 : ZMod N) ^ k * f c (section16Init z) (section16Last z) + rem c z)
    (hGr : ∀ c, ∀ z ∈ D c, (z, rem c z) ∈ Gr)
    {Pb Es : Nat → Real → Real}
    (Gs : (r : Nat) → (ι → Fin r → ZMod N) → Finset (Point N k × ZMod N))
    (hslice : ∀ r sample, MultiplyLinearWith (Pb r) (Es r) (Gs r sample))
    (hGs : ∀ r sample c h i, appendCoordinate h (sample c i) ∈ D c →
      (h, phi c (appendCoordinate h (sample c i))) ∈ Gs r sample)
    (hranges : Section16SliceProviderRanges Pb Es)
    (hPb : ∀ ε, Monotone (fun r => Pb r ε)) (hEs : ∀ ε, 0 < ε → Antitone (fun r => Es r ε)) :
    MultiplyLinearWith
      (fun rho => max (famPieceGraphBound Qr Pb (Fintype.card ι) rho)
        ((3 ^ (k + 1) * Fintype.card ι : Nat) : Real))
      (fun rho => section16CappedWidthExponent
        (pieceLineExponent Bq Qb Eb Er rho * famPieceSliceExponent Qr Es (Fintype.card ι) rho / 4)
        (section16RoundedPowerThreshold (pieceWidthScale A Qb zeta rho)
          (pieceLineExponent Bq Qb Eb Er rho) (famPieceSliceExponent Qr Es (Fintype.card ι) rho)))
      (Finset.univ.biUnion fun c => partialGraph (D c) (phi c)) := by
  have hpos (rho : Real) (hrho : 0 < rho) (hrho1 : rho ≤ 1) :
      0 < pieceLineExponent Bq Qb Eb Er rho * famPieceSliceExponent Qr Es (Fintype.card ι) rho / 4 := by
    have h8 : 0 < rho / 8 := by positivity
    have h81 : rho / 8 ≤ 1 := by linarith
    have hEb := (hQb (rho / 8) h8 h81).2.1
    have hEr8 := hEr (rho / 8) h8 h81
    have hBq := hB ⌊Qb (rho / 8)⌋₊
    have hEs' := (hranges (famPieceSamples Qr (Fintype.card ι) rho) (rho / 4)
      (famPieceSamples_pos hrho) (by positivity) (by linarith)).2.1
    unfold pieceLineExponent famPieceSliceExponent
    positivity
  exact multiplyLinearWith_of_large_box_covers (by omega : 0 < k + 1) (Fintype.card ι)
    (card_biUnion_partialGraph_fiber_le D phi)
    (fun rho => famPieceGraphBound Qr Pb (Fintype.card ι) rho)
    (fun rho => pieceLineExponent Bq Qb Eb Er rho * famPieceSliceExponent Qr Es (Fintype.card ι) rho / 4)
    (fun rho => section16RoundedPowerThreshold
      (pieceWidthScale A Qb zeta rho)
      (pieceLineExponent Bq Qb Eb Er rho) (famPieceSliceExponent Qr Es (Fintype.card ι) rho)) hpos
    (abstract_family_piece_large_box_profile hk hA hB hlemma6 hz hzHalf hQb hEr hML hrem
      hfreq hlinear hdom hid hGr Gs hslice hGs hranges hPb hEs)

end LeanProofs.GowersSzemeredi
