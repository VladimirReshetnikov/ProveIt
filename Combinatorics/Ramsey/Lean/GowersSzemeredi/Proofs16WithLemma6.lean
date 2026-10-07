import GowersSzemeredi.Proofs16Lemma6
import GowersSzemeredi.Proofs16PolyBaseCase

/-! Lemma 16.6 with arbitrary control functions for the spectrum.

The proof of Lemma 16.6 uses the multiple multilinearity of the spectrum only
through its cover, the actual graph count `q` of that cover, and the
positivity of its width exponent. The width it produces depends on `q`
through the Lemma 16.1 exponent `K^(-2^(k+1)*q)`. With the source's control
functions `q` is only bounded by `q(sigma/t,delta,k)^t`, which grows with
`1/sigma`; with `MultiplyLinearWith` a loss-independent count can be
supplied (for instance by `section16_freiman_family_poly_cover`).

Everything here mirrors `Proofs16LocalizedCover`, `Proofs16ProductAssembly`
and `Proofs16Lemma6` with `(Qb sigma, Eb sigma)` in place of
`(q(t⁻¹ sigma,delta,k)^t, c(t⁻¹ sigma,delta,k)^t)`. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem MultiplyLinearWith.on_partition {N k J : Nat} [NeZero N]
    {Qb Eb : Real → Real} {Gamma : Finset (Point N k × ZMod N)}
    (hML : MultiplyLinearWith Qb Eb Gamma) (sigma : Real)
    (hs : 0 < sigma) (hs1 : sigma ≤ 1) (hQ : 0 ≤ Qb sigma) (P : Box N k)
    (B : Fin J → Box N k) (hBpart : IsBoxPartition B P) (hBproper : ∀ j, (B j).IsProper) :
    ∃ q : Nat, ∃ G : Finset (Point N k), ∃ M : Fin J → Nat,
      ∃ R : (j : Fin J) → Fin (M j) → Box N k,
      ∃ mu : (j : Fin J) → Fin (M j) → Fin q → Point N k → ZMod N,
      (q : Real) ≤ Qb sigma ∧
      G ⊆ P.carrier ∧ (1 - sigma) * (P.carrier.card : Real) ≤ G.card ∧
      (∀ j, IsBoxPartition (R j) (B j)) ∧
      (∀ j a, (R j a).IsProper) ∧
      (∀ j a, ((B j).width : Real) ^ (Eb sigma) ≤ (R j a).width) ∧
      (∀ j a i, IsMultilinear (mu j a i)) ∧
      ∀ j a x, x ∈ (R j a).carrier → x ∈ G → ∀ y,
        (x, y) ∈ Gamma → ∃ i, y = mu j a i x := by
  classical
  choose M p H R nu hHsub hHmass hRpart hRproper hp hRwidth hnu hcover using
    fun j => hML sigma hs hs1 (B j) (hBproper j)
  let q := Nat.floor (Qb sigma)
  have hpq (j : Fin J) : p j ≤ q := Nat.le_floor (hp j)
  let G := Finset.univ.biUnion H
  have hG := IsPartition.good_union hBpart H sigma hHsub hHmass
  refine ⟨q, G, M, R, fun j a => padMultilinearFamily (nu j a) q,
    Nat.floor_le hQ, hG.1, hG.2, hRpart, hRproper, hRwidth, ?_, ?_⟩
  · intro j a i
    exact padMultilinearFamily_isMultilinear (nu j a) (hnu j a) i
  · intro j a x hx hxG y hxy
    have hxB := IsPartition.cell_subset (hRpart j) a hx
    have hxH := (IsPartition.good_union_mem_iff hBpart H hHsub j hxB).mp hxG
    exact padMultilinearFamily_covers (nu j a) (hpq j) x y (hcover j a x hx hxH y hxy)

theorem MultiplyLinearWith.short_parent_cover {N k m : Nat} [NeZero N]
    {Qb Eb : Real → Real} {Gamma : Finset (Point N k × ZMod N)}
    (hML : MultiplyLinearWith Qb Eb Gamma) (sigma : Real)
    (hs : 0 < sigma) (hs1 : sigma ≤ 1) (hQ : 0 ≤ Qb sigma) (hE : 0 ≤ Eb sigma)
    (P : Box N k) (I : ModAP N) (hP : P.IsProper) (hI : I.IsProper)
    (hk : 0 < k) (hm : 4 ≤ m) (hmP : m ≤ P.width) (hmI : m ≤ I.length) :
    ∃ q : Nat, ∃ G : Finset (Point N k), ∃ J : Nat, ∃ B : Fin J → Box N k,
      ∃ M : Fin J → Nat, ∃ R : (j : Fin J) → Fin (M j) → Box N k,
      ∃ mu : (j : Fin J) → Fin (M j) → Fin q → Point N k → ZMod N,
      (q : Real) ≤ Qb sigma ∧
      G ⊆ P.carrier ∧ (1 - sigma) * (P.carrier.card : Real) ≤ G.card ∧
      IsBoxPartition B P ∧ (∀ j, (B j).IsProper) ∧
      (∀ j i, 0 < ((B j).axis i).length ∧
        2 * ((B j).axis i).length ≤ N ∧ ((B j).axis i).length ≤ I.length) ∧
      (∀ j, (B j).commonDiff = P.commonDiff) ∧
      (∀ j, IsBoxPartition (R j) (B j)) ∧ (∀ j a, (R j a).IsProper) ∧
      (∀ j a, ((m : Real) / 8) ^ (Eb sigma) ≤ (R j a).width) ∧
      (∀ j a i, IsMultilinear (mu j a i)) ∧
      ∀ j a x, x ∈ (R j a).carrier → x ∈ G → ∀ y,
        (x, y) ∈ Gamma → ∃ i, y = mu j a i x := by
  obtain ⟨J, B, hBpart, hBproper, hBaxes, hBstep⟩ :=
    P.short_parent_partition I hP hI hk hm hmP hmI
  obtain ⟨q, G, M, R, mu, hq, hGsub, hGmass, hRpart, hRproper, hRwidth, hmu, hcover⟩ :=
    hML.on_partition sigma hs hs1 hQ P B hBpart (fun j => (hBproper j).1)
  refine ⟨q, G, J, B, M, R, mu, hq, hGsub, hGmass, hBpart,
    (fun j => (hBproper j).1), hBaxes, hBstep, hRpart, hRproper, ?_, hmu, hcover⟩
  intro j a
  exact (Real.rpow_le_rpow (by positivity) (hBproper j).2 hE).trans (hRwidth j a)

theorem MultiplyLinearWith.product_linearity_large_m {N k m : Nat} [NeZero N]
    {Qb Eb : Real → Real} {Gamma : Finset (Point N k × ZMod N)}
    (hML : MultiplyLinearWith Qb Eb Gamma) (sigma theta gamma : Real)
    (hs : 0 < sigma) (hs1 : sigma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hQ : 0 ≤ Qb sigma) (ha : 0 < Eb sigma) (ha1 : Eb sigma ≤ 1)
    (P : Box N k) (I : ModAP N) (u : (ZMod N)ˣ)
    (hP : P.IsProper) (hI : I.IsProper) (hstep : I.step = P.commonDiff)
    (hu : I.step = (↑u : ZMod N)) (hk : 1 ≤ k)
    (hm : 4 ≤ m) (hmP : m ≤ P.width) (hmI : m ≤ I.length)
    (H : Finset (Point N k)) (K : Point N k → Finset (ZMod N))
    (A : Point N k → Finset (ZMod N)) (f : Point N k → ZMod N → ZMod N)
    (hK : ∀ x ∈ H, ∀ r ∈ K x, (x, r) ∈ Gamma)
    (hlinear : ∀ x ∈ H, ∀ v : Nat, 0 < v → ∀ J : ModAP N, J.length ≤ v →
      J.step ∈ bohr (K x) (section16Zeta theta gamma k / v) →
      LinearOn (J.carrier ∩ A x) (f x)) :
    ∃ q : Nat, ∃ G : Finset (Point N k), ∃ M : Nat,
      ∃ S : Fin M → Box N (k + 1), ∃ T : Fin M → Box N k, ∃ J : Fin M → ModAP N,
      (q : Real) ≤ Qb sigma ∧
      G ⊆ P.carrier ∧ (1 - sigma) * (P.carrier.card : Real) ≤ G.card ∧
      IsPartition (fun j => (S j).carrier) (lastProductSet P.carrier I.carrier) ∧
      (∀ j, (S j).IsProper ∧ (section16Zeta theta gamma k / 2) *
        Real.sqrt ((m : Real) ^ (Eb sigma * section16RecurrenceExponent k q)) ≤ (S j).width) ∧
      (∀ j, IsLastCoordinateBoxProduct (S j) (T j) (J j)) ∧
      ∀ j x, x ∈ G → x ∈ H → x ∈ (T j).carrier →
        LinearOn ((J j).carrier ∩ A x) (f x) := by
  classical
  obtain ⟨q, G, b, B, n, R, mu, hq, hGsub, hGmass, hBpart, hBproper,
      hBaxes, hBstep, hRpart, hRproper, hRwidth, hmu, hcover⟩ :=
    hML.short_parent_cover sigma hs hs1 hQ ha.le P I hP hI (by omega) hm hmP hmI
  let a := Eb sigma
  let l := (section16Zeta theta gamma k / 2) *
    Real.sqrt ((m : Real) ^ (a * section16RecurrenceExponent k q))
  by_cases hl : l ≤ 1
  · obtain ⟨M, S, hpart, hproper, hwidth, hlin⟩ :=
      section16_local_linearity_singletons (boxAppend P I hstep) l hl A f
    refine ⟨q, G, M, S, fun j => boxInit (S j), fun j => (S j).axis (Fin.last k),
      hq, hGsub, hGmass, ?_, fun j => ⟨hproper j, hwidth j⟩,
      fun j => boxInit_last_product (S j), ?_⟩
    · change IsPartition (fun j => (S j).carrier) _ at hpart ⊢
      simpa only [(boxAppend_product P I hstep).1, lastProductSet] using hpart
    · intro j x _ _ _
      simpa only [Finset.filter_mem_eq_inter] using hlin j x
  · have hlarge : 1 < l := lt_of_not_ge hl
    obtain ⟨_, hp, hthreshold, v, hv, hvwidth, hvscale, hvbudget⟩ :=
      section16_localized_parameters hk (by omega : 1 ≤ m) ht ht1 hg hg1 ha ha1 hlarge
    let p := Nat.floor (((m : Real) / 8) ^ a)
    let e := section5NatFlattenEquiv n
    let R' := boxFlatten n R
    have hR'part : IsBoxPartition R' P := boxFlatten_partition P B n R hBpart hRpart
    let i : Fin k := ⟨0, by omega⟩
    have hpR (j : Fin (∑ z, n z)) : p ≤ (R' j).width := by
      have hfloor : (p : Real) ≤ ((m : Real) / 8) ^ a := Nat.floor_le (by positivity)
      have h := hfloor.trans (hRwidth (e.symm j).1 (e.symm j).2)
      exact_mod_cast h
    have hne (j : Fin (∑ z, n z)) : (R' j).carrier.Nonempty := by
      apply Box.carrier_nonempty_of_axis_pos
      intro z
      exact hp.trans_le ((hpR j).trans ((R' j).width_le_axis_length z))
    have hsub (j : Fin (∑ z, n z)) :
        ((R' j).axis i).carrier ⊆ ((B (e.symm j).1).axis i).carrier :=
      (R' j).axis_carrier_subset_of_carrier_subset (B (e.symm j).1) (hne j)
        (IsPartition.cell_subset (hRpart (e.symm j).1) (e.symm j).2) i
    have hBunit (j : Fin (∑ z, n z)) : ((B (e.symm j).1).axis i).step = (↑u : ZMod N) := by
      rw [(B _).axis_step, hBstep, ← hstep, hu]
    have hIparallel (j : Fin (∑ z, n z)) : I.step = ((B (e.symm j).1).axis i).step := by
      rw [(B _).axis_step, hBstep, hstep]
    have hlocal (j : Fin (∑ z, n z)) :
        ∃ M : Nat, ∃ S : Fin M → Box N (k + 1), ∃ T : Fin M → Box N k,
          ∃ J : Fin M → ModAP N,
          IsPartition (fun z => (S z).carrier) (lastProductSet (R' j).carrier I.carrier) ∧
          (∀ z, (S z).IsProper ∧ v - 1 ≤ (S z).width) ∧
          (∀ z, IsLastCoordinateBoxProduct (S z) (T z) (J z)) ∧
          ∀ z x, x ∈ (T z).carrier → x ∈ G ∩ H → LinearOn ((J z).carrier ∩ A x) (f x) := by
      apply proper_retiled_product_linearity (R' j) ((B (e.symm j).1).axis i) I i u
        (hRproper _ _) hI (hBunit j) (hIparallel j) (hsub j)
        (hBaxes _ i).2.1 (hBaxes _ i).2.2 (mu (e.symm j).1 (e.symm j).2)
        (hmu _ _) hthreshold (hpR j) hv hvscale K (section16Zeta theta gamma k)
        (G ∩ H) A f ?_ ?_ hvbudget
      · intro x hx hxGH r hr
        exact hcover (e.symm j).1 (e.symm j).2 x hx (Finset.mem_inter.mp hxGH).1 r
          (hK x (Finset.mem_inter.mp hxGH).2 r hr)
      · intro x hxGH J hJ hd
        exact hlinear x (Finset.mem_inter.mp hxGH).2 v (by omega) J hJ hd
    choose L S T J hSpart hSproper hSproduct hSlin using hlocal
    let fidx := section5NatFlattenEquiv L
    refine ⟨q, G, ∑ j, L j, boxFlatten L S,
      (fun j => T (fidx.symm j).1 (fidx.symm j).2),
      (fun j => J (fidx.symm j).1 (fidx.symm j).2), hq, hGsub, hGmass,
      finsetPartition_flatten L (fun j => lastProductSet (R' j).carrier I.carrier)
        (lastProductSet P.carrier I.carrier) (fun j z => (S j z).carrier)
        (lastProductSet_partition _ _ _ hR'part) hSpart, ?_, ?_, ?_⟩
    · intro j
      exact ⟨(hSproper _ _).1, hvwidth.trans (by exact_mod_cast (hSproper (fidx.symm j).1 (fidx.symm j).2).2)⟩
    · intro j
      exact hSproduct _ _
    · intro j x hxG hxH hxT
      exact hSlin _ _ x hxT (Finset.mem_inter.mpr ⟨hxG, hxH⟩)

/-- The Lemma 16.6 width for a spectrum cover with graph count `q` and width
exponent `a`, in the square-root form of `section16Lemma6Width_eq_sqrt`. -/
def lemma6WidthWith (m q k : Nat) (a zeta : Real) : Real :=
  (zeta / 2) * Real.sqrt ((m : Real) ^ (a * section16RecurrenceExponent k q))

theorem lemma6WidthWith_antitone_count {m p q k : Nat} {a zeta : Real}
    (hpq : p ≤ q) (hz : 0 ≤ zeta) (ha : 0 < a) :
    lemma6WidthWith m q k a zeta ≤ lemma6WidthWith m p k a zeta := by
  unfold lemma6WidthWith
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.sqrt_le_sqrt
  rcases Nat.eq_zero_or_pos m with hm0 | hm0
  · subst hm0
    have h1 := mul_pos ha ((section16RecurrenceExponent_pos_le_one k q).1)
    have h2 := mul_pos ha ((section16RecurrenceExponent_pos_le_one k p).1)
    simp [Real.zero_rpow h1.ne', Real.zero_rpow h2.ne']
  · apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hm0)
    exact mul_le_mul_of_nonneg_left (section16RecurrenceExponent_antitone k hpq) ha.le

theorem lemma6WidthWith_small {m q k : Nat} {a theta gamma : Real}
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hm : m < 4) :
    lemma6WidthWith m q k a (section16Zeta theta gamma k) ≤ 1 := by
  obtain ⟨hz, hzh⟩ := section16Zeta_pos_le_half k ht ht1 hg hg1
  have he := (section16RecurrenceExponent_pos_le_one k q).1
  have he1 := (section16RecurrenceExponent_pos_le_one k q).2
  have hx0 : 0 ≤ a * section16RecurrenceExponent k q := mul_nonneg ha he.le
  have hx1 : a * section16RecurrenceExponent k q ≤ 1 := by nlinarith
  have hm3 : (m : Real) ≤ 3 := by exact_mod_cast (by omega : m ≤ 3)
  have hpow : (m : Real) ^ (a * section16RecurrenceExponent k q) ≤ 3 := by
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · subst hm0
      rcases eq_or_lt_of_le hx0 with h | h
      · rw [← h]; norm_num
      · rw [Nat.cast_zero, Real.zero_rpow h.ne']; norm_num
    · have hm1 : (1 : Real) ≤ m := by exact_mod_cast hm0
      calc (m : Real) ^ (a * section16RecurrenceExponent k q)
          ≤ (m : Real) ^ (1 : Real) := Real.rpow_le_rpow_of_exponent_le hm1 hx1
        _ = m := Real.rpow_one _
        _ ≤ 3 := hm3
  have hsqrt : Real.sqrt ((m : Real) ^ (a * section16RecurrenceExponent k q)) ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    linarith
  unfold lemma6WidthWith
  calc section16Zeta theta gamma k / 2 *
        Real.sqrt ((m : Real) ^ (a * section16RecurrenceExponent k q))
      ≤ (1 / 2) / 2 * 2 := by
        apply mul_le_mul (by linarith) hsqrt (Real.sqrt_nonneg _) (by norm_num)
    _ ≤ 1 := by norm_num

/-- **Lemma 16.6 with arbitrary spectrum controls.** -/
theorem proper_lemma_16_6_with :
  ∀ (N k m : Nat) [NeZero N] [Fact N.Prime], 1 ≤ k →
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
      ∃ q : Nat,
        (q : Real) ≤ Qb sigma ∧
        ∃ G : Finset (Point N k), ∃ M : Nat,
          ∃ S : Fin M → Box N (k + 1),
            ∃ T : Fin M → Box N k, ∃ A : Fin M → ModAP N,
              G ⊆ Q.carrier ∧
              (1 - sigma) * Q.carrier.card ≤ G.card ∧
              IsBoxPartition S P ∧ (∀ u, (S u).IsProper) ∧
              (∀ u, IsLastCoordinateBoxProduct (S u) (T u) (A u)) ∧
              (∀ u, lemma6WidthWith m q k (Eb sigma) zeta ≤ (S u).width) ∧
              ∀ u h, h ∈ G → h ∈ H1 → h ∈ (T u).carrier →
                LinearOn ((A u).carrier.filter fun x =>
                  (h, x) ∈ section16InducedDomain B H Y) (phiPrime h) := by
  intro N k m _ _ hk theta gamma sigma ht ht1 hg hg1 hs hs1 Qb Eb hQ ha ha1
    B phi H Jbase H1 Y phiPrime
  dsimp only
  intro hH1 hML hselection P Q I hP hproduct hmP
  classical
  let theta1 := section16ThetaOne theta gamma k
  let delta := section16Delta theta1
  let D (x : Point N k) := Finset.univ.filter (fun y => (x, y) ∈ section16InducedDomain B H Y)
  by_cases hm : m < 4
  · have hl := lemma6WidthWith_small (q := 0) (k := k) ht ht1 hg hg1 ha.le ha1 hm
    obtain ⟨M, S, hpart, hproper, hwidth, hlin⟩ :=
      section16_local_linearity_singletons P _ hl D phiPrime
    refine ⟨0, by simpa using hQ, Q.carrier, M, S, (fun j => boxInit (S j)),
      (fun j => (S j).axis (Fin.last k)), Finset.Subset.refl _, ?_, hpart, hproper,
      (fun j => boxInit_last_product (S j)), hwidth, ?_⟩
    · have hcard : (0 : Real) ≤ Q.carrier.card := Nat.cast_nonneg _
      nlinarith
    · intro j x _ _ _
      simpa only [D, Finset.mem_filter, Finset.mem_univ, true_and] using hlin j x
  · have hm4 : 4 ≤ m := by omega
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
    have hfreq (x : Point N k) (hx : x ∈ H1) (r : ZMod N)
        (hr : r ∈ section16LargeSpectrum B x delta) :
        (x, r) ∈ restrictRelation (section16SpectrumRelation B delta) Jbase := by
      have hxJ := (Finset.mem_inter.mp (hH1 ▸ hx)).2
      simpa only [restrictRelation, section16SpectrumRelation, Finset.mem_filter,
        Finset.mem_univ, true_and] using And.intro hr hxJ
    have hlinear (x : Point N k) (hx : x ∈ H1) (v : Nat) (hv : 0 < v)
        (J : ModAP N) (hJ : J.length ≤ v)
        (hdJ : J.step ∈ bohr (section16LargeSpectrum B x delta)
          (section16Zeta theta gamma k / v)) :
        LinearOn (J.carrier ∩ D x) (phiPrime x) := by
      have hxH := (Finset.mem_inter.mp (hH1 ▸ hx)).1
      have h := hselection.2 x hxH v hv J.step hdJ J rfl hJ
      simpa only [D, Finset.inter_filter, Finset.inter_univ] using h
    obtain ⟨q, G, M, S, T, J, hq, hGsub, hGmass, hpart, hSproper, hSproduct, hSlin⟩ :=
      hML.product_linearity_large_m sigma theta gamma hs hs1 ht ht1 hg hg1 hQ ha ha1
        Q' I' u hQ' hI' hstep hu' hk hm4 hmQ' hmI' H1
        (fun x => section16LargeSpectrum B x delta) D phiPrime hfreq hlinear
    refine ⟨q, hq, G, M, S, T, J, ?_, ?_, ?_, (fun j => (hSproper j).1), hSproduct, ?_, ?_⟩
    · simpa only [Q', hcanon.1] using hGsub
    · simpa only [Q', hcanon.1] using hGmass
    · change IsPartition (fun j => (S j).carrier) P.carrier
      simpa only [(boxInit_last_product P).1, lastProductSet, Q', I'] using hpart
    · intro j
      exact (hSproper j).2
    · intro j x hxG hxH hxT
      have h := hSlin j x hxG hxH hxT
      simpa only [D, Finset.inter_filter, Finset.inter_univ] using h

end LeanProofs.GowersSzemeredi
