import GowersSzemeredi.Proofs16AbstractFamily
import GowersSzemeredi.Proofs16IntegerLocalCover
import GowersSzemeredi.Proofs16IntegerBoxFactors

/-! Family Lemma 16.6 with genuine integer input and output boxes.
The original polynomial profile constants, graph counts, width and deletion
budgets are retained. Canonicalization handles either input orientation. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- **Lemma 16.6 for abstract members, at every scale.** -/
def IntegerAbstractFamilyLemma166At (k : Nat) (W : Nat → Nat → Real → Real → Real) : Prop :=
  ∀ (N m : Nat) [NeZero N], 1 ≤ k →
    ∀ (zeta sigma : Real), 0 < zeta → zeta ≤ 1 / 2 → 0 < sigma → sigma ≤ 1 →
    ∀ (Qb Eb : Real → Real), 0 ≤ Qb sigma → 0 < Eb sigma → Eb sigma ≤ 1 →
    ∀ (Gamma : Finset (Point N k × ZMod N)), IntegerMultiplyLinearWith Qb Eb Gamma →
    ∀ (ι : Type) (H1 : ι → Finset (Point N k)) (K A : ι → Point N k → Finset (ZMod N))
      (f : ι → Point N k → ZMod N → ZMod N),
    (∀ c, ∀ x ∈ H1 c, ∀ r ∈ K c x, (x, r) ∈ Gamma) →
    (∀ c, ∀ x ∈ H1 c, ∀ v : Nat, 0 < v → ∀ J : ModAP N, J.length ≤ v →
      J.step ∈ bohr (K c x) (zeta / v) → LinearOn (J.carrier ∩ A c x) (f c x)) →
    ∀ (P : Box N (k + 1)) (Q : Box N k) (I : ModAP N),
      P.HasIntegerRepresentatives → IsLastCoordinateBoxProduct P Q I → m ≤ P.width →
      ∃ G : Finset (Point N k), ∃ M : Nat,
          ∃ S : Fin M → Box N (k + 1),
            ∃ T : Fin M → Box N k, ∃ J : Fin M → ModAP N,
              G ⊆ Q.carrier ∧
              (1 - sigma) * Q.carrier.card ≤ G.card ∧
              IsBoxPartition S P ∧ (∀ u, (S u).IsAscendingInteger) ∧
              (∀ u, IsLastCoordinateBoxProduct (S u) (T u) (J u)) ∧
              (∀ u, W m (Nat.floor (Qb sigma)) (Eb sigma) zeta ≤ (S u).width) ∧
              ∀ c u x, x ∈ G → x ∈ H1 c → x ∈ (T u).carrier →
                LinearOn ((J u).carrier ∩ A c x) (f c x)

/-- The abstract family Lemma 16.6 from the recurrence profile. -/
theorem integerAbstractFamilyLemma166At_of (k : Nat) {C p : Nat} (hC : 2 ≤ C) (hp : 0 < p)
    (hrec : IntegerSection16RecurrenceProfileWith k (familyRecThr k C p) (familyRecExp k p)) :
    IntegerAbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor C) (familyWidthDivisor k p)) := by
  unfold IntegerAbstractFamilyLemma166At
  intro N m _ hk zeta sigma hz hzHalf hs hs1 Qb Eb hQ ha ha1 Gamma hML
    ι H1 K A f hfreq hlinear P Q I hP hproduct hmP
  classical
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
      fun j => pointSingletonBox_isAscendingInteger _,
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
    obtain ⟨d, A0, hAstep, hd, hA0, hcarrier, hwidth, _⟩ := hP.canonical_axes
    let PC := integerAxesBox N A0 d hAstep
    have hPC : PC.IsAscendingInteger :=
      ⟨d, A0, hd, rfl, fun i => ⟨(hA0 i).1, hAstep i, (hA0 i).2, rfl⟩⟩
    have hmC : m ≤ PC.width := by rwa [hwidth]
    have hneP : P.carrier.Nonempty :=
      P.carrier_nonempty_of_axis_pos (fun i => hwidthpos.trans_le (P.width_le_axis_length i))
    have hneC : PC.carrier.Nonempty := by rwa [hcarrier]
    have hInit : (boxInit PC).carrier = (boxInit P).carrier :=
      boxInit_carrier_eq_of_box_carrier_eq PC P hcarrier hneC hneP
    let Q' := boxInit PC
    let I0 := A0 (Fin.last k)
    let I' := I0.toModAP N
    have hIeq : I' = PC.axis (Fin.last k) := rfl
    have hQ' : Q'.IsAscendingInteger := boxInit_isAscendingInteger PC hPC
    have hI0 : I0.IsProper := (hA0 (Fin.last k)).1
    have hI0N : I0.carrier ⊆ Finset.range N := (hA0 (Fin.last k)).2
    have hI' : I'.IsProper := (I0.toModAP_hasIntegerRepresentatives hI0 hI0N).isProper
    have hmQ' : m ≤ Q'.width := hmC.trans (boxInit_width PC (by omega))
    have hmI' : m ≤ I'.length := hmC.trans (PC.width_le_axis_length (Fin.last k))
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
    have hn2 : 2 ≤ n := by
      by_contra h
      have hn1 : n = 1 := by omega
      simp only [lcell, hn1, Nat.cast_one, Real.one_rpow, Real.sqrt_one, mul_one] at hlcell
      linarith only [hlcell, hzHalf]
    choose dB AB hdB hBcommon hBA using hBproper
    have hBasc (j : Fin bb) : (Bp j).IsAscendingInteger :=
      ⟨dB j, AB j, hdB j, hBcommon j, hBA j⟩
    let BN (j : Fin (∑ z, cnt z)) := AB (e.symm j).1 i
    have hBN (j : Fin (∑ z, cnt z)) : (BN j).carrier ⊆ Finset.range N :=
      (hBA (e.symm j).1 i).2.2.1
    have hBNeq (j : Fin (∑ z, cnt z)) : (BN j).toModAP N = (Bp (e.symm j).1).axis i :=
      (hBA (e.symm j).1 i).2.2.2
    have hBNlen (j : Fin (∑ z, cnt z)) : 2 ≤ (BN j).length := by
      have hc := Finset.card_le_card (hsub j)
      rw [show ((R' j).axis i).carrier.card = ((R' j).axis i).length from
        (hRproper (e.symm j).1 (e.symm j).2).isProper i,
        show ((Bp (e.symm j).1).axis i).carrier.card = ((Bp (e.symm j).1).axis i).length from
          (hBasc (e.symm j).1).isProper i] at hc
      have hlen : (BN j).length = ((Bp (e.symm j).1).axis i).length :=
        congrArg ModAP.length (hBNeq j)
      rw [hlen]
      exact hn2.trans ((hnR j).trans ((R' j).width_le_axis_length i) |>.trans hc)
    have hparallel (j : Fin (∑ z, cnt z)) : (BN j).step = I0.step := by
      apply (BN j).step_eq_of_mod_step_eq I0 (hBN j) hI0N (hBNlen j) (by change 2 ≤ I'.length; omega)
      rw [hBNeq j, (Bp _).axis_step, hBstep]
      change (d : ZMod N) = (I0.step : ZMod N)
      rw [show I0.step = d from hAstep (Fin.last k)]
    have hlocal (j : Fin (∑ z, cnt z)) :
        ∃ M : Nat, ∃ S : Fin M → Box N (k + 1), ∃ T : Fin M → Box N k,
          ∃ J : Fin M → ModAP N,
          IsPartition (fun z => (S z).carrier) (lastProductSet (R' j).carrier I'.carrier) ∧
          (∀ z, (S z).IsAscendingInteger ∧ lcell ≤ (S z).width) ∧
          (∀ z, IsLastCoordinateBoxProduct (S z) (T z) (J z)) ∧
          ∀ c z x, x ∈ (T z).carrier → x ∈ G ∩ H1 c →
            LinearOn ((J z).carrier ∩ A c x) (f c x) := by
      obtain ⟨L, S, T, J, hpart, hS, _, hprod, _, hlin⟩ :=
        hrec.retiled_family (fun q => familyRecThr_pos (by omega) q) q' N n (R' j)
          (hRproper _ _).toGenuine (BN j) I0 i (hBA (e.symm j).1 i).1 hI0
          (hBN j) hI0N (hparallel j) (by rw [hBNeq j]; exact hsub j)
          (by
            change ((BN j).toModAP N).length ≤ I'.length
            rw [hBNeq j]
            exact (hBaxes (e.symm j).1 i).2.2) (mu (e.symm j).1 (e.symm j).2) (hmu _ _)
          hthreshold (hnR j) ι K (fun c => G ∩ H1 c) A f zeta hz hzHalf
          (by
            intro c x hx hxGH r hr
            exact hcover (e.symm j).1 (e.symm j).2 x hx (Finset.mem_inter.mp hxGH).1 r
              (hfreq c x (Finset.mem_inter.mp hxGH).2 r hr))
          (by
            intro c x hxGH v hv J hJ hd
            exact hlinear c x (Finset.mem_inter.mp hxGH).2 v hv J hJ hd) hlcell
      exact ⟨L, S, T, J, hpart, hS, hprod, hlin⟩
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
    · simpa only [Q', hInit, hcanon.1] using hGsub
    · simpa only [Q', hInit, hcanon.1] using hGmass
    · change IsPartition (fun j => (boxFlatten L S j).carrier) P.carrier
      rw [← hcarrier]
      change IsPartition (fun j => (boxFlatten L S j).carrier) PC.carrier
      rw [(boxInit_last_product PC).1]
      simpa only [lastProductSet, Q', hIeq] using hpartQ
    · intro j
      have hw := (hSproper (fidx.symm j).1 (fidx.symm j).2).2
      exact (le_of_eq hlval).trans (htarget'.trans hw)
    · intro c j h hhG hhH hhT
      exact hSlin (fidx.symm j).1 c (fidx.symm j).2 h hhT (Finset.mem_inter.mpr ⟨hhG, hhH⟩)

theorem integerAbstractFamilyLemma166At_explicit (k : Nat) :
    IntegerAbstractFamilyLemma166At k
      (section16PowerWidth
        (familyWidthPrefactor (Nat.ceil (multiaffinePartitionK (k + 1) (2 ^ (k + 1)))))
        (familyWidthDivisor k ((k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1))))) := by
  apply integerAbstractFamilyLemma166At_of k
    (by
      have hK := two_le_multiaffinePartitionK (k + 1) (2 ^ (k + 1))
      exact_mod_cast hK.trans (Nat.le_ceil _))
    (Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
  exact integerSection16RecurrenceProfileWith_explicit k

end LeanProofs.GowersSzemeredi
