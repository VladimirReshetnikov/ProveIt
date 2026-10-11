import GowersSzemeredi.Proofs16FamilyRetiledLinearity
import GowersSzemeredi.Proofs16PieceCoverWithRemainder
import GowersSzemeredi.Proofs16SingletonPartition

/-! Lemma 16.6 for a family of pieces, on one common partition.

Step (B) of Notes L.3. The pieces of one relation (or of a family of
relations) each have their own induced function `φ′_c` and spectrum
`Δ_c`. If one relation `Γ` covers every member's large spectrum, then one
spectrum cover of `Γ` and one recurrence partition make every `φ′_c(h, ·)`
linear on the same cells. Nothing is refined sequentially, so the width
exponent is that of a single piece, at the graph count of `Γ`.

The polynomial recurrence enters through `Section16RecurrenceProfileWith`
at the explicit shapes `familyRecThr` and `familyRecExp`. These are copies of
`section16SimultaneousThreshold` and `section16SimultaneousExponent`, so the
heavy `PolynomialSection16RecurrenceProfileAt k K p` is definitionally an
instance. The widths are `section16PowerWidth (familyWidthPrefactor C)
(familyWidthDivisor k p)`, the polynomial width
`ζ/(4C(q+1)) · m^(a/(8p(q+1)^(2^(k+2))))`.
* `section16_rounded_recurrence_scale`: a copy of the arithmetic lemma
  `polynomial_localized_recurrence_parameters`, which sits in a heavy module.
* `AllScaleFamilyLemma166At`, `allScaleFamilyLemma166At_of`.
* `AllScaleFamilyLemma166At.single`: the case of one piece, in the form
  `AllScaleLemma166WidthAt`. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- The divisor `2p(q+1)^(2^(k+2))` of the simultaneous recurrence exponent. -/
def familyRecDivisor (k p q : Nat) : Nat := 2 * (p * (q + 1) ^ (2 * (2 ^ (k + 1))))

/-- The simultaneous recurrence exponent (`section16SimultaneousExponent`). -/
def familyRecExp (k p q : Nat) : Real := ((2 * (p * (q + 1) ^ (2 * (2 ^ (k + 1)))) : Nat) : Real)⁻¹

/-- The simultaneous recurrence threshold (`section16SimultaneousThreshold`). -/
def familyRecThr (k K p q : Nat) : Nat := (K * (q + 1)) ^ (2 * (p * (q + 1) ^ (2 * (2 ^ (k + 1)))))

def familyWidthPrefactor (C : Nat) (q : Nat) : Real := 4 * ((C * (q + 1) : Nat) : Real)

def familyWidthDivisor (k p : Nat) (q : Nat) : Real :=
  4 * ((2 * (p * (q + 1) ^ (2 * (2 ^ (k + 1)))) : Nat) : Real)

theorem familyRecThr_pos {k K p : Nat} (hK : 1 ≤ K) (q : Nat) : 0 < familyRecThr k K p q := by
  unfold familyRecThr
  exact pow_pos (Nat.mul_pos (by omega) (by omega)) _

theorem familyRecThr_mono {k K p q r : Nat} (hK : 1 ≤ K) (hqr : q ≤ r) :
    familyRecThr k K p q ≤ familyRecThr k K p r := by
  unfold familyRecThr
  have hbase : K * (q + 1) ≤ K * (r + 1) := Nat.mul_le_mul_left K (by omega)
  have hexp : 2 * (p * (q + 1) ^ (2 * 2 ^ (k + 1))) ≤
      2 * (p * (r + 1) ^ (2 * 2 ^ (k + 1))) :=
    Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left p (Nat.pow_le_pow_left (by omega) _))
  exact (Nat.pow_le_pow_left hbase _).trans
    (Nat.pow_le_pow_right (Nat.mul_pos (by omega) (by omega)) hexp)

theorem familyRecExp_pos (k p q : Nat) (hp : 0 < p) : 0 < familyRecExp k p q := by
  unfold familyRecExp
  positivity

theorem familyRecExp_antitone {k p q r : Nat} (hp : 0 < p) (hqr : q ≤ r) :
    familyRecExp k p r ≤ familyRecExp k p q := by
  unfold familyRecExp
  apply inv_anti₀ (by positivity)
  exact_mod_cast Nat.mul_le_mul_left 2
    (Nat.mul_le_mul_left p (Nat.pow_le_pow_left (by omega : q + 1 ≤ r + 1) _))

theorem familyWidthPrefactor_pos {C : Nat} (hC : 1 ≤ C) (q : Nat) :
    0 < familyWidthPrefactor C q := by
  unfold familyWidthPrefactor
  have : 0 < C * (q + 1) := Nat.mul_pos (by omega) (by omega)
  positivity

theorem familyWidthDivisor_pos {k p : Nat} (hp : 0 < p) (q : Nat) :
    0 < familyWidthDivisor k p q := by
  unfold familyWidthDivisor
  have : 0 < 2 * (p * (q + 1) ^ (2 * (2 ^ (k + 1)))) := by positivity
  positivity

/-- Above the singleton regime, an integer recurrence scale between `b^E`
and `(m/8)^a` exists, and its retiled width dominates the target. A copy
of `polynomial_localized_recurrence_parameters`. -/
theorem section16_rounded_recurrence_scale {m b E : Nat} {a zeta : Real}
    (hm : 1 ≤ m) (hb : 2 ≤ b) (hE : 0 < E)
    (_ha : 0 < a) (ha1 : a ≤ 1) (hz : 0 < zeta) (hzHalf : zeta ≤ 1 / 2)
    (hlarge : 1 < (zeta / (4 * b)) * (m : Real) ^ (a / (4 * E))) :
    ∃ n : Nat, 4 ≤ m ∧ 0 < n ∧
      (n : Real) ≤ ((m : Real) / 8) ^ a ∧ b ^ E ≤ n ∧
      (zeta / (4 * b)) * (m : Real) ^ (a / (4 * E)) ≤
        (zeta / 2) * Real.sqrt ((n : Real) ^ ((E : Real)⁻¹)) := by
  have hmR : (1 : Real) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : Real) < m := zero_lt_one.trans_le hmR
  have hbR : (2 : Real) ≤ b := by exact_mod_cast hb
  have hER : (0 : Real) < E := by exact_mod_cast hE
  have hEone : (1 : Real) ≤ E := by exact_mod_cast hE
  let x : Real := (m : Real) ^ (a / (4 * E))
  have hxpos : 0 < x := Real.rpow_pos_of_pos hmpos _
  change 1 < (zeta / (4 * b)) * x at hlarge
  have hden : (0 : Real) < 4 * b := by positivity
  have hscaled : 4 * (b : Real) < zeta * x := by
    have h := mul_lt_mul_of_pos_right hlarge hden
    have heq : (zeta / (4 * (b : Real)) * x) * (4 * b) = zeta * x := by field_simp
    simpa only [one_mul, heq] using h
  have hzx : zeta * x ≤ (1 / 2) * x := mul_le_mul_of_nonneg_right hzHalf hxpos.le
  have hx16 : 16 < x := by nlinarith
  have hbx : (b : Real) ≤ x := by nlinarith
  let H : Nat := Nat.ceil x
  have hxH : x ≤ (H : Real) := Nat.le_ceil x
  have hH : 0 < H := Nat.ceil_pos.mpr hxpos
  have hHbound : (H : Real) ≤ x ^ 2 / 8 := by
    have hc : (H : Real) ≤ x + 1 := (Nat.ceil_lt_add_one hxpos.le).le
    nlinarith
  have hxpow : x ^ (4 * E) = (m : Real) ^ a := by
    dsimp only [x]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hmpos.le]
    congr 1
    push_cast
    exact div_mul_cancel₀ _ (by positivity)
  let n : Nat := H ^ (2 * E)
  have hn : 0 < n := pow_pos hH _
  have h8a : (8 : Real) ^ a ≤ 8 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : Real) ≤ 8) ha1
  have h8E : (8 : Real) ≤ (8 : Real) ^ (2 * E) := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : Real) ≤ 8)
      (by omega : 1 ≤ 2 * E)
  have hnscale : (n : Real) ≤ ((m : Real) / 8) ^ a := by
    rw [Real.div_rpow hmpos.le (by norm_num : (0 : Real) ≤ 8)]
    calc
      (n : Real) = (H : Real) ^ (2 * E) := by simp only [n, Nat.cast_pow]
      _ ≤ (x ^ 2 / 8) ^ (2 * E) := pow_le_pow_left₀ (Nat.cast_nonneg H) hHbound _
      _ = (m : Real) ^ a / (8 : Real) ^ (2 * E) := by
        rw [div_pow, ← pow_mul, show 2 * (2 * E) = 4 * E by omega, hxpow]
      _ ≤ (m : Real) ^ a / (8 : Real) ^ a :=
        div_le_div_of_nonneg_left (Real.rpow_nonneg hmpos.le _)
          (Real.rpow_pos_of_pos (by norm_num : (0 : Real) < 8) _) (h8a.trans h8E)
  have hbH : b ≤ H := by exact_mod_cast hbx.trans hxH
  have hthreshold : b ^ E ≤ n :=
    (Nat.pow_le_pow_left hbH _).trans (Nat.pow_le_pow_right hH (by omega : E ≤ 2 * E))
  have hxle : x ≤ (m : Real) := by
    have he : a / (4 * (E : Real)) ≤ 1 := (div_le_iff₀ (by positivity)).mpr (by nlinarith)
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hmR he
  have hm4 : 4 ≤ m := by
    have h : (4 : Real) ≤ m := by linarith
    exact_mod_cast h
  have hnroot : (n : Real) ^ ((E : Real)⁻¹) = (H : Real) ^ 2 := by
    dsimp only [n]
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg H)]
    rw [← Real.rpow_natCast]
    congr 1
    push_cast
    field_simp
  refine ⟨n, hm4, hn, hnscale, hthreshold, ?_⟩
  rw [hnroot, Real.sqrt_sq (Nat.cast_nonneg H)]
  have hfactor : zeta / (4 * (b : Real)) ≤ zeta / 2 :=
    div_le_div_of_nonneg_left hz.le (by norm_num) (by nlinarith)
  exact mul_le_mul hfactor hxH hxpos.le (by positivity)

/-- **Lemma 16.6 for a family, at every scale.** One relation `Γ` covers
the large spectra of all members; one partition makes every member's
induced function linear. -/
def AllScaleFamilyLemma166At (k : Nat) (W : Nat → Nat → Real → Real → Real) : Prop :=
  ∀ (N m : Nat) [NeZero N] [Fact N.Prime], 1 ≤ k →
    ∀ (theta gamma sigma : Real),
    0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 →
    0 < sigma → sigma ≤ 1 →
    ∀ (Qb Eb : Real → Real), 0 ≤ Qb sigma → 0 < Eb sigma → Eb sigma ≤ 1 →
    ∀ (Gamma : Finset (Point N k × ZMod N)), MultiplyLinearWith Qb Eb Gamma →
    ∀ (ι : Type) (B : ι → Finset (Point N (k + 1))) (phi : ι → Point N (k + 1) → ZMod N)
      (H H1 : ι → Finset (Point N k))
      (Y : (c : ι) → (h : Point N k) → Finset (Section16CubeElement (B c) h))
      (phiPrime : ι → Point N k → ZMod N → ZMod N),
    (∀ c, ∀ x ∈ H1 c, ∀ r ∈ section16LargeSpectrum (B c) x
      (section16Delta (section16ThetaOne theta gamma k)), (x, r) ∈ Gamma) →
    (∀ c, H1 c ⊆ H c) →
    (∀ c, Section16InducedSelection (B c) (phi c) (H c) (Y c)
      (fun h => section16LargeSpectrum (B c) h (section16Delta (section16ThetaOne theta gamma k)))
      (section16Zeta theta gamma k) (phiPrime c)) →
    ∀ (P : Box N (k + 1)) (Q : Box N k) (I : ModAP N),
      P.IsProper → IsLastCoordinateBoxProduct P Q I → m ≤ P.width →
      ∃ G : Finset (Point N k), ∃ M : Nat,
          ∃ S : Fin M → Box N (k + 1),
            ∃ T : Fin M → Box N k, ∃ A : Fin M → ModAP N,
              G ⊆ Q.carrier ∧
              (1 - sigma) * Q.carrier.card ≤ G.card ∧
              IsBoxPartition S P ∧ (∀ u, (S u).IsProper) ∧
              (∀ u, IsLastCoordinateBoxProduct (S u) (T u) (A u)) ∧
              (∀ u, W m (Nat.floor (Qb sigma)) (Eb sigma) (section16Zeta theta gamma k) ≤
                (S u).width) ∧
              ∀ c u h, h ∈ G → h ∈ H1 c → h ∈ (T u).carrier →
                LinearOn ((A u).carrier.filter fun x =>
                  (h, x) ∈ section16InducedDomain (B c) (H c) (Y c)) (phiPrime c h)

/-- **The family Lemma 16.6 from the recurrence profile.** -/
theorem allScaleFamilyLemma166At_of (k : Nat) {C p : Nat} (hC : 2 ≤ C) (hp : 0 < p)
    (hrec : Section16RecurrenceProfileWith k (familyRecThr k C p) (familyRecExp k p)) :
    AllScaleFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor C) (familyWidthDivisor k p)) := by
  unfold AllScaleFamilyLemma166At
  intro N m _ _ hk theta gamma sigma ht ht1 hg hg1 hs hs1 Qb Eb hQ ha ha1 Gamma hML
    ι B phi H H1 Y phiPrime hfreq hH1 hselection P Q I hP hproduct hmP
  classical
  have hfam := hrec.retiled_family (fun q => familyRecThr_pos (by omega) q)
  let delta := section16Delta (section16ThetaOne theta gamma k)
  let zeta := section16Zeta theta gamma k
  obtain ⟨hz, hzHalf⟩ := section16Zeta_pos_le_half k ht ht1 hg hg1
  let D (c : ι) (x : Point N k) :=
    Finset.univ.filter (fun y => (x, y) ∈ section16InducedDomain (B c) (H c) (Y c))
  let q := Nat.floor (Qb sigma)
  let b := C * (q + 1)
  let E := 2 * (p * (q + 1) ^ (2 * (2 ^ (k + 1))))
  let l := section16PowerWidth (familyWidthPrefactor C) (familyWidthDivisor k p) m q (Eb sigma) zeta
  have hlval : l = (zeta / (4 * (b : Real))) * (m : Real) ^ (Eb sigma / (4 * (E : Real))) := rfl
  by_cases hl : l ≤ 1
  · -- singleton cells
    obtain ⟨M, x, hpart⟩ := box_singleton_partition P
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
      simpa only [pointSingletonBox_axis_carrier] using (Finset.mem_filter.mp hy).1
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
    -- the base factors of P
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
    -- the spectrum cover on short parents
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
            LinearOn ((J z).carrier ∩ D c x) (phiPrime c x) := by
      apply hfam q' N n (R' j) ((Bp (e.symm j).1).axis i) I' i u
        (hRproper _ _) hI' (hBunit j) (hIparallel j) (hsub j)
        (hBaxes _ i).2.1 (hBaxes _ i).2.2 (mu (e.symm j).1 (e.symm j).2)
        (hmu _ _) hthreshold (hnR j) ι (fun c x => section16LargeSpectrum (B c) x delta)
        (fun c => G ∩ H1 c) D phiPrime zeta hz hzHalf
      · intro c x hx hxGH r hr
        exact hcover (e.symm j).1 (e.symm j).2 x hx (Finset.mem_inter.mp hxGH).1 r
          (hfreq c x (Finset.mem_inter.mp hxGH).2 r hr)
      · intro c x hxGH v hv J hJ hd
        have hxH := hH1 c (Finset.mem_inter.mp hxGH).2
        have h := (hselection c).2 x hxH v hv J.step hd J rfl hJ
        simpa only [D, Finset.inter_filter, Finset.inter_univ] using h
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
      have hlin := hSlin (fidx.symm j).1 c (fidx.symm j).2 h hhT (Finset.mem_inter.mpr ⟨hhG, hhH⟩)
      simpa only [D, Finset.inter_filter, Finset.inter_univ] using hlin


/-- The family Lemma 16.6 contains the single-piece one: take one member and
the restricted spectrum relation as `Γ`. -/
theorem AllScaleFamilyLemma166At.single {k : Nat} {W : Nat → Nat → Real → Real → Real}
    (hfam : AllScaleFamilyLemma166At k W) : AllScaleLemma166WidthAt k W := by
  unfold AllScaleLemma166WidthAt
  intro N m _ _ hk theta gamma sigma ht ht1 hg hg1 hs hs1 Qb Eb hQ ha ha1
    B phi H Jbase H1 Y phiPrime
  dsimp only
  intro hH1 hML hselection P Q I hP hproduct hmP
  classical
  have hfreq : ∀ _c : Unit, ∀ x ∈ H1, ∀ r ∈ section16LargeSpectrum B x
      (section16Delta (section16ThetaOne theta gamma k)),
      (x, r) ∈ restrictRelation (section16SpectrumRelation B
        (section16Delta (section16ThetaOne theta gamma k))) Jbase := by
    intro _ x hx r hr
    have hxJ := (Finset.mem_inter.mp (hH1 ▸ hx)).2
    simpa only [restrictRelation, section16SpectrumRelation, Finset.mem_filter,
      Finset.mem_univ, true_and] using And.intro hr hxJ
  have hsub : ∀ _c : Unit, H1 ⊆ H := fun _ => by
    rw [hH1]; exact Finset.inter_subset_left
  obtain ⟨G, M, S, T, A, hGsub, hGmass, hpart, hproper, hprod', hwidth, hlin⟩ :=
    hfam N m hk theta gamma sigma ht ht1 hg hg1 hs hs1 Qb Eb hQ ha ha1 _ hML Unit
      (fun _ => B) (fun _ => phi) (fun _ => H) (fun _ => H1) (fun _ => Y) (fun _ => phiPrime)
      hfreq hsub (fun _ => hselection) P Q I hP hproduct hmP
  exact ⟨G, M, S, T, A, hGsub, hGmass, hpart, hproper, hprod', hwidth,
    fun u h hhG hhH hhT => hlin () u h hhG hhH hhT⟩
end LeanProofs.GowersSzemeredi
