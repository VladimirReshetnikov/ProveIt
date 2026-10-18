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
* `AbstractFamilyLemma166At`, `abstractFamilyLemma166At_of`: the same for
  abstract members (frequencies `K`, linearity domains `A`, functions `f`); the
  proof never uses Gowers's frame.
* `AllScaleFamilyLemma166At`, `allScaleFamilyLemma166At_of`: its instance at
  Gowers's data.
* `AllScaleFamilyLemma166At.single`: the case of one piece, in the form
  `AllScaleLemma166WidthAt`.

`AllScaleFamilyLemma166At`, `AllScaleFamilyLemma166At.single`,
`allScaleFamilyLemma166At_of` and `familyRecDivisor` are in
`Proofs16FamilyLemma6Side`, outside the final route. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

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
  have hEone : (1 : Real) ≤ E := by exact_mod_cast hE
  set x : Real := (m : Real) ^ (a / (4 * E)) with hx
  have hxpos : 0 < x := Real.rpow_pos_of_pos hmpos _
  -- `8b < x`, as `1 < ζx/(4b)` and `ζ ≤ 1/2`
  have h8b : 8 * (b : Real) < x := by
    rw [div_mul_eq_mul_div, lt_div_iff₀ (by positivity), one_mul] at hlarge
    linarith [mul_le_mul_of_nonneg_right hzHalf hxpos.le]
  -- the scale `n = ⌈x⌉^(2E)`
  let H : Nat := Nat.ceil x
  have hxH : x ≤ (H : Real) := Nat.le_ceil x
  have hH : 0 < H := Nat.ceil_pos.mpr hxpos
  have hHbound : (H : Real) ≤ x ^ 2 / 8 := by
    have hc : (H : Real) < x + 1 := Nat.ceil_lt_add_one hxpos.le
    nlinarith [mul_lt_mul_of_pos_right h8b hxpos, mul_le_mul_of_nonneg_right hbR hxpos.le]
  have hxpow : x ^ (4 * E) = (m : Real) ^ a := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul hmpos.le]
    congr 1
    push_cast
    exact div_mul_cancel₀ _ (by positivity)
  set n : Nat := H ^ (2 * E) with hn_def
  have hnscale : (n : Real) ≤ ((m : Real) / 8) ^ a := by
    rw [Real.div_rpow hmpos.le (by norm_num : (0 : Real) ≤ 8)]
    calc (n : Real) = (H : Real) ^ (2 * E) := by rw [hn_def, Nat.cast_pow]
      _ ≤ (x ^ 2 / 8) ^ (2 * E) := pow_le_pow_left₀ (Nat.cast_nonneg H) hHbound _
      _ = (m : Real) ^ a / (8 : Real) ^ (2 * E) := by
        rw [div_pow, ← pow_mul, show 2 * (2 * E) = 4 * E by omega, hxpow]
      _ ≤ (m : Real) ^ a / (8 : Real) ^ a :=
        div_le_div_of_nonneg_left (Real.rpow_nonneg hmpos.le _) (by positivity)
          ((Real.rpow_le_rpow_of_exponent_le (by norm_num) ha1).trans
            (by rw [Real.rpow_one]; exact le_self_pow₀ (by norm_num) (by omega)))
  have hthreshold : b ^ E ≤ n :=
    (Nat.pow_le_pow_left (by exact_mod_cast (show (b : Real) ≤ H by linarith)) _).trans
      (Nat.pow_le_pow_right hH (by omega : E ≤ 2 * E))
  -- `x ≤ m`, so `m ≥ 16`
  have hxle : x ≤ (m : Real) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hmR
      (div_le_one_of_le₀ (by linarith) (by positivity) : a / (4 * (E : Real)) ≤ 1)
  have hnroot : (n : Real) ^ ((E : Real)⁻¹) = (H : Real) ^ 2 := by
    rw [hn_def, Nat.cast_pow, pow_mul]
    exact Real.pow_rpow_inv_natCast (by positivity) (by omega)
  refine ⟨n, by exact_mod_cast (show (4 : Real) ≤ m by linarith), pow_pos hH _, hnscale,
    hthreshold, ?_⟩
  rw [hnroot, Real.sqrt_sq (Nat.cast_nonneg H)]
  exact mul_le_mul (div_le_div_of_nonneg_left hz.le (by norm_num) (by linarith)) hxH hxpos.le
    (by positivity)

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
  have hfam := hrec.retiled_family (fun q => familyRecThr_pos (by omega) q)
  let q := Nat.floor (Qb sigma)
  let b := C * (q + 1)
  let E := 2 * (p * (q + 1) ^ (2 * (2 ^ (k + 1))))
  let l := section16PowerWidth (familyWidthPrefactor C) (familyWidthDivisor k p) m q (Eb sigma) zeta
  by_cases hl : l ≤ 1
  · -- below the threshold, single points
    obtain ⟨M, x, hpart⟩ := box_singleton_partition P
    refine ⟨Q.carrier, M, fun j => pointSingletonBox (x j),
      (fun j => boxInit (pointSingletonBox (x j))),
      (fun j => (pointSingletonBox (x j)).axis (Fin.last k)), Finset.Subset.refl _,
      mul_le_of_le_one_left (Nat.cast_nonneg _) (by linarith), hpart,
      fun j => pointSingletonBox_isProper _, fun j => boxInit_last_product _, fun j => ?_,
      fun c j h _ _ _ => LinearOn.of_subset_singleton _ _ _
        (Finset.inter_subset_left.trans (pointSingletonBox_axis_carrier _ _).subset)⟩
    simpa only [pointSingletonBox_width (by omega : 0 < k + 1), Nat.cast_one] using hl
  · have hb : 2 ≤ b := hC.trans (Nat.le_mul_of_pos_right C (by omega))
    have hE : 0 < E := by dsimp [E]; positivity
    have hlarge : 1 < (zeta / (4 * (b : Real))) * (m : Real) ^ (Eb sigma / (4 * (E : Real))) :=
      lt_of_not_ge hl
    have hm : 1 ≤ m := by
      by_contra hm
      have he : Eb sigma / (4 * (E : Real)) ≠ 0 := by positivity
      rw [show m = 0 by omega, Nat.cast_zero, Real.zero_rpow he, mul_zero] at hlarge
      norm_num at hlarge
    obtain ⟨n, hm4, hn, hnscale, hnthreshold, htarget⟩ :=
      section16_rounded_recurrence_scale hm hb hE ha ha1 hz hzHalf hlarge
    -- one short-parent cover of `Γ` over the base `Q' = boxInit P`
    let Q' := boxInit P
    let I' := P.axis (Fin.last k)
    have hI' : I'.IsProper := hP (Fin.last k)
    have hmI' : m ≤ I'.length := hmP.trans (P.width_le_axis_length _)
    obtain ⟨u, hu⟩ := I'.step_isUnit_of_prime hI' (by omega)
    have hstep : I'.step = Q'.commonDiff := P.axis_step (Fin.last k)
    obtain ⟨q', G, bb, Bp, cnt, R, mu, hq', hGsub, hGmass, hBpart, _,
        hBaxes, hBstep, hRpart, hRproper, hRwidth, hmu, hcover⟩ :=
      hML.short_parent_cover sigma hs hs1 hQ ha.le Q' I' (boxInit_isProper P hP) hI' (by omega)
        hm4 (hmP.trans (boxInit_width P (by omega))) hmI'
    have hq'q : q' ≤ q := Nat.le_floor hq'
    let lcell := (zeta / 2) * Real.sqrt ((n : Real) ^ familyRecExp k p q')
    have htarget' : (zeta / (4 * (b : Real))) * (m : Real) ^ (Eb sigma / (4 * (E : Real))) ≤
        lcell := htarget.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
          (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (familyRecExp_antitone hp hq'q)))
          (by positivity))
    -- the retiled family bound on every cell `R' j`
    let e := section5NatFlattenEquiv cnt
    let R' := boxFlatten cnt R
    let i : Fin k := ⟨0, by omega⟩
    have hnR (j : Fin (∑ z, cnt z)) : n ≤ (R' j).width := by
      exact_mod_cast hnscale.trans (hRwidth (e.symm j).1 (e.symm j).2)
    choose L S T J hSpart hSproper hSproduct hSlin using fun j : Fin (∑ z, cnt z) =>
      hfam q' N n (R' j) ((Bp (e.symm j).1).axis i) I' i u (hRproper _ _) hI'
        (by rw [(Bp _).axis_step, hBstep, ← hstep, ← hu])
        (by rw [(Bp _).axis_step, hBstep, hstep])
        ((R' j).axis_carrier_subset_of_carrier_subset (Bp (e.symm j).1)
          ((R' j).carrier_nonempty_of_axis_pos fun z =>
            hn.trans_le ((hnR j).trans ((R' j).width_le_axis_length z)))
          (IsPartition.cell_subset (hRpart (e.symm j).1) (e.symm j).2) i)
        (hBaxes _ i).2.1 (hBaxes _ i).2.2 (mu (e.symm j).1 (e.symm j).2) (hmu _ _)
        ((familyRecThr_mono (by omega) hq'q).trans hnthreshold) (hnR j) ι K (fun c => G ∩ H1 c)
        A f zeta hz hzHalf (fun c x hx hxGH r hr => hcover (e.symm j).1 (e.symm j).2 x hx
          (Finset.mem_inter.mp hxGH).1 r (hfreq c x (Finset.mem_inter.mp hxGH).2 r hr))
        (fun c x hxGH => hlinear c x (Finset.mem_inter.mp hxGH).2) (hlarge.trans_le htarget')
    let fidx := section5NatFlattenEquiv L
    have hcanon := hproduct.canonical_factors (by omega : 0 < P.width)
    refine ⟨G, ∑ j, L j, boxFlatten L S, (fun j => T (fidx.symm j).1 (fidx.symm j).2),
      (fun j => J (fidx.symm j).1 (fidx.symm j).2), by simpa only [Q', hcanon.1] using hGsub,
      by simpa only [Q', hcanon.1] using hGmass, ?_, fun j => (hSproper _ _).1,
      fun j => hSproduct _ _,
      fun j => htarget'.trans (hSproper (fidx.symm j).1 (fidx.symm j).2).2,
      fun c j h hhG hhH hhT =>
        hSlin (fidx.symm j).1 c (fidx.symm j).2 h hhT (Finset.mem_inter.mpr ⟨hhG, hhH⟩)⟩
    have hpartQ : IsPartition (fun z => (boxFlatten L S z).carrier)
        (lastProductSet Q'.carrier I'.carrier) :=
      finsetPartition_flatten L (fun j => lastProductSet (R' j).carrier I'.carrier)
        (lastProductSet Q'.carrier I'.carrier) (fun j z => (S j z).carrier)
        (lastProductSet_partition _ _ _ (boxFlatten_partition Q' Bp cnt R hBpart hRpart)) hSpart
    change IsPartition (fun j => (boxFlatten L S j).carrier) P.carrier
    simpa only [(boxInit_last_product P).1, lastProductSet, Q', I'] using hpartQ

end LeanProofs.GowersSzemeredi
