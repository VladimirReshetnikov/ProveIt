import OAI.Combinatorics.Progressions.Dynamics.PreparedModularCanonicalDetectorResourceBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

noncomputable def generalDetectorCoefficientCost (m dim : ℕ) : ℕ :=
  ∑ j : Fin m, Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1))

noncomputable def preparedModularGeneralDetectorResources {α : Type*} [Semiring α]
    (K : PreparedModularCanonicalDetectorResourceConstants) (dim : ℕ) (P L : α) :
    PreparedModularCanonicalDetectorResources α :=
  let Q : α := (P + K.Cperiod) ^ K.Cperiod
  let v : α := P + 8
  let w : α := P + 1
  let Dg : α := 2 * P + K.m * P + (layerTailDegree K.m + 1 : ℕ) + K.m + comparisonProfileBound + 8
  let Pproj : α := 4 * (L + 8) ^ 2
  let coverLog : α := (Pproj + (dim + 2 : ℕ) + K.Acover) ^ K.Acover
  let Pmass : α := (Pproj + K.Asample) ^ K.Asample
  let Vlog : α := L ^ 2 * ((layerTailDegree K.m + 1 : ℕ) * L + 1)
  let Nlog : α := (K.m * 2 ^ dim : ℕ) * (P + 8) * (1 + 4 * P)
  let Pbox : α := 2 * P ^ 2 + 8
  let Banalytic : α := Dg + 4 * P + 32
  let baseAmbient : α := Pproj + coverLog + Vlog + Nlog + Q + (layerTailDegree K.m + 1 : ℕ) * L + 3 * P + comparisonProfileBound + (2 ^ dim : ℕ) + 32
  let tq : α := dim + Q + (P + 1) + 1
  let pq : α := K.Cgrid + (dim + 1 : ℕ) * Q + (P + 1) + 4
  let gridlog : α := slicedGridGeometryLog Dg v w tq + pq
  let Fpref : α := (P + K.Cpref) ^ K.Cpref
  let sumlog : α := Pbox + P + Vlog + Nlog + Q + P
  let idealQ : α := dim + P * sumlog + (P + comparisonProfileBound + (P + 1) * sumlog) + sumlog + 1
  let ambient : α := affineAmbientPrimitiveBudget baseAmbient idealQ
  let Psample : α := Pmass + ambient + Pproj + 2 * P +
    generalDetectorCoefficientCost K.m dim + (P + (K.m + dim + 2 : ℕ)) ^ (K.m + dim + 2) + 8
  let Pside : α := Psample + Pproj + Pmass + 2 * L
  let Pnative : α := Dg + gridlog + v + Fpref + 6 * P + Banalytic
  let nativeBudget : α := ((Pnative + K.Cnative) ^ K.Cnative + K.Anorm) ^ K.Anorm
  let E : α := 3 * P + nativeBudget + 30
  let full : α := 4 * (L + 8) ^ 2
  let required : α := (Psample + K.Apert) ^ K.Apert + (Pmass + K.AmassWindow) ^ K.AmassWindow + (Pproj + K.Aproj) ^ K.Aproj + (Pside + K.Aside) ^ K.Aside + (full + E + K.Amarginal) ^ K.Amarginal
  { Q, v, w, Dg, Pproj, coverLog, Pmass, Vlog, Nlog, Pbox, Banalytic, baseAmbient, tq, pq, gridlog, Fpref, sumlog, idealQ, ambient, Psample, Pside, Pnative, nativeBudget, E, full, required }

private theorem generalResources_map {α β : Type*} [Semiring α] [Semiring β]
    (f : α →+* β) (K : PreparedModularCanonicalDetectorResourceConstants)
    (dim : ℕ) (P L : α) :
    (preparedModularGeneralDetectorResources K dim P L).map f =
      preparedModularGeneralDetectorResources K dim (f P) (f L) := by
  simp [preparedModularGeneralDetectorResources,
    PreparedModularCanonicalDetectorResources.map, slicedGridGeometryLog,
    affineAmbientPrimitiveBudget, affineAmbientMassLog, map_ofNat]

private theorem generalResources_total_map {α β : Type*} [Semiring α] [Semiring β]
    (f : α →+* β) (r : PreparedModularCanonicalDetectorResources α) :
    (r.map f).total = f r.total := by
  simp [PreparedModularCanonicalDetectorResources.total,
    PreparedModularCanonicalDetectorResources.toList,
    PreparedModularCanonicalDetectorResources.map]

private theorem generalResources_bounds_of_list
    {r : PreparedModularCanonicalDetectorResources ℝ} {budget : ℝ}
    (h : ∀ x ∈ r.toList, x ∈ Set.Icc 0 budget) : r.Bounds budget := by
  constructor <;> apply h <;>
    simp only [PreparedModularCanonicalDetectorResources.toList, List.mem_cons] <;> tauto

private theorem natMv_eval_nonneg {ι : Type*} (p : MvPolynomial ι ℕ)
    {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i) :
    0 ≤ p.eval₂ (Nat.castRingHom ℝ) x := by
  induction p using MvPolynomial.induction_on with
  | C n => simp only [MvPolynomial.eval₂_C]; exact Nat.cast_nonneg _
  | add p q hp hq => simpa only [MvPolynomial.eval₂_add] using add_nonneg hp hq
  | mul_X p i hp =>
    simpa only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X] using mul_nonneg hp (hx i)

private theorem natMv_eval_mono {ι : Type*} (p : MvPolynomial ι ℕ)
    {x y : ι → ℝ} (hx : ∀ i, 0 ≤ x i) (hxy : ∀ i, x i ≤ y i) :
    p.eval₂ (Nat.castRingHom ℝ) x ≤ p.eval₂ (Nat.castRingHom ℝ) y := by
  have hy (i) : 0 ≤ y i := (hx i).trans (hxy i)
  induction p using MvPolynomial.induction_on with
  | C n => simp only [MvPolynomial.eval₂_C, le_refl]
  | add p q hp hq => simpa only [MvPolynomial.eval₂_add] using add_le_add hp hq
  | mul_X p i hp =>
    simpa only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X] using
      mul_le_mul hp (hxy i) (hx i) (natMv_eval_nonneg p hy)

theorem exists_preparedModularGeneralDetector_resource_budget
    (K : PreparedModularCanonicalDetectorResourceConstants) (dim : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {P L : ℝ}, 0 ≤ P → P ≤ L →
      let resources := preparedModularGeneralDetectorResources K dim P L
      resources.Bounds ((P + L + C) ^ C) ∧ resources.total ≤ (P + L + C) ^ C := by
  let diagonal := preparedModularGeneralDetectorResources K dim
    (Polynomial.X : Polynomial ℕ) Polynomial.X
  let bivariate := preparedModularGeneralDetectorResources K dim
    (MvPolynomial.X false : MvPolynomial Bool ℕ) (MvPolynomial.X true)
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget diagonal.total
  refine ⟨C, hC, ?_⟩
  intro P L hP hPL resources
  have hL : 0 ≤ L := hP.trans hPL
  let values : Bool → ℝ := fun b => if b then L else P
  let ev : MvPolynomial Bool ℕ →+* ℝ := MvPolynomial.eval₂Hom (Nat.castRingHom ℝ) values
  let evSum : MvPolynomial Bool ℕ →+* ℝ := MvPolynomial.eval₂Hom (Nat.castRingHom ℝ) (fun _ => P + L)
  let evDiag : Polynomial ℕ →+* ℝ := Polynomial.eval₂RingHom (Nat.castRingHom ℝ) (P + L)
  have hmap : bivariate.map ev = resources := by
    simpa [bivariate, resources, ev, values] using
      generalResources_map ev K dim (MvPolynomial.X false) (MvPolynomial.X true)
  have hmapSum : bivariate.map evSum = preparedModularGeneralDetectorResources K dim (P + L) (P + L) := by
    simpa [bivariate, evSum] using
      generalResources_map evSum K dim (MvPolynomial.X false) (MvPolynomial.X true)
  have hmapDiag : diagonal.map evDiag = preparedModularGeneralDetectorResources K dim (P + L) (P + L) := by
    simpa [diagonal, evDiag] using generalResources_map evDiag K dim Polynomial.X Polynomial.X
  have hvalues (i) : 0 ≤ values i := by cases i <;> assumption
  have hdom (i) : values i ≤ P + L := by cases i <;> dsimp [values] <;> linarith
  have hmono : resources.total ≤ (preparedModularGeneralDetectorResources K dim (P + L) (P + L)).total := by
    rw [← hmap, ← hmapSum, generalResources_total_map, generalResources_total_map]
    exact natMv_eval_mono bivariate.total hvalues hdom
  have htotal : resources.total ≤ (P + L + C) ^ C := by
    apply hmono.trans
    rw [← hmapDiag, generalResources_total_map]
    exact hbound (P + L) (add_nonneg hP hL)
  have hnonneg : ∀ x ∈ resources.toList, 0 ≤ x := by
    rw [← hmap]
    change ∀ x ∈ bivariate.toList.map ev, 0 ≤ x
    intro x hx
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hx
    exact natMv_eval_nonneg q hvalues
  refine ⟨generalResources_bounds_of_list ?_, htotal⟩
  intro x hx
  exact ⟨hnonneg x hx, (List.single_le_sum hnonneg x hx).trans htotal⟩

theorem preparedModularGeneralDetectorResources_nativeBudget_eq
    {α : Type*} [Semiring α] (K : PreparedModularCanonicalDetectorResourceConstants)
    (dim : ℕ) (P L L' : α) :
    (preparedModularGeneralDetectorResources K dim P L).nativeBudget =
      (preparedModularGeneralDetectorResources K dim P L').nativeBudget := rfl

theorem preparedModularGeneralDetectorResources_early_fields_eq
    {α : Type*} [Semiring α] (K : PreparedModularCanonicalDetectorResourceConstants)
    (dim : ℕ) (P L L' : α) :
    let r := preparedModularGeneralDetectorResources K dim P L
    let r' := preparedModularGeneralDetectorResources K dim P L'
    r.Nlog = r'.Nlog ∧ r.gridlog = r'.gridlog ∧ r.Pnative = r'.Pnative ∧ r.E = r'.E :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem generalDetectorCoefficientCost_single (m dim : ℕ) (j : Fin m) :
    Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) ≤
      generalDetectorCoefficientCost m dim := by
  exact Finset.single_le_sum (f := fun j : Fin m =>
    Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)

theorem preparedModularGeneralDetectorResources_primitive_domination
    (K : PreparedModularCanonicalDetectorResourceConstants) (dim : ℕ)
    {P L : ℝ} (hP : 0 ≤ P) (hPL : P ≤ L) :
    let r := preparedModularGeneralDetectorResources K dim P L
    P ≤ r.v ∧ P ≤ r.Dg ∧ P ≤ r.Pnative ∧
    (generalDetectorCoefficientCost K.m dim : ℝ) ≤ r.Psample ∧
    r.Pmass ≤ r.Psample ∧ r.ambient ≤ r.Psample ∧ r.Pproj ≤ r.Psample ∧
    r.Psample ≤ r.Pside ∧ L ≤ r.Pside ∧
    ∀ j : Fin K.m, (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ) ≤
      Real.exp r.Psample := by
  intro r
  have hL := hP.trans hPL
  have h := ((Classical.choose_spec
    (exists_preparedModularGeneralDetector_resource_budget K dim)).2 hP hPL).1
  have hv : P ≤ r.v := by change P ≤ P + 8; linarith
  have hD : P ≤ r.Dg := by
    have hrest : 0 ≤ (K.m : ℝ) * P + (layerTailDegree K.m + 1 : ℕ) +
        K.m + comparisonProfileBound + 8 := by positivity
    change P ≤ 2 * P + K.m * P + (layerTailDegree K.m + 1 : ℕ) + K.m + comparisonProfileBound + 8
    linarith only [hP, hrest]
  have hN : P ≤ r.Pnative := by
    change P ≤ r.Dg + r.gridlog + r.v + r.Fpref + 6 * P + r.Banalytic
    linarith only [hv, h.Dg.1, h.gridlog.1, h.Fpref.1, h.Banalytic.1, hP]
  have hpow : 0 ≤ (P + (K.m + dim + 2 : ℕ)) ^ (K.m + dim + 2) := by positivity
  have hcost0 : (0 : ℝ) ≤ generalDetectorCoefficientCost K.m dim := Nat.cast_nonneg _
  have hsample : r.Psample = r.Pmass + r.ambient + r.Pproj + 2 * P +
      generalDetectorCoefficientCost K.m dim + (P + (K.m + dim + 2 : ℕ)) ^ (K.m + dim + 2) + 8 := rfl
  have hcost : (generalDetectorCoefficientCost K.m dim : ℝ) ≤ r.Psample := by
    linarith only [hsample, h.Pmass.1, h.ambient.1, h.Pproj.1, hP, hpow]
  have hside : r.Pside = r.Psample + r.Pproj + r.Pmass + 2 * L := rfl
  refine ⟨hv, hD, hN, hcost, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith only [hsample, h.ambient.1, h.Pproj.1, hP, hcost0, hpow]
  · linarith only [hsample, h.Pmass.1, h.Pproj.1, hP, hcost0, hpow]
  · linarith only [hsample, h.Pmass.1, h.ambient.1, hP, hcost0, hpow]
  · linarith only [hside, h.Pproj.1, h.Pmass.1, hL]
  · linarith only [hside, h.Psample.1, h.Pproj.1, h.Pmass.1, hL]
  · intro j
    exact (Nat.cast_le.mpr (generalDetectorCoefficientCost_single K.m dim j)).trans
      (hcost.trans (by linarith only [Real.add_one_le_exp r.Psample]))

theorem exists_preparedModularGeneralDetector_early_native_budget
    (K : PreparedModularCanonicalDetectorResourceConstants) (dim : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {P : ℝ}, 0 ≤ P → ∀ L : ℝ,
      let r := preparedModularGeneralDetectorResources K dim P L
      r.Pnative ∈ Set.Icc 0 ((2 * P + C) ^ C) ∧
      r.nativeBudget ∈ Set.Icc 0 ((2 * P + C) ^ C) ∧
      r.E ∈ Set.Icc 0 ((2 * P + C) ^ C) := by
  obtain ⟨C, hC, hbound⟩ := exists_preparedModularGeneralDetector_resource_budget K dim
  refine ⟨C, hC, ?_⟩
  intro P hP L r
  have h := (hbound (P := P) (L := P) hP le_rfl).1
  change (preparedModularGeneralDetectorResources K dim P P).Pnative ∈ _ ∧
    (preparedModularGeneralDetectorResources K dim P P).nativeBudget ∈ _ ∧
    (preparedModularGeneralDetectorResources K dim P P).E ∈ _
  simpa only [two_mul] using And.intro h.Pnative (And.intro h.nativeBudget h.E)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

private theorem generalResource_nonneg
    (K : PreparedModularCanonicalDetectorResourceConstants) (dim : ℕ)
    {P L : ℝ} (hP : 0 ≤ P) (hPL : P ≤ L) :
    ∃ budget : ℝ, (preparedModularGeneralDetectorResources K dim P L).Bounds budget := by
  obtain ⟨C, _, hbound⟩ := exists_preparedModularGeneralDetector_resource_budget K dim
  exact ⟨(P + L + C) ^ C, (hbound hP hPL).1⟩

private theorem prepared_slicedGridGeometryLog_mono
    {D v w t D' v' w' t' : ℝ} (hD : 0 ≤ D) (hv : 0 ≤ v) (hw : 0 ≤ w) (ht : 0 ≤ t)
    (hDD : D ≤ D') (hvv : v ≤ v') (hww : w ≤ w') (htt : t ≤ t') :
    slicedGridGeometryLog D v w t ≤ slicedGridGeometryLog D' v' w' t' := by
  have hD' : 0 ≤ D' := hD.trans hDD
  unfold slicedGridGeometryLog
  gcongr

private theorem prepared_affineAmbientPrimitiveBudget_mono
    {base Q base' Q' : ℝ} (hb : 0 ≤ base) (hQ : 0 ≤ Q)
    (hbb : base ≤ base') (hQQ : Q ≤ Q') :
    affineAmbientPrimitiveBudget base Q ≤ affineAmbientPrimitiveBudget base' Q' := by
  have hb' : 0 ≤ base' := hb.trans hbb
  have hQ' : 0 ≤ Q' := hQ.trans hQQ
  dsimp only [affineAmbientPrimitiveBudget, affineAmbientMassLog]
  gcongr

theorem preparedModularGeneralDetector_ideal_site_bound
    (K : PreparedModularCanonicalDetectorResourceConstants) (dim : ℕ) {P L : ℝ} (hP : 0 ≤ P)
    {outputs : ℕ} (hout : (outputs : ℝ) ≤ P) {sumlog : ℝ}
    (hsum : sumlog ∈ Set.Icc 0 (preparedModularGeneralDetectorResources K dim P L).sumlog) :
    idealSiteLogBudget outputs dim sumlog ∈
      Set.Icc 0 (preparedModularGeneralDetectorResources K dim P L).idealQ := by
  let r := preparedModularGeneralDetectorResources K dim P L
  have hprofile : (probabilityProfileLipschitz : ℝ) ≤ comparisonProfileBound :=
    (Nat.le_ceil _).trans (by unfold comparisonProfileBound; push_cast; linarith)
  refine ⟨(idealSiteLogBudget_bounds outputs dim hsum.1).1, ?_⟩
  change idealSiteLogBudget outputs dim sumlog ≤
    (dim : ℝ) + P * r.sumlog + (P + comparisonProfileBound + (P + 1) * r.sumlog) + r.sumlog + 1
  unfold idealSiteLogBudget affineProfileLogBound
  have hs0 := hsum.1
  have hs1 := hsum.2
  gcongr

theorem preparedModularGeneralDetector_ambient_bound
    (K : PreparedModularCanonicalDetectorResourceConstants) (dim : ℕ) {P L : ℝ} (hP : 0 ≤ P)
    {outputs : ℕ} (hout : (outputs : ℝ) ≤ P)
    {box Prho volume normalizer mask target base : ℝ}
    (hbox : box ∈ Set.Icc 0 (preparedModularGeneralDetectorResources K dim P L).Pbox)
    (hPrho : Prho ∈ Set.Icc 0 P)
    (hvolume : volume ∈ Set.Icc 0 (preparedModularGeneralDetectorResources K dim P L).Vlog)
    (hnormalizer : normalizer ∈ Set.Icc 0 (preparedModularGeneralDetectorResources K dim P L).Nlog)
    (hmask : mask ∈ Set.Icc 0 (preparedModularGeneralDetectorResources K dim P L).Q)
    (htarget : target ∈ Set.Icc 0 P)
    (hbase : base ∈ Set.Icc 0 (preparedModularGeneralDetectorResources K dim P L).baseAmbient) :
    let site := idealSiteLogBudget outputs dim (box + Prho + volume + normalizer + mask + target)
    site ∈ Set.Icc 0 (preparedModularGeneralDetectorResources K dim P L).idealQ ∧
    affineAmbientPrimitiveBudget base site ∈
      Set.Icc 0 (preparedModularGeneralDetectorResources K dim P L).ambient := by
  intro site
  have hsum : box + Prho + volume + normalizer + mask + target ∈
      Set.Icc 0 (preparedModularGeneralDetectorResources K dim P L).sumlog := by
    constructor
    · linarith only [hbox.1, hPrho.1, hvolume.1, hnormalizer.1, hmask.1, htarget.1]
    · exact add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hbox.2 hPrho.2)
        hvolume.2) hnormalizer.2) hmask.2) htarget.2
  have hsite := preparedModularGeneralDetector_ideal_site_bound K dim hP hout hsum
  refine ⟨hsite, ⟨?_, ?_⟩⟩
  · have hb := hbase.1
    have hq := hsite.1
    dsimp only [affineAmbientPrimitiveBudget, affineAmbientMassLog]
    positivity
  · exact prepared_affineAmbientPrimitiveBudget_mono hbase.1 hsite.1 hbase.2 hsite.2

theorem preparedModularGeneralDetector_grid_bound
    (K : PreparedModularCanonicalDetectorResourceConstants) (dim : ℕ) {P L pDetect qlog : ℝ}
    (hP : 0 ≤ P) (hPL : P ≤ L) (hp : pDetect ∈ Set.Icc 0 P)
    (hq : qlog ∈ Set.Icc 0 (preparedModularGeneralDetectorResources K dim P L).Q) :
    let r := preparedModularGeneralDetectorResources K dim P L
    let tg := (dim : ℝ) + qlog + (pDetect + 1) + 1
    let pg := (K.Cgrid : ℝ) + ((dim + 1 : ℕ) : ℝ) * qlog + (pDetect + 1) + 4
    slicedGridGeometryLog r.Dg r.v (pDetect + 1) tg + pg ∈ Set.Icc 0 r.gridlog := by
  intro r tg pg
  obtain ⟨_, h⟩ := generalResource_nonneg K dim hP hPL
  have ht : tg ∈ Set.Icc 0 r.tq := by
    change 0 ≤ (dim : ℝ) + qlog + (pDetect + 1) + 1 ∧
      (dim : ℝ) + qlog + (pDetect + 1) + 1 ≤ (dim : ℝ) + r.Q + (P + 1) + 1
    constructor <;> linarith only [hq.1, hq.2, hp.1, hp.2, Nat.cast_nonneg (α := ℝ) dim]
  have hg : pg ∈ Set.Icc 0 r.pq := by
    change 0 ≤ (K.Cgrid : ℝ) + ((dim + 1 : ℕ) : ℝ) * qlog + (pDetect + 1) + 4 ∧
      (K.Cgrid : ℝ) + ((dim + 1 : ℕ) : ℝ) * qlog + (pDetect + 1) + 4 ≤ K.Cgrid + ((dim + 1 : ℕ) : ℝ) * r.Q + (P + 1) + 4
    have hq0 := mul_nonneg (Nat.cast_nonneg (α := ℝ) (dim + 1)) hq.1
    have hq1 := mul_le_mul_of_nonneg_left hq.2 (Nat.cast_nonneg (α := ℝ) (dim + 1))
    constructor <;> linarith only [hq0, hq1, hp.1, hp.2, Nat.cast_nonneg (α := ℝ) K.Cgrid]
  have hw : 0 ≤ pDetect + 1 := by linarith only [hp.1]
  constructor
  · have hD := h.Dg.1
    have hv := h.v.1
    have ht0 := ht.1
    have hg0 := hg.1
    unfold slicedGridGeometryLog
    positivity
  · exact add_le_add
      (prepared_slicedGridGeometryLog_mono h.Dg.1 h.v.1 hw ht.1 le_rfl le_rfl
        (by change pDetect + 1 ≤ P + 1; linarith only [hp.2]) ht.2) hg.2

theorem preparedModularGeneralDetector_grid_resource_width_bound
    (K : PreparedModularCanonicalDetectorResourceConstants) (dim : ℕ) {P L pDetect qlog : ℝ}
    (hP : 0 ≤ P) (hPL : P ≤ L) (hp : pDetect ∈ Set.Icc 0 P)
    (hq : qlog ∈ Set.Icc 0 (preparedModularGeneralDetectorResources K dim P L).Q) :
    let r := preparedModularGeneralDetectorResources K dim P L
    let tg := (dim : ℝ) + qlog + (pDetect + 1) + 1
    let pg := (K.Cgrid : ℝ) + ((dim + 1 : ℕ) : ℝ) * qlog + (pDetect + 1) + 4
    slicedGridGeometryLog r.Dg r.v r.w tg + pg ∈ Set.Icc 0 r.gridlog := by
  intro r tg pg
  obtain ⟨_, h⟩ := generalResource_nonneg K dim hP hPL
  have ht : tg ∈ Set.Icc 0 r.tq := by
    change 0 ≤ (dim : ℝ) + qlog + (pDetect + 1) + 1 ∧
      (dim : ℝ) + qlog + (pDetect + 1) + 1 ≤ (dim : ℝ) + r.Q + (P + 1) + 1
    constructor <;> linarith only [hq.1, hq.2, hp.1, hp.2, Nat.cast_nonneg (α := ℝ) dim]
  have hg : pg ∈ Set.Icc 0 r.pq := by
    change 0 ≤ (K.Cgrid : ℝ) + ((dim + 1 : ℕ) : ℝ) * qlog + (pDetect + 1) + 4 ∧
      (K.Cgrid : ℝ) + ((dim + 1 : ℕ) : ℝ) * qlog + (pDetect + 1) + 4 ≤ K.Cgrid + ((dim + 1 : ℕ) : ℝ) * r.Q + (P + 1) + 4
    have hq0 := mul_nonneg (Nat.cast_nonneg (α := ℝ) (dim + 1)) hq.1
    have hq1 := mul_le_mul_of_nonneg_left hq.2 (Nat.cast_nonneg (α := ℝ) (dim + 1))
    constructor <;> linarith only [hq0, hq1, hp.1, hp.2, Nat.cast_nonneg (α := ℝ) K.Cgrid]
  have hw : 0 ≤ r.w := h.w.1
  constructor
  · have hD := h.Dg.1
    have hv := h.v.1
    have ht0 := ht.1
    have hg0 := hg.1
    unfold slicedGridGeometryLog
    positivity
  · exact add_le_add
      (prepared_slicedGridGeometryLog_mono h.Dg.1 h.v.1 hw ht.1 le_rfl le_rfl le_rfl ht.2) hg.2

theorem preparedModularGeneralDetector_native_inputs
    (K : PreparedModularCanonicalDetectorResourceConstants) (dim : ℕ) {P L : ℝ} (hP : 0 ≤ P) (hPL : P ≤ L) :
    let r := preparedModularGeneralDetectorResources K dim P L
    r.Dg ∈ Set.Icc 0 r.Pnative ∧ r.gridlog ∈ Set.Icc 0 r.Pnative ∧
    r.v ∈ Set.Icc 0 r.Pnative ∧ r.Fpref ∈ Set.Icc 0 r.Pnative ∧
    r.Banalytic ∈ Set.Icc 0 r.Pnative ∧ P ≤ r.Pnative ∧
    ∀ a ∈ Set.Icc (0 : ℝ) P, a ∈ Set.Icc 0 r.Pnative := by
  intro r
  obtain ⟨_, h⟩ := generalResource_nonneg K dim hP hPL
  have hD := h.Dg.1
  have hg := h.gridlog.1
  have hv := h.v.1
  have hf := h.Fpref.1
  have hb := h.Banalytic.1
  have heq : r.Pnative = r.Dg + r.gridlog + r.v + r.Fpref + 6 * P + r.Banalytic := rfl
  have hpv : P ≤ r.v := by change P ≤ P + 8; linarith
  have hPnative : P ≤ r.Pnative := by linarith only [heq, hpv, hD, hg, hf, hb, hP]
  refine ⟨⟨hD, ?_⟩, ⟨hg, ?_⟩, ⟨hv, ?_⟩, ⟨hf, ?_⟩, ⟨hb, ?_⟩, hPnative, ?_⟩
  all_goals first | linarith only [heq, hD, hg, hv, hf, hb, hP] |
    exact fun a ha => ⟨ha.1, ha.2.trans hPnative⟩

theorem preparedModularGeneralDetector_final_error_bound
    (K : PreparedModularCanonicalDetectorResourceConstants) (dim : ℕ) {P L u pModel : ℝ}
    (hu : u ≤ P) (hpModel : pModel ≤ P) :
    u + 2 * pModel + (preparedModularGeneralDetectorResources K dim P L).nativeBudget + 30 ≤
      (preparedModularGeneralDetectorResources K dim P L).E := by
  let r := preparedModularGeneralDetectorResources K dim P L
  have hE : r.E = 3 * P + r.nativeBudget + 30 := rfl
  change u + 2 * pModel + r.nativeBudget + 30 ≤ r.E
  rw [hE]
  linarith only [hu, hpModel]

theorem preparedModularGeneralDetector_native_budget_mono
    (K : PreparedModularCanonicalDetectorResourceConstants) (dim : ℕ) {P L native : ℝ}
    (hn : native ∈ Set.Icc 0 (preparedModularGeneralDetectorResources K dim P L).Pnative) :
    ((native + K.Cnative) ^ K.Cnative + K.Anorm) ^ K.Anorm ≤
      (preparedModularGeneralDetectorResources K dim P L).nativeBudget := by
  change ((native + K.Cnative) ^ K.Cnative + K.Anorm) ^ K.Anorm ≤
    (((preparedModularGeneralDetectorResources K dim P L).Pnative + K.Cnative) ^ K.Cnative +
      K.Anorm) ^ K.Anorm
  have hn0 := hn.1
  have hn1 := hn.2
  gcongr

theorem preparedModularGeneralDetector_required_bounds
    (K : PreparedModularCanonicalDetectorResourceConstants) (dim : ℕ) {P L : ℝ} (hP : 0 ≤ P) (hPL : P ≤ L) :
    let r := preparedModularGeneralDetectorResources K dim P L
    (r.Psample + K.Apert) ^ K.Apert ≤ r.required ∧
    (r.Pmass + K.AmassWindow) ^ K.AmassWindow ≤ r.required ∧
    (r.Pproj + K.Aproj) ^ K.Aproj ≤ r.required ∧
    (r.Pside + K.Aside) ^ K.Aside ≤ r.required ∧
    (r.full + r.E + K.Amarginal) ^ K.Amarginal ≤ r.required := by
  intro r
  obtain ⟨_, h⟩ := generalResource_nonneg K dim hP hPL
  have hs := h.Psample.1
  have hm := h.Pmass.1
  have hp := h.Pproj.1
  have hside := h.Pside.1
  have hf := h.full.1
  have he := h.E.1
  have h1 : 0 ≤ (r.Psample + K.Apert) ^ K.Apert := by positivity
  have h2 : 0 ≤ (r.Pmass + K.AmassWindow) ^ K.AmassWindow := by positivity
  have h3 : 0 ≤ (r.Pproj + K.Aproj) ^ K.Aproj := by positivity
  have h4 : 0 ≤ (r.Pside + K.Aside) ^ K.Aside := by positivity
  have h5 : 0 ≤ (r.full + r.E + K.Amarginal) ^ K.Amarginal := by positivity
  have hsum : r.required = (r.Psample + K.Apert) ^ K.Apert +
      (r.Pmass + K.AmassWindow) ^ K.AmassWindow + (r.Pproj + K.Aproj) ^ K.Aproj +
      (r.Pside + K.Aside) ^ K.Aside + (r.full + r.E + K.Amarginal) ^ K.Amarginal := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith only [hsum, h1, h2, h3, h4, h5]

end Erdos3.VectorPolynomial

end

end OAI
