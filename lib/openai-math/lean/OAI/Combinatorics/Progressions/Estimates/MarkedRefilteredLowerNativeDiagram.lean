import OAI.Combinatorics.Progressions.Dynamics.AllocatedMarkedCoveredLowerDiagramBudget
import OAI.Combinatorics.Progressions.Dynamics.MarkedRefilteredModelBudget
import OAI.Combinatorics.Progressions.Dynamics.NativeMarkedQuotientHeightBudget
import OAI.Combinatorics.Progressions.Estimates.AdaptedDiagramNativeExternalNet
import OAI.Combinatorics.Progressions.Linear.ActualOrdinaryPointwiseSpanning

namespace OAI


namespace Erdos3

open Module

variable {L M ι κ α β : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] [Fintype ι] [Fintype κ] [Fintype β]

theorem restrictedLieMap_coordinate_logHeight
    (e : Basis ι ℚ L) (f : Basis κ ℚ M)
    (U : LieSubalgebra ℚ L) (V : LieSubalgebra ℚ M)
    (b : Basis α ℚ U) (c : Basis β ℚ V)
    (φ : L →ₗ⁅ℚ⁆ M) (hUV : ∀ x ∈ U, φ x ∈ V)
    {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hβ : (Fintype.card β : ℝ) ≤ p)
    (hφ : ∀ i j, rationalLogHeight (f.repr (φ (e i)) j) ≤ p)
    (hb : ∀ i j, rationalLogHeight (e.repr (b i : L) j) ≤ p)
    (hc : ∀ i j, rationalLogHeight (f.repr (c i : M) j) ≤ p)
    (i : α) (j : β) :
    rationalLogHeight (c.repr ⟨φ (b i), hUV _ (b i).property⟩ j) ≤
      ((p + 2) ^ 4 + p + 4) ^ 8 := by
  let q := (p + 2) ^ 4 + p + 1
  have hp4 : 0 ≤ (p + 2) ^ 4 := by positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hp4q : (p + 2) ^ 4 ≤ q := by dsimp [q]; linarith
  have hq : 0 ≤ q := hp.trans hpq
  have himage (k : κ) : rationalLogHeight (f.repr (φ (b i)) k) ≤ q :=
    (linearMap_coordinate_logHeight e f φ.toLinearMap hp hι hφ (b i) (hb i) k).trans hp4q
  let x : V := ⟨φ (b i), hUV _ (b i).property⟩
  apply rationalLogHeight_le_of_height
    (embedding_basis_coordinate_height c f V.incl.toLinearMap
      (fun _ _ h => Subtype.ext h) (one_le_ceil_exp q)
      (fun k l => rationalHeightLE_ceil_exp ((hc l k).trans hpq)) x
      (fun k => rationalHeightLE_ceil_exp (himage k)) j)
  have hraw := embedding_coordinate_height_budget (Fintype.card κ) (Fintype.card β)
    ⌈Real.exp q⌉₊ ⌈Real.exp q⌉₊ (show 0 ≤ q + 1 by linarith)
    (hκ.trans (hpq.trans (by linarith))) (hβ.trans (hpq.trans (by linarith)))
    (ceil_exp_le_exp_add_one hq) (ceil_exp_le_exp_add_one hq)
  convert hraw using 1
  dsimp [q]
  congr 2
  ring

end Erdos3


namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieFiltration

theorem exists_controlled_marked_top_quotient :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M : Type*}
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      {s d e n : ℕ}
      (D : RationalFilteredNilmanifold L (s + 1) d)
      (E : RationalFilteredNilmanifold M (s + 1) e)
      (φ : L →ₗ⁅ℚ⁆ M)
      (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ E.filtration.layer j)
      (Q : RationalFilteredNilmanifold (L ⧸ D.filtration.layerIdeal (s + 1)) s n)
      (_hQ : Q.filtration = D.filtration.quotientTop),
      (∀ j, ∀ y ∈ E.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y) →
      ∀ {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      Q.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (Q.basis.repr
        (lieQuotientMap (D.filtration.layerIdeal (s + 1)) (D.basis j)) i) ≤ p) →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis i)) j) ≤ p) →
      ∃ m : ℕ, m ≤ e ∧
        ∃ QF : RationalFilteredNilmanifold (M ⧸ E.filtration.layerIdeal (s + 1)) s m,
          QF.filtration = E.filtration.quotientTop ∧
          QF.lattice = E.lattice.map
            (E.filtration.quotientStepHom (E.filtration.layerIdeal (s + 1)) le_rfl) ∧
          QF.GeometryComplexityLE ((p + C) ^ C) ∧
          (∀ i j, rationalLogHeight (QF.basis.repr
            (lieQuotientMap (E.filtration.layerIdeal (s + 1)) (E.basis j)) i) ≤
              (p + C) ^ C) ∧
          (∀ i j, rationalLogHeight
            (QF.basis.repr (D.topQuotientMarkedMap E φ hφ (Q.basis i)) j) ≤
              (p + C) ^ C) ∧
          (∀ j, ∀ x ∈ Q.filtration.layer j,
            D.topQuotientMarkedMap E φ hφ x ∈ QF.filtration.layer j) ∧
          ∀ j, ∀ y ∈ QF.filtration.layer j, ∃ x ∈ Q.filtration.layer j,
            D.topQuotientMarkedMap E φ hφ x = y := by
  obtain ⟨C, hC, hbudget⟩ := exists_nativeMarkedQuotientHeightBudget 11
  refine ⟨C, hC, ?_⟩
  intro L M _ _ _ _ s d e n D E φ hφ Q hQ hsurj p hp hD hE hQgeom hproj hmark
  obtain ⟨m, hm, QF, hQF, hQFL, hQFgeom, hprojF, _⟩ :=
    E.exists_controlled_top_quotient hp hE
  have hpA : p ≤ (p + 11) ^ 11 := by
    calc
      p ≤ (p + 2) ^ 11 := le_power_budget hp (by decide)
      _ ≤ (p + 11) ^ 11 := by gcongr; norm_num
  have hgeoA : (p + 3) ^ 11 ≤ (p + 11) ^ 11 := by gcongr; norm_num
  have hprojA : (p + 3) ^ 5 ≤ (p + 11) ^ 11 := by
    calc
      (p + 3) ^ 5 ≤ (p + 3) ^ 11 :=
        pow_le_pow_right₀ (by linarith) (by decide)
      _ ≤ (p + 11) ^ 11 := hgeoA
  obtain ⟨hAC, hmapC⟩ := hbudget p hp
  refine ⟨m, hm, QF, hQF, hQFL, hQFgeom.mono QF (hgeoA.trans hAC),
    (fun i j => (hprojF j i).trans (hprojA.trans hAC)), ?_, ?_, ?_⟩
  · intro i j
    exact (D.topQuotientMarkedMap_basis_logHeight E φ hφ Q QF (hp.trans hpA)
      (hD.mono D hpA) (hE.mono E hpA) (hQgeom.mono Q hpA)
      (fun i j => (hproj i j).trans hpA) (fun i j => (hmark i j).trans hpA)
      (fun i j => (hprojF j i).trans hprojA) i j).trans hmapC
  · exact D.topQuotientMarkedMap_mem_layer E φ hφ Q hQ QF hQF
  · exact D.topQuotientMarkedMap_layer_surjective E φ hφ Q hQ QF hQF hsurj

end Erdos3.RationalFilteredNilmanifold


namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

theorem exists_controlled_refiltered_marked_top_quotient :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M ι κ : Type*}
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      {s d f nD nF nQ : ℕ}
      (D : RationalFilteredNilmanifold L (s + 1) d)
      (Fmark : RationalFilteredNilmanifold M (s + 1) f)
      (φ : L →ₗ⁅ℚ⁆ M)
      (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
      (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
      (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hD : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (c : Basis κ ℚ M) (ν : κ → ℕ)
      (_hF : ∀ j, Fmark.filtration.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i})),
      BasisGradedSubmodule (D.filtration.associatedGradedBasis b ω hD) ω W.toSubmodule →
      (∀ j, ∀ y ∈ Fmark.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y) →
      ∀ (Dref : RationalFilteredNilmanifold
          (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)
        (hDref : Dref.filtration = D.filtration.gradedRefiltration W)
        (Fref : RationalFilteredNilmanifold
          (Fmark.filtration.gradedRefiltrationSubalgebra
            (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
        (hFref : Fref.filtration = Fmark.filtration.gradedRefiltration
          (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))
        (Q : RationalFilteredNilmanifold
          ((D.filtration.gradedRefiltrationSubalgebra W) ⧸
            Dref.filtration.layerIdeal (s + 1)) s nQ)
        (_hQ : Q.filtration = Dref.filtration.quotientTop)
        {p : ℝ},
        0 ≤ p → Dref.GeometryComplexityLE p → Fref.GeometryComplexityLE p →
        Q.GeometryComplexityLE p →
        (∀ i j, rationalLogHeight (Q.basis.repr
          (lieQuotientMap (Dref.filtration.layerIdeal (s + 1)) (Dref.basis j)) i) ≤ p) →
        (∀ i j, rationalLogHeight (Fref.basis.repr
          (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W (Dref.basis i)) j) ≤ p) →
        let mark := D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W
        let hmark := D.refilteredMarkedMap_mem_layer Fmark φ hφ W Dref hDref Fref hFref
        ∃ m : ℕ, m ≤ nF ∧
          ∃ QF : RationalFilteredNilmanifold
              ((Fmark.filtration.gradedRefiltrationSubalgebra
                (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) ⧸
                Fref.filtration.layerIdeal (s + 1)) s m,
            QF.filtration = Fref.filtration.quotientTop ∧
            QF.lattice = Fref.lattice.map
              (Fref.filtration.quotientStepHom (Fref.filtration.layerIdeal (s + 1)) le_rfl) ∧
            QF.GeometryComplexityLE ((p + C) ^ C) ∧
            (∀ i j, rationalLogHeight (QF.basis.repr
              (lieQuotientMap (Fref.filtration.layerIdeal (s + 1)) (Fref.basis j)) i) ≤
                (p + C) ^ C) ∧
            (∀ i j, rationalLogHeight
              (QF.basis.repr (Dref.topQuotientMarkedMap Fref mark hmark (Q.basis i)) j) ≤
                (p + C) ^ C) ∧
            (∀ j, ∀ x ∈ Q.filtration.layer j,
              Dref.topQuotientMarkedMap Fref mark hmark x ∈ QF.filtration.layer j) ∧
            ∀ j, ∀ y ∈ QF.filtration.layer j, ∃ x ∈ Q.filtration.layer j,
              Dref.topQuotientMarkedMap Fref mark hmark x = y := by
  obtain ⟨C, hC, hconstruct⟩ := exists_controlled_marked_top_quotient
  refine ⟨C, hC, ?_⟩
  intro L M ι κ _ _ _ _ s d f nD nF nQ D Fmark φ hφ W b ω hD c ν hF hW
    hsurj Dref hDref Fref hFref Q hQ p hp hDgeom hFgeom hQgeom hproj hmark
  exact hconstruct Dref Fref
    (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W)
    (D.refilteredMarkedMap_mem_layer Fmark φ hφ W Dref hDref Fref hFref) Q hQ
    (D.refilteredMarkedMap_layer_surjective Fmark φ hφ W Dref hDref Fref hFref
      b ω hD c ν hF hW hsurj) hp hDgeom hFgeom hQgeom hproj hmark

end Erdos3.RationalFilteredNilmanifold


namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

universe u

def MarkedRefilteredNativeDiagramData
    {L M : Type u} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d f : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d)
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded) (P : ℝ) : Prop :=
      let V := W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)
      let mark := D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W
      ∃ E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra W) (s + 1)
          (finrank ℚ (D.filtration.gradedRefiltrationSubalgebra W)),
        E.filtration = D.filtration.gradedRefiltration W ∧
        E.lattice = D.lattice.comap
          (NilpotentLieBCHGroup.map
            (hnil := (D.filtration.gradedRefiltration W).lowerCentralSeries_eq_bot)
            (D.filtration.gradedRefiltrationSubalgebra W).incl) ∧
        E.GeometryComplexityLE (P) ∧
        (∀ i j, rationalLogHeight (D.basis.repr (E.basis j : L) i) ≤ P) ∧
        ∃ EF : RationalFilteredNilmanifold (Fmark.filtration.gradedRefiltrationSubalgebra V) (s + 1)
            (finrank ℚ (Fmark.filtration.gradedRefiltrationSubalgebra V)),
          EF.filtration = Fmark.filtration.gradedRefiltration V ∧
          EF.lattice = Fmark.lattice.comap
            (NilpotentLieBCHGroup.map
              (hnil := (Fmark.filtration.gradedRefiltration V).lowerCentralSeries_eq_bot)
              (Fmark.filtration.gradedRefiltrationSubalgebra V).incl) ∧
          EF.GeometryComplexityLE (P) ∧
          (∀ i j, rationalLogHeight (Fmark.basis.repr (EF.basis j : M) i) ≤ P) ∧
          (∀ i j, rationalLogHeight (EF.basis.repr (mark (E.basis i)) j) ≤ P) ∧
          (∀ j, ∀ x ∈ E.filtration.layer j, mark x ∈ EF.filtration.layer j) ∧
          (∀ j, ∀ y ∈ EF.filtration.layer j, ∃ x ∈ E.filtration.layer j, mark x = y) ∧
          (∃ m : ℕ, m ≤ finrank ℚ (D.filtration.gradedRefiltrationSubalgebra W) ∧
            ∃ Q : RationalFilteredNilmanifold
                ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s m,
              Q.filtration = E.filtration.quotientTop ∧
              Q.lattice = E.lattice.map
                (E.filtration.quotientStepHom (E.filtration.layerIdeal (s + 1)) le_rfl) ∧
              Q.GeometryComplexityLE (P) ∧
              ∀ i j, rationalLogHeight (Q.basis.repr
                (lieQuotientMap (E.filtration.layerIdeal (s + 1)) (E.basis j)) i) ≤ P) ∧
          (∃ m : ℕ, m ≤ finrank ℚ (Fmark.filtration.gradedRefiltrationSubalgebra V) ∧
            ∃ QF : RationalFilteredNilmanifold
                ((Fmark.filtration.gradedRefiltrationSubalgebra V) ⧸ EF.filtration.layerIdeal (s + 1)) s m,
              QF.filtration = EF.filtration.quotientTop ∧
              QF.lattice = EF.lattice.map
                (EF.filtration.quotientStepHom (EF.filtration.layerIdeal (s + 1)) le_rfl) ∧
              QF.GeometryComplexityLE (P) ∧
              ∀ i j, rationalLogHeight (QF.basis.repr
                (lieQuotientMap (EF.filtration.layerIdeal (s + 1)) (EF.basis j)) i) ≤ P)

theorem exists_marked_refiltered_native_diagram :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {L M : Type u} {κ : Type*} [LieRing L] [LieAlgebra ℚ L]
      [LieRing M] [LieAlgebra ℚ M] [Fintype κ]
      {s d f n k : ℕ}
      (D : RationalFilteredNilmanifold L (s + 1) d)
      (Fmark : RationalFilteredNilmanifold M (s + 1) f)
      (b : Basis (Fin n) ℚ L) (ω : Fin n → ℕ)
      (hD : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (c : Basis (Fin k) ℚ M) (ν : Fin k → ℕ)
      (_hF : ∀ j, Fmark.filtration.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
      (φ : L →ₗ⁅ℚ⁆ M)
      (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j),
      (∀ j, ∀ y ∈ Fmark.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y) →
    ∀ (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
      (v : κ → D.filtration.AssociatedGraded),
      Submodule.span ℚ (Set.range v) = W.toSubmodule →
      BasisGradedSubmodule (D.filtration.associatedGradedBasis b ω hD) ω W.toSubmodule →
    ∀ {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p → Fmark.GeometryComplexityLE p →
      (Fintype.card κ : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (D.basis.repr (b i) j) ≤ p) →
      (∀ i j, rationalLogHeight (Fmark.basis.repr (c i) j) ≤ p) →
      (∀ i j, rationalLogHeight (Fmark.basis.repr (φ (D.basis i)) j) ≤ p) →
      (∀ i j, rationalLogHeight ((D.filtration.associatedGradedBasis b ω hD).repr (v i) j) ≤ p) →
      MarkedRefilteredNativeDiagramData D Fmark φ hφ W ((p + C) ^ C) := by
  obtain ⟨A, _, hmodels⟩ := exists_adapted_single_refiltered_models
  obtain ⟨C, hC, hbudget⟩ := exists_markedRefilteredModelInput_budget A
  refine ⟨C, hC, ?_⟩
  intro L M κ _ _ _ _ _ s d f n k D Fmark b ω hD c ν hF φ hφ hsurj
    W v hspan hW p hp hDgeom hFgeom hκ hb hc hφheight hv
  obtain ⟨hq, hpq, hmapq, ht, hqt, himaget, hr, hpr, hmodelr⟩ :=
    markedRefilteredModelInput_bounds A hp
  obtain ⟨hrC, hmarkC⟩ := hbudget p hp
  have hpt := hpq.trans hqt
  have hmodelC := hmodelr.trans hrC
  have hbn : (Fintype.card (Fin n) : ℝ) ≤ p :=
    (D.basis_geometry_of_forward_height b hp hDgeom
      (fun i j => (hb i j).trans (by linarith))).1
  have hadapted (i : Fin n) (j : Fin k) :
      rationalLogHeight (c.repr (φ (b i)) j) ≤ markedRefilteredBasisInput p :=
    (D.markedMap_basisChange_logHeight Fmark b c φ.toLinearMap hp hDgeom hFgeom
      hb hc hφheight i j).trans hmapq
  let V := W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)
  let imagev : κ → Fmark.filtration.AssociatedGraded := D.filtration.gradedImageSpanningFamily Fmark.filtration φ hφ v
  obtain ⟨himage, _, himageH⟩ :=
    D.filtration.gradedImage_bounded_spanning Fmark.filtration φ hφ
      b ω hD c ν hF W v hspan hW hq (hbn.trans hpq)
      (fun i j => (hv i j).trans hpq) hadapted
  obtain ⟨E, hEF, hEL, hEgeom, hEinc, m, hm, Q, hQF, hQL, hQgeom, hQmap⟩ :=
    hmodels D b ω hD W v hspan ht (hDgeom.mono D hpt) (hκ.trans hpt)
      (fun i j => (hb i j).trans hpt) (fun i j => (hv i j).trans hpt)
  have himageSpan : Submodule.span ℚ (Set.range imagev) = V.toSubmodule := by
    with_reducible exact himage
  have htarget := by
    with_reducible exact (hmodels (L := M) (κ := κ) (s := s) (d := f) (n := k) Fmark c ν hF V imagev himageSpan (p := markedRefilteredMapInput p) ht (hFgeom.mono Fmark hpt) (hκ.trans hpt) (fun i j => (hc i j).trans hpt) (fun i j => (himageH i j).trans himaget))
  obtain ⟨EF, hEFF, hEFL, hEFgeom, hEFinc, mf, hmf, QF, hQFF, hQFL, hQFgeom, hQFmap⟩ := htarget
  let mark := D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W
  have hmarked (i) (j) : rationalLogHeight (EF.basis.repr (mark (E.basis i)) j) ≤
      (p + C) ^ C := by
    apply (restrictedLieMap_coordinate_logHeight D.basis Fmark.basis
      (D.filtration.gradedRefiltrationSubalgebra W)
      (Fmark.filtration.gradedRefiltrationSubalgebra V) E.basis EF.basis φ
      (fun x hx => D.filtration.gradedRefiltrationLayer_map_mem Fmark.filtration φ hφ W 1 x hx)
      hr (by simpa only [Fintype.card_fin] using hDgeom.1.trans hpr)
      (by simpa only [Fintype.card_fin] using hFgeom.1.trans hpr)
      (by simpa only [Fintype.card_fin] using hEFgeom.1.trans hmodelr)
      (fun i j => (hφheight i j).trans hpr)
      (fun i j => (hEinc j i).trans hmodelr)
      (fun i j => (hEFinc j i).trans hmodelr) i j).trans hmarkC
  unfold MarkedRefilteredNativeDiagramData
  refine ⟨E, hEF, hEL, hEgeom.mono E hmodelC,
    fun i j => (hEinc i j).trans hmodelC,
    EF, hEFF, hEFL, hEFgeom.mono EF hmodelC,
    fun i j => (hEFinc i j).trans hmodelC, hmarked, ?_, ?_, ?_, ?_⟩
  · intro j x hx
    rw [hEF] at hx
    rw [hEFF]
    exact D.filtration.gradedRefiltrationMap_mem_layer Fmark.filtration φ hφ W j x hx
  · intro j y hy
    rw [hEFF] at hy
    obtain ⟨x, hx, heq⟩ := D.filtration.gradedRefiltrationMap_layer_surjective
      Fmark.filtration b ω hD c ν hF φ hφ W hW hsurj j y hy
    exact ⟨x, by rwa [hEF], heq⟩
  · exact ⟨m, hm, Q, hQF, hQL, hQgeom.mono Q hmodelC,
      fun i j => (hQmap i j).trans hmodelC⟩
  · exact ⟨mf, hmf, QF, hQFF, hQFL, hQFgeom.mono QF hmodelC,
      fun i j => (hQFmap i j).trans hmodelC⟩

end Erdos3.RationalFilteredNilmanifold


section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L M : Type u} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f : ℕ}
    (D : RationalFilteredNilmanifold L (s + 1) d)
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

structure AllocatedMarkedCoveredLowerDiagram (k q : ℕ) (p cost : ℝ) where
  Dref : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra W)
    (s + 1) (finrank ℚ (D.filtration.gradedRefiltrationSubalgebra W))
  Dref_filtration : Dref.filtration = D.filtration.gradedRefiltration W
  Dref_lattice : Dref.lattice = D.lattice.comap
    (NilpotentLieBCHGroup.map
      (hnil := (D.filtration.gradedRefiltration W).lowerCentralSeries_eq_bot)
      (D.filtration.gradedRefiltrationSubalgebra W).incl)
  Dref_geometry : Dref.GeometryComplexityLE cost
  inclusion_height : ∀ i j, rationalLogHeight (D.basis.repr (Dref.basis j : L) i) ≤ cost
  Fbase : RationalFilteredNilmanifold
    (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1)
    (finrank ℚ (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))
  Fbase_filtration : Fbase.filtration = Fmark.filtration.gradedRefiltration
    (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))
  Fbase_lattice : Fbase.lattice = Fmark.lattice.comap
    (NilpotentLieBCHGroup.map
      (hnil := (Fmark.filtration.gradedRefiltration
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))).lowerCentralSeries_eq_bot)
      (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))).incl)
  nQ : ℕ
  nQ_le : nQ ≤ finrank ℚ (D.filtration.gradedRefiltrationSubalgebra W)
  Qbase : RationalFilteredNilmanifold
    ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1)) s nQ
  Qbase_filtration : Qbase.filtration = Dref.filtration.quotientTop
  Qbase_lattice : Qbase.lattice = Dref.lattice.map
    (Dref.filtration.quotientStepHom (Dref.filtration.layerIdeal (s + 1)) le_rfl)
  Fref : RationalFilteredNilmanifold
    (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1)
    (finrank ℚ (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))
  Fref_filtration : Fref.filtration = Fmark.filtration.gradedRefiltration
    (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))
  Fref_basis : Fref.basis = Fbase.basis
  Fref_lattice : Fref.lattice ≤ Fbase.lattice
  Fref_geometry : Fref.GeometryComplexityLE cost
  marked_inclusion_height : ∀ i j,
    rationalLogHeight (Fmark.basis.repr (Fref.basis j : M) i) ≤ cost
  restricted_mark_height : ∀ i j, rationalLogHeight (Fref.basis.repr
    (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W (Dref.basis i)) j) ≤ cost
  Q : RationalFilteredNilmanifold
    ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1)) s nQ
  Q_filtration : Q.filtration = Dref.filtration.quotientTop
  Q_basis : Q.basis = Qbase.basis
  Q_lattice : Q.lattice ≤ Qbase.lattice
  Q_geometry : Q.GeometryComplexityLE cost
  quotient_height : ∀ i j, rationalLogHeight (Q.basis.repr
    (lieQuotientMap (Dref.filtration.layerIdeal (s + 1)) (Dref.basis j)) i) ≤ cost
  refiltered_mark_strong : ∀ j, ∀ y ∈ Fref.filtration.layer j,
    ∃ x ∈ Dref.filtration.layer j,
      D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W x = y
  nQF : ℕ
  nQF_le : nQF ≤ finrank ℚ (Fmark.filtration.gradedRefiltrationSubalgebra
    (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))
  Fquot : RationalFilteredNilmanifold
    ((Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) ⧸
      Fref.filtration.layerIdeal (s + 1)) s nQF
  Fquot_filtration : Fquot.filtration = Fref.filtration.quotientTop
  Fquot_lattice : Fquot.lattice = Fref.lattice.map
    (Fref.filtration.quotientStepHom (Fref.filtration.layerIdeal (s + 1)) le_rfl)
  Fquot_geometry : Fquot.GeometryComplexityLE cost
  marked_quotient_height : ∀ i j, rationalLogHeight (Fquot.basis.repr
    (lieQuotientMap (Fref.filtration.layerIdeal (s + 1)) (Fref.basis j)) i) ≤ cost
  lower_mark_height : ∀ i j, rationalLogHeight (Fquot.basis.repr
    (Dref.topQuotientMarkedMap Fref
      (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W)
      (D.refilteredMarkedMap_mem_layer Fmark φ hφ W Dref Dref_filtration Fref Fref_filtration)
      (Q.basis i)) j) ≤ cost
  lower_mark_filtered : ∀ j, ∀ x ∈ Q.filtration.layer j,
    Dref.topQuotientMarkedMap Fref
      (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W)
      (D.refilteredMarkedMap_mem_layer Fmark φ hφ W Dref Dref_filtration Fref Fref_filtration)
      x ∈ Fquot.filtration.layer j
  lower_mark_strong : ∀ j, ∀ y ∈ Fquot.filtration.layer j,
    ∃ x ∈ Q.filtration.layer j, Dref.topQuotientMarkedMap Fref
      (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W)
      (D.refilteredMarkedMap_mem_layer Fmark φ hφ W Dref Dref_filtration Fref Fref_filtration)
      x = y
  pCover : ℝ
  pCover_nonneg : 0 ≤ pCover
  pCover_le : pCover ≤ cost
  recovery :
    letI := moduleTopology ℝ (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))
    letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))) :=
      IsModuleTopology.isTopologicalAddGroup ℝ _
    letI := realification_moduleTopology_t2 Fref.basis
    letI := moduleTopology ℝ (ℝ ⊗[ℚ]
      ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1)))
    letI : IsTopologicalAddGroup (ℝ ⊗[ℚ]
      ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1))) :=
      IsModuleTopology.isTopologicalAddGroup ℝ _
    letI := realification_moduleTopology_t2 Q.basis
    letI := Q.metricSpace
    letI := Fref.metricSpace
    let diagram := Dref.markedTopQuotientDiagram Fref
      (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q
    let K : ℝ≥0 := ⟨Real.exp pCover, (Real.exp_pos _).le⟩
    ∀ a r : D.RealGroup,
      (∀ i, |(D.basis.baseChange ℝ).repr a.coord i| ≤ Real.exp ((p + 2) ^ k)) →
      (D.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid q →
      ∀ (S : D.Space → ℂ) (ℓ : ℝ≥0), (ℓ : ℝ) ≤ Real.exp p →
        (letI := D.metricSpace; LipschitzWith ℓ S) →
        (∀ y, (S y).im = 0 ∧ 0 ≤ (S y).re ∧ (S y).re ≤ 1) →
        let frozen := fun x : Dref.RealGroup => S (QuotientGroup.mk
          (a * realificationMap (hnil := Dref.filtration.lowerCentralSeries_eq_bot)
            (hM := D.filtration.lowerCentralSeries_eq_bot)
            (D.filtration.gradedRefiltrationSubalgebra W).incl x * r))
        ∀ x : Dref.RealGroup,
          positiveImageSlice diagram K frozen (diagram x).2 (diagram x).1 = frozen x

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_allocated_marked_covered_lower_diagram (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M : Type u} {κ : Type*}
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] [Fintype κ]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d f nb nf : ℕ}
      (D : RationalFilteredNilmanifold L (s + 1) d)
      (Fmark : RationalFilteredNilmanifold M (s + 1) f)
      (b : Basis (Fin nb) ℚ L) (ω : Fin nb → ℕ)
      (hD : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (c : Basis (Fin nf) ℚ M) (ν : Fin nf → ℕ)
      (_hF : ∀ j, Fmark.filtration.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
      (φ : L →ₗ⁅ℚ⁆ M)
      (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j),
      (∀ j, ∀ y ∈ Fmark.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y) →
      ∀ (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
        (v : κ → D.filtration.AssociatedGraded),
      Submodule.span ℚ (Set.range v) = W.toSubmodule →
      BasisGradedSubmodule (D.filtration.associatedGradedBasis b ω hD) ω W.toSubmodule →
      ∀ {p : ℝ}, 1 ≤ p → D.GeometryComplexityLE p → Fmark.GeometryComplexityLE p →
      (Fintype.card κ : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (D.basis.repr (b i) j) ≤ p) →
      (∀ i j, rationalLogHeight (Fmark.basis.repr (c i) j) ≤ p) →
      (∀ i j, rationalLogHeight (Fmark.basis.repr (φ (D.basis i)) j) ≤ p) →
      (∀ i j, rationalLogHeight
        ((D.filtration.associatedGradedBasis b ω hD).repr (v i) j) ≤ p) →
      (∀ x : L, x ∈ D.filtration.gradedRefiltrationLayer W (s + 1) → φ x = 0 → x = 0) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
        Nonempty (AllocatedMarkedCoveredLowerDiagram D Fmark φ hφ W k q p ((p + C) ^ C)) := by
  obtain ⟨A, _, hnative⟩ := exists_marked_refiltered_native_diagram
  obtain ⟨B, _, hcover⟩ := exists_allocated_marked_diagram_recovery_covers s k
  obtain ⟨T, _, hlower⟩ := exists_controlled_marked_top_quotient
  obtain ⟨C, hC, hbudget⟩ := exists_allocatedMarkedCoveredLowerDiagramBudget A B T
  refine ⟨C, hC, ?_⟩
  intro L M κ _ _ _ _ _ _ _ _ _ d f nb nf D Fmark b ω hD c ν hF φ hφ hsurj
    W v hspan hW p hp hDgeom hFgeom hκ hb hc hφheight hv hker q hq hqp
  have hp0 : 0 ≤ p := le_trans zero_le_one hp
  let p₀ := p + (p + A) ^ A
  let pCover := (p₀ + B) ^ B
  let p₁ := p₀ + pCover
  obtain ⟨hp₀, hpp₀, hnative₀, hp₀p₁, hcover₁, hp₁C, hlowerC⟩ := hbudget p hp
  have hnativeC : (p + A) ^ A ≤ (p + C) ^ C := hnative₀.trans (hp₀p₁.trans hp₁C)
  have hcoverC : pCover ≤ (p + C) ^ C := hcover₁.trans hp₁C
  have hp₀0 : 0 ≤ p₀ := le_trans zero_le_one hp₀
  have hp₁0 : 0 ≤ p₁ := hp₀0.trans hp₀p₁
  have hdata := hnative D Fmark b ω hD c ν hF φ hφ hsurj W v hspan hW
    hp0 hDgeom hFgeom hκ hb hc hφheight hv
  unfold MarkedRefilteredNativeDiagramData at hdata
  obtain ⟨E, hEfil, hElat, hEgeom, hEinc, F, hFfil, hFlat, hFgeo, hFinc,
    hmark, _, _, hsource, _⟩ := hdata
  obtain ⟨nQ, hnQ, Q, hQfil, hQlat, hQgeom, hQproj⟩ := hsource
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (D.filtration.gradedRefiltrationSubalgebra W))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (D.filtration.gradedRefiltrationSubalgebra W)) :=
    IsModuleTopology.isTopologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 E.basis
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
    (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
    (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))) :=
    IsModuleTopology.isTopologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 F.basis
  let := moduleTopology ℝ (ℝ ⊗[ℚ]
    ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ]
    ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1))) :=
    IsModuleTopology.isTopologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 Q.basis
  have hcovers := hcover D Fmark φ hφ W E hEfil F Q hp₀
    (hEgeom.mono E hnative₀) (hDgeom.mono D hpp₀)
    (hQgeom.mono Q hnative₀) (hFgeo.mono F hnative₀)
    (fun i j => (hEinc i j).trans hnative₀)
    (fun i j => (hQproj i j).trans hnative₀)
    (fun i j => (hmark j i).trans hnative₀) hker q hq
    (hqp.trans (Real.exp_le_exp.mpr hpp₀))
  unfold AllocatedMarkedDiagramRecoveryCovers at hcovers
  obtain ⟨Q', hQ'fil, hQ'basis, hQ'lat, hQ'geom, F', hF'fil, hF'basis,
    hF'lat, hF'geom, hrec⟩ := hcovers
  have hQ'F : Q'.filtration = E.filtration.quotientTop := hQ'fil.trans hQfil
  have hF'F : F'.filtration = Fmark.filtration.gradedRefiltration
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)) := hF'fil.trans hFfil
  have hmarked := D.refilteredMarkedMap_mem_layer Fmark φ hφ W E hEfil F' hF'F
  have hstrong := D.refilteredMarkedMap_layer_surjective Fmark φ hφ W E hEfil F' hF'F
    b ω hD c ν hF hW hsurj
  have hproj₁ : ∀ i j, rationalLogHeight (Q'.basis.repr
      (lieQuotientMap (E.filtration.layerIdeal (s + 1)) (E.basis j)) i) ≤ p₁ := by
    intro i j
    rw [hQ'basis]
    exact (hQproj i j).trans (hnative₀.trans hp₀p₁)
  have hmark₁ : ∀ i j, rationalLogHeight (F'.basis.repr
      (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W (E.basis i)) j) ≤ p₁ := by
    intro i j
    rw [hF'basis]
    exact (hmark i j).trans (hnative₀.trans hp₀p₁)
  obtain ⟨nQF, hnQF, QF, hQFfil, hQFlat, hQFgeom, hQFproj, hQFmark, hQFfiltered, hQFstrong⟩ :=
    hlower E F' (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W)
      hmarked Q' hQ'F hstrong hp₁0 (hEgeom.mono E (hnative₀.trans hp₀p₁))
      (hF'geom.mono F' hcover₁) (hQ'geom.mono Q' hcover₁) hproj₁ hmark₁
  refine ⟨{
    Dref := E
    Dref_filtration := hEfil
    Dref_lattice := hElat
    Dref_geometry := hEgeom.mono E hnativeC
    inclusion_height := fun i j => (hEinc i j).trans hnativeC
    Fbase := F
    Fbase_filtration := hFfil
    Fbase_lattice := hFlat
    nQ := nQ
    nQ_le := hnQ
    Qbase := Q
    Qbase_filtration := hQfil
    Qbase_lattice := hQlat
    Fref := F'
    Fref_filtration := hF'F
    Fref_basis := hF'basis
    Fref_lattice := hF'lat
    Fref_geometry := hF'geom.mono F' hcoverC
    marked_inclusion_height := ?_
    restricted_mark_height := fun i j => (hmark₁ i j).trans hp₁C
    Q := Q'
    Q_filtration := hQ'F
    Q_basis := hQ'basis
    Q_lattice := hQ'lat
    Q_geometry := hQ'geom.mono Q' hcoverC
    quotient_height := fun i j => (hproj₁ i j).trans hp₁C
    refiltered_mark_strong := hstrong
    nQF := nQF
    nQF_le := hnQF
    Fquot := QF
    Fquot_filtration := hQFfil
    Fquot_lattice := hQFlat
    Fquot_geometry := hQFgeom.mono QF hlowerC
    marked_quotient_height := fun i j => (hQFproj i j).trans hlowerC
    lower_mark_height := fun i j => (hQFmark i j).trans hlowerC
    lower_mark_filtered := hQFfiltered
    lower_mark_strong := hQFstrong
    pCover := pCover
    pCover_nonneg := pow_nonneg (add_nonneg hp₀0 (Nat.cast_nonneg B)) B
    pCover_le := hcoverC
    recovery := ?_ }⟩
  · intro i j
    rw [hF'basis]
    exact (hFinc i j).trans hnativeC
  · dsimp only
    intro a r ha hr S ℓ hℓ hS hpositive
    apply hrec a r (fun i => (ha i).trans ?_) hr S ℓ
      (hℓ.trans (Real.exp_le_exp.mpr hpp₀)) hS hpositive
    exact Real.exp_le_exp.mpr (pow_le_pow_left₀ (by linarith) (by linarith) k)

end Erdos3.RationalFilteredNilmanifold

end


namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

universe u

def MarkedRefilteredLowerNativeDiagramData
    {L M : Type u} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d f : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d)
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded) (P : ℝ) : Prop :=
  let V := W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)
  let mark := D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W
  ∃ E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra W) (s + 1)
      (finrank ℚ (D.filtration.gradedRefiltrationSubalgebra W)),
    E.filtration = D.filtration.gradedRefiltration W ∧
    E.lattice = D.lattice.comap
      (NilpotentLieBCHGroup.map
        (hnil := (D.filtration.gradedRefiltration W).lowerCentralSeries_eq_bot)
        (D.filtration.gradedRefiltrationSubalgebra W).incl) ∧
    E.GeometryComplexityLE P ∧
    (∀ i j, rationalLogHeight (D.basis.repr (E.basis j : L) i) ≤ P) ∧
    ∃ EF : RationalFilteredNilmanifold (Fmark.filtration.gradedRefiltrationSubalgebra V) (s + 1)
        (finrank ℚ (Fmark.filtration.gradedRefiltrationSubalgebra V)),
      EF.filtration = Fmark.filtration.gradedRefiltration V ∧
      EF.lattice = Fmark.lattice.comap
        (NilpotentLieBCHGroup.map
          (hnil := (Fmark.filtration.gradedRefiltration V).lowerCentralSeries_eq_bot)
          (Fmark.filtration.gradedRefiltrationSubalgebra V).incl) ∧
      EF.GeometryComplexityLE P ∧
      (∀ i j, rationalLogHeight (Fmark.basis.repr (EF.basis j : M) i) ≤ P) ∧
      (∀ i j, rationalLogHeight (EF.basis.repr (mark (E.basis i)) j) ≤ P) ∧
      ∃ hmark : ∀ j, ∀ x ∈ E.filtration.layer j, mark x ∈ EF.filtration.layer j,
        (∀ j, ∀ y ∈ EF.filtration.layer j, ∃ x ∈ E.filtration.layer j, mark x = y) ∧
        ∃ n : ℕ, n ≤ finrank ℚ (D.filtration.gradedRefiltrationSubalgebra W) ∧
        ∃ Q : RationalFilteredNilmanifold
            ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n,
          Q.filtration = E.filtration.quotientTop ∧
          Q.lattice = E.lattice.map
            (E.filtration.quotientStepHom (E.filtration.layerIdeal (s + 1)) le_rfl) ∧
          Q.GeometryComplexityLE P ∧
          (∀ i j, rationalLogHeight (Q.basis.repr
            (lieQuotientMap (E.filtration.layerIdeal (s + 1)) (E.basis j)) i) ≤ P) ∧
          ∃ nF : ℕ, nF ≤ finrank ℚ (Fmark.filtration.gradedRefiltrationSubalgebra V) ∧
          ∃ QF : RationalFilteredNilmanifold
              ((Fmark.filtration.gradedRefiltrationSubalgebra V) ⧸ EF.filtration.layerIdeal (s + 1)) s nF,
            QF.filtration = EF.filtration.quotientTop ∧
            QF.lattice = EF.lattice.map
              (EF.filtration.quotientStepHom (EF.filtration.layerIdeal (s + 1)) le_rfl) ∧
            QF.GeometryComplexityLE P ∧
            (∀ i j, rationalLogHeight (QF.basis.repr
              (lieQuotientMap (EF.filtration.layerIdeal (s + 1)) (EF.basis j)) i) ≤ P) ∧
            (∀ i j, rationalLogHeight
              (QF.basis.repr (E.topQuotientMarkedMap EF mark hmark (Q.basis i)) j) ≤ P) ∧
            (∀ j, ∀ x ∈ Q.filtration.layer j,
              E.topQuotientMarkedMap EF mark hmark x ∈ QF.filtration.layer j) ∧
            ∀ j, ∀ y ∈ QF.filtration.layer j, ∃ x ∈ Q.filtration.layer j,
              E.topQuotientMarkedMap EF mark hmark x = y

theorem exists_marked_refiltered_lower_native_diagram :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {L M : Type u} {κ : Type*} [LieRing L] [LieAlgebra ℚ L]
      [LieRing M] [LieAlgebra ℚ M] [Fintype κ]
      {s d f n k : ℕ}
      (D : RationalFilteredNilmanifold L (s + 1) d)
      (Fmark : RationalFilteredNilmanifold M (s + 1) f)
      (b : Basis (Fin n) ℚ L) (ω : Fin n → ℕ)
      (hD : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (c : Basis (Fin k) ℚ M) (ν : Fin k → ℕ)
      (_hF : ∀ j, Fmark.filtration.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
      (φ : L →ₗ⁅ℚ⁆ M)
      (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j),
      (∀ j, ∀ y ∈ Fmark.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y) →
    ∀ (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
      (v : κ → D.filtration.AssociatedGraded),
      Submodule.span ℚ (Set.range v) = W.toSubmodule →
      BasisGradedSubmodule (D.filtration.associatedGradedBasis b ω hD) ω W.toSubmodule →
    ∀ {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p → Fmark.GeometryComplexityLE p →
      (Fintype.card κ : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (D.basis.repr (b i) j) ≤ p) →
      (∀ i j, rationalLogHeight (Fmark.basis.repr (c i) j) ≤ p) →
      (∀ i j, rationalLogHeight (Fmark.basis.repr (φ (D.basis i)) j) ≤ p) →
      (∀ i j, rationalLogHeight ((D.filtration.associatedGradedBasis b ω hD).repr (v i) j) ≤ p) →
      MarkedRefilteredLowerNativeDiagramData D Fmark φ hφ W ((p + C) ^ C) := by
  obtain ⟨A, _, hdiagram⟩ := exists_marked_refiltered_native_diagram
  obtain ⟨C, hC, hbudget⟩ := exists_nativeMarkedQuotientHeightBudget A
  refine ⟨C, hC, ?_⟩
  intro L M κ _ _ _ _ _ s d f n k D Fmark b ω hD c ν hF φ hφ hsurj
    W v hspan hW p hp hDgeom hFgeom hκ hb hc hφheight hv
  obtain ⟨hqC, hhC⟩ := hbudget p hp
  have hdata := hdiagram D Fmark b ω hD c ν hF φ hφ hsurj W v hspan hW
    hp hDgeom hFgeom hκ hb hc hφheight hv
  unfold MarkedRefilteredNativeDiagramData at hdata
  obtain ⟨E, hE, hEL, hEgeom, hEinc, EF, hEF, hEFL, hEFgeom, hEFinc,
    hmarkheight, hmark, hstrong, hsourceQ, htargetQ⟩ := hdata
  obtain ⟨nQ, hnQ, Q, hQ, hQL, hQgeom, hQproj⟩ := hsourceQ
  obtain ⟨nQF, hnQF, QF, hQF, hQFL, hQFgeom, hQFproj⟩ := htargetQ
  let mark := D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W
  have hq : 0 ≤ (p + A) ^ A := by positivity
  have hquotheight (i : Fin nQ) (j : Fin nQF) :
      rationalLogHeight (QF.basis.repr (E.topQuotientMarkedMap EF mark hmark
        (Q.basis i)) j) ≤ (p + C) ^ C :=
    (E.topQuotientMarkedMap_basis_logHeight EF mark hmark Q QF hq hEgeom hEFgeom
      hQgeom hQproj hmarkheight hQFproj i j).trans hhC
  unfold MarkedRefilteredLowerNativeDiagramData
  refine ⟨E, hE, hEL, hEgeom.mono E hqC, fun i j => (hEinc i j).trans hqC,
    EF, hEF, hEFL, hEFgeom.mono EF hqC, fun i j => (hEFinc i j).trans hqC,
    fun i j => (hmarkheight i j).trans hqC, hmark, hstrong,
    nQ, hnQ, Q, hQ, hQL, hQgeom.mono Q hqC, fun i j => (hQproj i j).trans hqC,
    nQF, hnQF, QF, hQF, hQFL, hQFgeom.mono QF hqC,
    fun i j => (hQFproj i j).trans hqC, hquotheight, ?_, ?_⟩
  · exact E.topQuotientMarkedMap_mem_layer EF mark hmark Q hQ QF hQF
  · exact E.topQuotientMarkedMap_layer_surjective EF mark hmark Q hQ QF hQF hstrong

end Erdos3.RationalFilteredNilmanifold

end OAI
