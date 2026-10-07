import OAI.Combinatorics.Progressions.Dynamics.ArbitraryStepPrescribedBudget
import OAI.Combinatorics.Progressions.Lattices.ActualFixedSpatialSlicedForecastFromResidueBox
import OAI.Combinatorics.Progressions.Sampling.ActualSlicedForecastLateData
import OAI.Combinatorics.Progressions.Sampling.AllocatedDenseFiberSliceForecastGeometry

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod : ℕ} {Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice : ℝ}

variable {A : Type} [Fintype A] {selected : A → Σ j : Fin m, Fin (n j)}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)
variable (q : ActualFixedSpatialSlicedForecastNumerics s)

structure ActualFixedSpatialDenseSliceInput where
  keep : G ⊕ PrincipalTupleIndex B (layerSamplerDegree I n) → Prop
  [keepDecidable : DecidablePred keep]
  keep_iff : ∀ k, keep k ↔ q.Hchild ≤
    Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S) k
  step : ℕ
  step_pos : 0 < step
  box : ResidueBoxSlice
    (fun k : {k // keep k} => Sum.elim (fun _ : G => S.value)
      (allocatedPrincipalSides B U b S) k.val) step
  fixed : {k // ¬keep k} → ℤ
  fixed_inside : ∀ k, 0 ≤ fixed k ∧ fixed k <
    ((Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S) k.val : ℕ) : ℤ)
  commonTuple : G → IntegerScalarCubeBox Empty S.value
  cost : ℝ
  dense : ∀ k, Real.exp (-cost) *
    ((Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S) k.val : ℕ) : ℝ) ≤ box.length k
  kernel_nonempty : Nonempty G
  cutoff_le : q.Hchild ≤ S.value
  late_floor : 2 ≤ Real.exp (-cost) * (S.value : ℝ)
  density_le : q.δ ≤ Real.exp (-cost)
  active_width : δslice ≤ Real.exp (-cost) / 2
  kernel_log : cost + 1 ≤ q.v
  prescribed_log : cost + 1 ≤ s.Ppres
  stride_cap : 2 * Real.exp cost ≤ q.Ptail

attribute [instance] ActualFixedSpatialDenseSliceInput.keepDecidable

namespace ActualFixedSpatialDenseSliceInput
variable {s q} (input : ActualFixedSpatialDenseSliceInput s q)

theorem side_pos (k : G ⊕ PrincipalTupleIndex B (layerSamplerDegree I n)) :
    0 < Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S) k := by
  cases k with
  | inl g => exact S.positive
  | inr j => exact allocatedPrincipalSides_pos B U b S j

omit [DecidableEq X] in
theorem length_pos (k : {k // input.keep k}) : 0 < input.box.length k := by
  have hp : (0 : ℝ) < ((Sum.elim (fun _ : G => S.value)
      (allocatedPrincipalSides B U b S) k.val : ℕ) : ℝ) := Nat.cast_pos.mpr (side_pos (S := S) k.val)
  exact Nat.cast_pos.mp ((mul_pos (Real.exp_pos _) hp).trans_le (input.dense k))

omit [DecidableEq X] in
theorem kernel_kept (g : G) : input.keep (Sum.inl g) :=
  (input.keep_iff _).mpr input.cutoff_le

omit [DecidableEq X] in
theorem active_kept (a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a})
    (p : B a.val × Fin (layerSamplerDegree I n a.val)) : input.keep (Sum.inr ⟨a.val,p⟩) := by
  apply (input.keep_iff _).mpr
  change q.Hchild ≤ allocatedPrincipalSides B U b S ⟨a.val,p⟩
  rw [allocatedPrincipalSides_not_short B U b S a p]
  exact input.cutoff_le

noncomputable def principalLower
    (a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a})
    (p : B a.val × Fin (layerSamplerDegree I n a.val)) : ℝ :=
  (input.box.fiberParameterStart input.fixed (Sum.inr ⟨a.val,p⟩) : ℝ) /
    allocatedPrincipalSides B U b S ⟨a.val,p⟩

noncomputable def principalWidth
    (a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a})
    (p : B a.val × Fin (layerSamplerDegree I n a.val)) : ℝ :=
  (ResidueBoxSlice.fiberParameterStride (keep := input.keep) (q := input.step)
    (Sum.inr ⟨a.val,p⟩) : ℝ) *
    (input.box.fiberParameterLength (Sum.inr ⟨a.val,p⟩) - 1 : ℕ) /
      allocatedPrincipalSides B U b S ⟨a.val,p⟩

omit [DecidableEq X] in
theorem kernel_geometry (g : G) :
    2 ≤ input.box.length ⟨Sum.inl g,input.kernel_kept g⟩ ∧
    0 ≤ (input.box.start ⟨Sum.inl g,input.kernel_kept g⟩ : ℝ) / S.value ∧
    Real.exp (-input.cost) / 2 ≤
      (input.step : ℝ) * (input.box.length ⟨Sum.inl g,input.kernel_kept g⟩ - 1 : ℕ) / S.value ∧
    (input.box.start ⟨Sum.inl g,input.kernel_kept g⟩ : ℝ) / S.value +
      (input.step : ℝ) * (input.box.length ⟨Sum.inl g,input.kernel_kept g⟩ - 1 : ℕ) / S.value < 1 ∧
    (input.step : ℝ) * (input.box.length ⟨Sum.inl g,input.kernel_kept g⟩ - 1 : ℕ) / S.value ≤ 1 ∧
    (input.step : ℝ) ≤ 2 * Real.exp input.cost :=
  input.box.denseCoordinate_geometry ⟨Sum.inl g,input.kernel_kept g⟩ input.step_pos
    S.positive (input.dense _) input.late_floor

omit [DecidableEq X] in
theorem principal_geometry
    (a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a})
    (p : B a.val × Fin (layerSamplerDegree I n a.val)) :
    0 ≤ input.principalLower a p ∧
      Real.exp (-input.cost) / 2 ≤ input.principalWidth a p ∧
      |input.principalLower a p| + |input.principalWidth a p| ≤ 1 := by
  have heq := allocatedPrincipalSides_not_short B U b S a p
  have hf : 2 ≤ Real.exp (-input.cost) *
      ((Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S) (Sum.inr ⟨a.val,p⟩) : ℕ) : ℝ) := by
    simpa only [Sum.elim_inr, heq] using input.late_floor
  have hg := input.box.fiberParameter_dense_geometry input.fixed
    (Sum.inr ⟨a.val,p⟩) (input.active_kept a p) input.step_pos
    (side_pos (S := S) _) (input.dense ⟨Sum.inr ⟨a.val,p⟩,input.active_kept a p⟩) hf
  exact ⟨hg.2.1, hg.2.2.1, hg.2.2.2.2⟩

omit [DecidableEq X] in
theorem step_le : (input.step : ℝ) ≤ 2 * Real.exp input.cost := by
  obtain ⟨g⟩ := input.kernel_nonempty
  exact (input.kernel_geometry g).2.2.2.2.2

omit [DecidableEq X] in
theorem kernel_exp_width : Real.exp (-q.v) ≤ Real.exp (-input.cost) / 2 := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc
    Real.exp (-q.v) ≤ Real.exp (-input.cost - 1) := Real.exp_le_exp.mpr (by linarith [input.kernel_log])
    _ = Real.exp (-input.cost) / Real.exp 1 := Real.exp_sub _ _
    _ ≤ _ := div_le_div_of_nonneg_left (Real.exp_nonneg _) (by norm_num) htwo

end ActualFixedSpatialDenseSliceInput

namespace ActualFixedSpatialForecastPath

variable {s q} {δbase PpresBase : ℝ}
variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δbase s.P s.Pbad PpresBase)

noncomputable def toDenseSliceMember (input : ActualFixedSpatialDenseSliceInput s q) :
    ActualFixedSpatialSlicedAdmissiblePath
      (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
      (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN) s q := by
  classical
  let origin : ∀ p : path.primes, LayerSamplerLongVariables
      (allocatedShortAxis (I := I) U b S.value) G B → ZMod (p.val ^ path.exponent p.val) :=
    fun p v => ((Sum.elim
      (fun g => (input.box.start ⟨Sum.inl g,input.kernel_kept g⟩ : ℤ))
      (fun a => input.box.fiberParameterStart input.fixed (Sum.inr ⟨a.1.val,a.2⟩)) v : ℤ) :
        ZMod (p.val ^ path.exponent p.val))
  have hpres : ((∏ p : path.primes, p.val ^ padicValNat p.val input.step : ℕ) : ℝ) ≤
      Real.exp s.Ppres :=
    (arbitraryStep_prescribed_product_exp_le path.primes path.prime input.step_pos input.step_le).trans
      (Real.exp_le_exp.mpr input.prescribed_log)
  let newpath := path.reparameterize δslice s.Ppres input.commonTuple
    (fun p => padicValNat p input.step) origin hpres
    input.principalLower input.principalWidth
    (fun a p => input.active_width.trans (input.principal_geometry a p).2.1)
    (fun a p => (input.principal_geometry a p).1)
    (fun a p => (input.principal_geometry a p).2.2)
  let slice := newpath.withResidueBoxSlice input.box input.length_pos input.fixed input.fixed_inside
    input.kernel_kept input.active_kept input.step_pos (fun g => (input.kernel_geometry g).1)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
  refine ⟨slice, ?_, ?_, ?_⟩
  · intro a
    have hdense (k : {k // input.keep k}) : q.δ *
        ((Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S) k.val : ℕ) : ℝ) ≤ input.box.length k :=
      (mul_le_mul_of_nonneg_right input.density_le (Nat.cast_nonneg _)).trans (input.dense k)
    have hregular := input.box.fiberParameter_regular_of_threshold hdense input.step_pos
      (fun k hk => (input.keep_iff k).mpr hk)
      (fun p : B ⟨(selected a).1,Sum.inr (selected a).2⟩ × Fin ((selected a).1.val + 1) =>
        Sum.inr (⟨⟨(selected a).1,Sum.inr (selected a).2⟩,p⟩ : PrincipalTupleIndex B (layerSamplerDegree I n)))
    rcases hregular with ⟨⟨i,v⟩,hsmall⟩ | ⟨hd,hs⟩
    · exact Or.inl ⟨i,v,hsmall⟩
    · exact Or.inr ⟨fun i v => hd (i,v), fun i v => hs (i,v)⟩
  · intro a i v
    exact (Nat.cast_le.mpr (ResidueBoxSlice.fiberParameterStride_le (keep := input.keep)
      (q := input.step) (Sum.inr ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,i,v⟩))).trans
        (input.step_le.trans input.stride_cap)
  · intro g
    exact input.kernel_exp_width.trans (input.kernel_geometry g).2.2.1

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod : ℕ} {Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice : ℝ}

variable {A : Type} [Fintype A] {selected : A → Σ j : Fin m, Fin (n j)}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)
variable (q : ActualFixedSpatialSlicedForecastNumerics s)

namespace ActualFixedSpatialForecastPath

variable {s q} {δbase PpresBase : ℝ}
variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δbase s.P s.Pbad PpresBase)

omit [Fintype Tsp] in

@[simp] theorem toDenseSliceMember_center (input : ActualFixedSpatialDenseSliceInput s q) :
    (path.toDenseSliceMember input).slice.path.center = path.center := rfl

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

end OAI
