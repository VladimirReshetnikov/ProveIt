/- Modified for ProveIt: unfold the newer IsLowerTriangular abbreviation
to BlockTriangular OrderDual.toDual for Lean 4.32. Mathematical statements
and proof bodies are otherwise unchanged. -/
import OAI.Combinatorics.Progressions.Lattices.PreparedIntegerRemainder
import OAI.Combinatorics.Progressions.Lattices.TriangularAffineReset
import OAI.Combinatorics.Progressions.Polynomial.PolynomialCoordinatePartition
import OAI.Combinatorics.Progressions.Polynomial.SingleParameterPolynomial

namespace OAI

section

namespace Erdos3

open MvPolynomial

namespace PolynomialPatch.LowestLayerModel

variable {σ : Type*} {s D E h : ℕ} {A : PolynomialPatch σ s (D + E)}
    (L : A.LowestLayerModel h)

theorem residualMatrix_lower : (1 - L.matrix).BlockTriangular OrderDual.toDual := by
  intro i j hij
  change i < j at hij
  simp [Matrix.sub_apply, Matrix.one_apply_ne hij.ne, L.strict i j hij.le]

theorem residualMatrix_diag (i : Fin D) : (1 - L.matrix) i i = 1 := by
  simp [Matrix.sub_apply, L.strict i i le_rfl]

noncomputable def integerChange : Matrix (Fin D) (Fin D) ℤ :=
  triangularReductionMatrix (1 - L.matrix)

theorem integerChange_det : L.integerChange.det = 1 :=
  triangularReductionMatrix_det (1 - L.matrix)

noncomputable def normalizedOrigin : Fin D → MvPolynomial σ ℝ :=
  polynomialMatrixAction (L.integerChange⁻¹.map (Int.castRingHom ℝ)) L.origin

theorem normalizedOrigin_degree (i : Fin D) :
    L.normalizedOrigin i ∈ weightedSupportLE (fun _ : σ => 1) h :=
  polynomialMatrixAction_degree _ L.origin L.degree i

theorem normalizedOrigin_residual (t : σ → ℝ) (y : Fin D → ℝ) :
    (1 - L.matrix).mulVec ((fun i => aeval t (L.origin i)) -
      (L.integerChange.map (Int.castRingHom ℝ)).mulVec y) =
      (reducedTriangularMatrix (1 - L.matrix)).mulVec
        ((fun i => aeval t (L.normalizedOrigin i)) - y) := by
  have hU : IsUnit L.integerChange.det := by rw [L.integerChange_det]; exact isUnit_one
  simpa only [normalizedOrigin, polynomialMatrixAction_eval, integerChange,
    reducedTriangularMatrix] using real_basis_change_residual (1 - L.matrix)
      L.integerChange hU (fun i => aeval t (L.origin i)) y

theorem exists_freeze_normalized (U : Set (σ → ℝ))
    (J : Fin D → MvPolynomial σ ℝ) (v : (σ → ℝ) → Fin D → ℤ)
    (hJ : ∀ i, J i ∈ weightedSupportLE (fun _ : σ => 1) h)
    (hint : ∀ t ∈ U, ∀ i, aeval t (J i) = (v t i : ℝ))
    (t₀ : σ → ℝ) (ht₀ : t₀ ∈ U) (bref : Fin (D + E) → ℤ)
    (href : A.kernel.value ((A.form.slots t₀).residual bref) ≠ 0)
    {ε : ℝ} (hε : (D : ℝ) * ε < 1 / 12)
    (hosc : ∀ t ∈ U, ‖(fun i => aeval t (L.normalizedOrigin i) - aeval t (J i)) -
      (fun i => aeval t₀ (L.normalizedOrigin i) - aeval t₀ (J i))‖ ≤ ε) :
    ∃ F : PolynomialPatch σ s E, F.kernel.lip = A.kernel.lip ∧
      (∀ i, F.weight i = A.weight (i.natAdd D)) ∧
      ∀ t ∈ U, dist (A.value t) (F.value t) ≤ A.kernel.lip * ((D : ℝ) * ε) := by
  let I := polynomialMatrixAction (L.integerChange.map (Int.castRingHom ℝ)) J
  let w (t : σ → ℝ) := L.integerChange.mulVec (v t)
  have hI : ∀ i, I i ∈ weightedSupportLE (fun _ : σ => 1) h :=
    polynomialMatrixAction_degree _ J hJ
  have hIeval : ∀ t ∈ U, ∀ i, aeval t (I i) = (w t i : ℝ) := by
    intro t ht i
    have heval := congrFun (polynomialMatrixAction_eval
      (L.integerChange.map (Int.castRingHom ℝ)) J t) i
    change aeval t (I i) = _ at heval
    rw [heval]
    simp only [hint t ht]
    exact (RingHom.map_mulVec (Int.castRingHom ℝ) L.integerChange (v t) i).symm
  have hres (t : σ → ℝ) :
      (1 - L.matrix).mulVec (fun i => aeval t (L.origin i) - aeval t (I i)) =
        (reducedTriangularMatrix (1 - L.matrix)).mulVec
          (fun i => aeval t (L.normalizedOrigin i) - aeval t (J i)) := by
    change (1 - L.matrix).mulVec ((fun i => aeval t (L.origin i)) -
      (fun i => aeval t (polynomialMatrixAction _ J i))) = _
    rw [polynomialMatrixAction_eval]
    exact L.normalizedOrigin_residual t (fun i => aeval t (J i))
  apply L.exists_freeze A U I w hI hIeval t₀ ht₀ bref href hε
  intro t ht
  rw [Matrix.mulVec_sub, hres t, hres t₀, ← dist_eq_norm]
  have hbound := (bounded_matrix_mulVec_lipschitz
    (reducedTriangularMatrix (1 - L.matrix))
    (reducedTriangularMatrix_bound (1 - L.matrix) L.residualMatrix_lower
      L.residualMatrix_diag)).dist_le_mul
        (fun i => aeval t (L.normalizedOrigin i) - aeval t (J i))
        (fun i => aeval t₀ (L.normalizedOrigin i) - aeval t₀ (J i))
  exact hbound.trans (mul_le_mul_of_nonneg_left
    (by simpa only [dist_eq_norm] using hosc t ht) (Nat.cast_nonneg D))

end PolynomialPatch.LowestLayerModel
end Erdos3

end

section

namespace Erdos3.PolynomialPatch.LowestLayerModel
open MvPolynomial

variable {σ τ : Type*} {s D E h : ℕ} {A : PolynomialPatch σ s (D + E)}

noncomputable def reparam (L : A.LowestLayerModel h)
    (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ a, f a ∈ weightedSupportLE (fun _ : τ => 1) 1) :
    (A.reparam f hf).LowestLayerModel h where
  matrix := L.matrix
  strict := L.strict
  origin i := aeval f (L.origin i)
  degree i := weightedSupportLE_aeval (fun _ : σ => 1) (fun _ : τ => 1) f hf (L.degree i)
  weights := L.weights
  form_eq t := by
    change ((A.form.reparam f hf).slots t).takePrefix = _
    rw [PolynomialSlots.reparam_slots, L.form_eq]
    simp only [MvPolynomial.comp_aeval_apply]

theorem reparam_normalizedOrigin (L : A.LowestLayerModel h)
    (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ a, f a ∈ weightedSupportLE (fun _ : τ => 1) 1) (i : Fin D) :
    (L.reparam f hf).normalizedOrigin i = aeval f (L.normalizedOrigin i) := by
  simp [normalizedOrigin, polynomialMatrixAction, reparam, integerChange]

noncomputable def onAffineLine (L : A.LowestLayerModel h) (a q : σ → ℝ) :
    (A.onAffineLine a q).LowestLayerModel h :=
  L.reparam (PolynomialPatch.affineLineParameters a q) (PolynomialPatch.affineLineParameters_degree a q)

theorem onAffineLine_normalizedOrigin_eval (L : A.LowestLayerModel h)
    (a q : σ → ℝ) (n : ℝ) (i : Fin D) :
    aeval (fun _ : Unit => n) ((L.onAffineLine a q).normalizedOrigin i) =
      aeval (fun j => a j + q j * n) (L.normalizedOrigin i) := by
  change aeval (fun _ : Unit => n) ((L.reparam _ _).normalizedOrigin i) = _
  rw [reparam_normalizedOrigin, MvPolynomial.comp_aeval_apply]
  have hargs : (fun j => aeval (fun _ : Unit => n) (PolynomialPatch.affineLineParameters a q j)) =
      (fun j => a j + q j * n) := by
    funext j
    simp [PolynomialPatch.affineLineParameters, MvPolynomial.aeval_eq_eval]
  rw [hargs]

end Erdos3.PolynomialPatch.LowestLayerModel

end

section

namespace Erdos3

open MvPolynomial
open scoped NNReal

def PatchKernel.zeroWithLip (d : ℕ) (L : ℝ≥0) : PatchKernel d where
  value _ := 0
  nonneg _ := le_rfl
  le_one _ := zero_le_one
  support _ h := (h rfl).elim
  lip := L
  lipschitz := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_self]
    exact mul_nonneg L.coe_nonneg (dist_nonneg (x := x) (y := y))

namespace PolynomialPatch.LowestLayerModel

variable {s D E h : ℕ} {A : PolynomialPatch Unit s (D + E)}

theorem exists_freeze_normalized_cell_at (L : A.LowestLayerModel h)
    (g : ℕ → Fin D → ℤ) (z : Fin D → ℝ) {N n₀ : ℕ} {δ : ℝ}
    (hδ : 0 ≤ δ) (hsmall : (2 : ℝ) ^ (h + 1) * δ < 1)
    (hfreeze : (D : ℝ) * (2 * δ) < 1 / 12)
    (hcell : ∀ n < N, ∀ i,
      ‖aeval (fun _ : Unit => (n : ℝ)) (L.normalizedOrigin i) - g n i - z i‖ ≤ δ)
    (hn₀ : n₀ < N) (bref : Fin (D + E) → ℤ)
    (href : A.kernel.value ((A.form.slots (fun _ => (n₀ : ℝ))).residual bref) ≠ 0) :
    ∃ F : PolynomialPatch Unit s E, F.kernel.lip = A.kernel.lip ∧
      (∀ i, F.weight i = A.weight (i.natAdd D)) ∧
      ∀ n < N, dist (A.value (fun _ => (n : ℝ))) (F.value (fun _ => (n : ℝ))) ≤
        A.kernel.lip * ((D : ℝ) * (2 * δ)) := by
  have hlift (i : Fin D) := exists_singleParameter_integer_lift
    (L.normalizedOrigin i - C (z i)) (fun n => g n i)
    ((weightedSupportLE _ _).sub_mem (L.normalizedOrigin_degree i)
      (weightedSupportLE_C _ _ _)) hsmall
    (show ∀ n < N, ‖(g n i : ℝ) - aeval (fun _ : Unit => (n : ℝ))
        (L.normalizedOrigin i - C (z i))‖ ≤ δ from by
      intro n hn
      simp only [map_sub, aeval_C, Algebra.algebraMap_self, RingHom.id_apply]
      rw [show (g n i : ℝ) - (aeval (fun _ : Unit => (n : ℝ)) (L.normalizedOrigin i) - z i) =
        -(aeval (fun _ : Unit => (n : ℝ)) (L.normalizedOrigin i) - g n i - z i) by ring,
        norm_neg]
      exact hcell n hn i)
  choose J hJ hJint hJeq hJclose using hlift
  let U : Set (Unit → ℝ) := {t | ∃ n < N, t = fun _ : Unit => (n : ℝ)}
  let v (t : Unit → ℝ) := g ⌊t ()⌋₊
  have hint : ∀ t ∈ U, ∀ i, aeval t (J i) = (v t i : ℝ) := by
    rintro t ⟨n, hn, rfl⟩ i
    simpa only [v, Nat.floor_natCast] using hJeq i n hn
  have hdist (n : ℕ) (hn : n < N) :
      dist (fun i => aeval (fun _ : Unit => (n : ℝ)) (L.normalizedOrigin i) -
        aeval (fun _ : Unit => (n : ℝ)) (J i)) z ≤ δ := by
    apply (dist_pi_le_iff hδ).mpr
    intro i
    rw [hJeq i n hn]
    simpa only [dist_eq_norm] using hcell n hn i
  have hosc : ∀ t ∈ U,
      ‖(fun i => aeval t (L.normalizedOrigin i) - aeval t (J i)) -
        (fun i => aeval (fun _ : Unit => (n₀ : ℝ)) (L.normalizedOrigin i) -
          aeval (fun _ : Unit => (n₀ : ℝ)) (J i))‖ ≤ 2 * δ := by
    rintro t ⟨n, hn, rfl⟩
    rw [← dist_eq_norm]
    calc
      _ ≤ dist (fun i => aeval (fun _ : Unit => (n : ℝ)) (L.normalizedOrigin i) -
            aeval (fun _ : Unit => (n : ℝ)) (J i)) z +
          dist z (fun i => aeval (fun _ : Unit => (n₀ : ℝ)) (L.normalizedOrigin i) -
            aeval (fun _ : Unit => (n₀ : ℝ)) (J i)) := dist_triangle _ _ _
      _ ≤ δ + δ := add_le_add (hdist n hn) (by simpa only [dist_comm] using hdist n₀ hn₀)
      _ = 2 * δ := by ring
  obtain ⟨F, hF, hweights, herror⟩ := L.exists_freeze_normalized U J v hJ hint
    (fun _ => (n₀ : ℝ)) ⟨n₀, hn₀, rfl⟩ bref href hfreeze hosc
  exact ⟨F, hF, hweights, fun n hn => herror (fun _ => (n : ℝ)) ⟨n, hn, rfl⟩⟩

theorem exists_freeze_normalized_cell (L : A.LowestLayerModel h)
    (g : ℕ → Fin D → ℤ) (z : Fin D → ℝ) {N : ℕ} {δ : ℝ}
    (hδ : 0 ≤ δ) (hsmall : (2 : ℝ) ^ (h + 1) * δ < 1)
    (hfreeze : (D : ℝ) * (2 * δ) < 1 / 12)
    (hcell : ∀ n < N, ∀ i,
      ‖aeval (fun _ : Unit => (n : ℝ)) (L.normalizedOrigin i) - g n i - z i‖ ≤ δ) :
    ∃ F : PolynomialPatch Unit s E, F.kernel.lip = A.kernel.lip ∧
      (∀ i, F.weight i = A.weight (i.natAdd D)) ∧
      ∀ n < N, dist (A.value (fun _ => (n : ℝ))) (F.value (fun _ => (n : ℝ))) ≤
        A.kernel.lip * ((D : ℝ) * (2 * δ)) := by
  by_cases hex : ∃ n < N, ∃ b : Fin (D + E) → ℤ,
      A.kernel.value ((A.form.slots (fun _ => (n : ℝ))).residual b) ≠ 0
  · obtain ⟨n, hn, b, hb⟩ := hex
    exact L.exists_freeze_normalized_cell_at g z hδ hsmall hfreeze hcell hn b hb
  · let base := A.freezePrefix (fun _ : Fin D => (0 : MvPolynomial Unit ℝ))
      (fun _ => (weightedSupportLE _ _).zero_mem) (0 : Fin D → ℝ)
    let F : PolynomialPatch Unit s E := { base with kernel := PatchKernel.zeroWithLip E A.kernel.lip }
    have hF (t : Unit → ℝ) : F.value t = 0 := by
      apply (F.form.slots t).patchValue_eq_zero F.kernel
      intro b
      rfl
    have hA (n : ℕ) (hn : n < N) : A.value (fun _ => (n : ℝ)) = 0 := by
      apply (A.form.slots (fun _ => (n : ℝ))).patchValue_eq_zero A.kernel
      intro b
      exact not_ne_iff.mp (fun hb => hex ⟨n, hn, b, hb⟩)
    refine ⟨F, rfl, (fun _ => rfl), ?_⟩
    intro n hn
    rw [hA n hn, hF, dist_self]
    positivity

end PolynomialPatch.LowestLayerModel
end Erdos3

end

section

namespace Erdos3

open MvPolynomial

theorem PolynomialCoordinatePartitionBound.freeze_layer {h p : ℕ} {K : ℝ}
    (hpartition : PolynomialCoordinatePartitionBound.{0} h K p)
    {s D E N H : ℕ} (A : PolynomialPatch Unit s (D + E)) (L : A.LowestLayerModel h)
    (hH : 0 < H) (hscale : K * ((D : ℝ) + 1) ≤ H)
    (hsize : H ^ (p * (D + 1) ^ (2 * h)) ≤ N)
    (hsmall : (2 : ℝ) ^ (h + 1) * ((h : ℝ) / H) < 1)
    (hfreeze : (D : ℝ) * (2 * ((h : ℝ) / H)) < 1 / 12) :
    ∃ (Q : FiniteProgressionPartition N) (F : Q.Label → PolynomialPatch Unit s E),
      Fintype.card Q.Label * H ≤ 2 ^ h * N ∧
      ∀ i, (F i).kernel.lip = A.kernel.lip ∧
        (∀ j, (F i).weight j = A.weight (j.natAdd D)) ∧
        ∀ n < Q.length i,
          dist (A.value (fun _ => ((Q.start i + Q.step i * n : ℕ) : ℝ)))
            ((F i).value (fun _ => (n : ℝ))) ≤ A.kernel.lip * ((D : ℝ) * (2 * ((h : ℝ) / H))) := by
  let P := fun i => MvPolynomial.uniqueAlgEquiv ℝ Unit (L.normalizedOrigin i)
  have hP : ∀ i, (P i).natDegree ≤ h := fun i => singleParameter_natDegree_le (L.normalizedOrigin_degree i)
  obtain ⟨Q, z, m, hcount, herror⟩ := hpartition (Fin D) P hP N H hH
    (by simpa only [Fintype.card_fin] using hscale) (by simpa only [Fintype.card_fin] using hsize)
  have hcell (i : Q.Label) :
      ∃ F : PolynomialPatch Unit s E, F.kernel.lip = A.kernel.lip ∧
        (∀ j, F.weight j = A.weight (j.natAdd D)) ∧
        ∀ n < Q.length i,
          dist (A.value (fun _ => ((Q.start i + Q.step i * n : ℕ) : ℝ)))
            (F.value (fun _ => (n : ℝ))) ≤ A.kernel.lip * ((D : ℝ) * (2 * ((h : ℝ) / H))) := by
    let L' := L.onAffineLine (fun _ => (Q.start i : ℝ)) (fun _ => (Q.step i : ℝ))
    have hclose : ∀ n < Q.length i, ∀ j,
        ‖aeval (fun _ : Unit => (n : ℝ)) (L'.normalizedOrigin j) - m i n j - z i j‖ ≤ (h : ℝ) / H := by
      intro n hn j
      change ‖aeval (fun _ : Unit => (n : ℝ))
        ((L.onAffineLine _ _).normalizedOrigin j) - m i n j - z i j‖ ≤ _
      rw [PolynomialPatch.LowestLayerModel.onAffineLine_normalizedOrigin_eval]
      have he := herror i n hn j
      simpa only [P, singleParameter_eval, Nat.cast_add, Nat.cast_mul, Real.norm_eq_abs] using he
    obtain ⟨F, hFlip, hFweights, hFerr⟩ := L'.exists_freeze_normalized_cell (m i) (z i)
      (by positivity : 0 ≤ (h : ℝ) / H) hsmall hfreeze hclose
    refine ⟨F, hFlip, hFweights, ?_⟩
    intro n hn
    have he := hFerr n hn
    rw [PolynomialPatch.onAffineLine_value] at he
    change dist (A.value _) (F.value _) ≤ A.kernel.lip * _ at he
    simpa only [Nat.cast_add, Nat.cast_mul] using he
  choose F hFlip hFweights hFerr using hcell
  exact ⟨Q, F, hcount, fun i => ⟨hFlip i, hFweights i, hFerr i⟩⟩

theorem exists_normalized_layer_partition (h : ℕ) :
    ∃ (K : ℝ) (p : ℕ), 1 ≤ K ∧ 0 < p ∧
      ∀ (s D E N H : ℕ) (A : PolynomialPatch Unit s (D + E)) (_L : A.LowestLayerModel h),
        0 < H → K * ((D : ℝ) + 1) ≤ H → H ^ (p * (D + 1) ^ (2 * h)) ≤ N →
        (2 : ℝ) ^ (h + 1) * ((h : ℝ) / H) < 1 →
        (D : ℝ) * (2 * ((h : ℝ) / H)) < 1 / 12 →
        ∃ (Q : FiniteProgressionPartition N) (F : Q.Label → PolynomialPatch Unit s E),
          Fintype.card Q.Label * H ≤ 2 ^ h * N ∧
          ∀ i, (F i).kernel.lip = A.kernel.lip ∧
            (∀ j, (F i).weight j = A.weight (j.natAdd D)) ∧
            ∀ n < Q.length i,
              dist (A.value (fun _ => ((Q.start i + Q.step i * n : ℕ) : ℝ)))
                ((F i).value (fun _ => (n : ℝ))) ≤ A.kernel.lip * ((D : ℝ) * (2 * ((h : ℝ) / H))) := by
  obtain ⟨K, p, hK, hp, hpartition⟩ := exists_polynomial_coordinate_partition_bound.{0} h
  exact ⟨K, p, hK, hp, fun s D E N H A L hH hscale hsize hsmall hfreeze =>
    hpartition.freeze_layer A L hH hscale hsize hsmall hfreeze⟩

end Erdos3

end

section

namespace Erdos3.PolynomialPatch.LowestLayerModel

open VectorPolynomial MvPolynomial
open scoped BigOperators TensorProduct

variable {X : Type} {s D E m : ℕ} {A : PolynomialPatch X s (D + E)}

theorem exists_freeze_prepared (F : A.LowestLayerModel m)
    (L : RankPreparationFamily X (Fin D) m)
    (ip : Fin D → MvPolynomial X ℤ) (hip : ∀ i, (ip i).totalDegree ≤ m)
    (c : Fin D → ℝ) (err : VectorPolynomial X ℝ (Fin D → ℝ))
    (hprepare : VectorPolynomial.ofCoordinates (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin =
      L.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c) + err)
    (β : ∀ u, (L u).Coord → MvPolynomial X ℤ)
    (hβ : ∀ u i, (β u i).totalDegree ≤ u.val + 1)
    (center : ∀ u, (L u).Coord → ℝ) (ε : Fin m → ℝ) (hε : ∀ u, 0 ≤ ε u)
    {δ : ℝ} (hδ : 0 ≤ δ) (Ω : Set (X → ℝ))
    (hinteger : ∀ x ∈ Ω, ∃ z : X → ℤ, x = fun i => (z i : ℝ))
    (hsmall : ∀ x ∈ Ω, ∀ u i, |VectorPolynomial.eval x (L u).poly i - center u i -
      MvPolynomial.eval x (MvPolynomial.map (Int.castRingHom ℝ) (β u i))| ≤ ε u)
    (herr : ∀ x ∈ Ω, ∀ i, |VectorPolynomial.eval x err i| ≤ δ)
    (x₀ : X → ℝ) (hx₀ : x₀ ∈ Ω) (bref : Fin (D + E) → ℤ)
    (href : A.kernel.value ((A.form.slots x₀).residual bref) ≠ 0)
    (hbudget : (D : ℝ) * (2 * ((∑ u, (Fintype.card (L u).Coord : ℝ) * ε u) + δ)) < 1 / 12) :
    ∃ A' : PolynomialPatch X s E,
      A'.kernel.lip = A.kernel.lip ∧
      (∀ i, A'.weight i = A.weight (i.natAdd D)) ∧
      ∀ x ∈ Ω, dist (A.value x) (A'.value x) ≤
        A.kernel.lip * ((D : ℝ) * (2 * ((∑ u, (Fintype.card (L u).Coord : ℝ) * ε u) + δ))) := by
  let Γ := L.integerRemainder ip β
  let J : Fin D → MvPolynomial X ℝ := fun i => MvPolynomial.map (Int.castRingHom ℝ) (Γ i)
  let z : (X → ℝ) → Fin D → ℤ := fun x i => MvPolynomial.eval (fun v => ⌊x v⌋) (Γ i)
  have hJ : ∀ i, J i ∈ weightedSupportLE (fun _ : X => 1) m := by
    intro i
    apply (mem_weightedSupportLE_iff _ _ _).mpr
    change (J i).weightedTotalDegree 1 ≤ m
    rw [MvPolynomial.weightedTotalDegree_one]
    have hmap : (J i).totalDegree ≤ (Γ i).totalDegree :=
      Finset.sup_mono (MvPolynomial.support_map_subset _ _)
    exact hmap.trans (L.integerRemainder_degree ip hip β hβ i)
  have hint : ∀ x ∈ Ω, ∀ i, aeval x (J i) = (z x i : ℝ) := by
    intro x hx i
    obtain ⟨v, rfl⟩ := hinteger x hx
    simp only [J, z, Int.floor_intCast, MvPolynomial.aeval_eq_eval]
    exact (MvPolynomial.map_eval (Int.castRingHom ℝ) v (Γ i)).symm
  apply F.exists_freeze_normalized Ω J z hJ hint x₀ hx₀ bref href hbudget
  have heval (x : X → ℝ) :
      VectorPolynomial.eval x (VectorPolynomial.ofCoordinates (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin) =
        fun i => aeval x (F.normalizedOrigin i) := by
    have he : eval₂ (R := ℝ) x (VectorPolynomial.ofCoordinates (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin) =
        VectorPolynomial.eval x (VectorPolynomial.ofCoordinates (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin) := by
      simpa using (eval₂_algebraMap (S := ℝ) x
        (VectorPolynomial.ofCoordinates (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin))
    rw [← he, eval₂_ofCoordinates, Pi.basisFun_equivFun]
    rfl
  intro x hx
  have hosc := L.integerRemainder_oscillation
    (VectorPolynomial.ofCoordinates (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin) err ip c hprepare
    β center ε hε hδ Ω hsmall herr x₀ hx₀ x hx
  simpa only [heval, J, Γ, Pi.sub_def, MvPolynomial.aeval_eq_eval] using hosc

end Erdos3.PolynomialPatch.LowestLayerModel

end

end OAI
