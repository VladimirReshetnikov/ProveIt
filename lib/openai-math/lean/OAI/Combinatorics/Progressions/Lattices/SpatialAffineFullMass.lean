import OAI.Combinatorics.Progressions.Estimates.PreparedLayerFreezing
import OAI.Combinatorics.Progressions.Estimates.VectorRealSubstitutionBound
import OAI.Combinatorics.Progressions.Polynomial.PreparedPolynomialPullback

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {K X R : Type*} [Fintype K] [CommRing R] [Nontrivial R]

noncomputable def affineFramePolynomial (frame : Option K → X → R) (i : X) : MvPolynomial K R :=
  MvPolynomial.C (frame none i) + ∑ k, MvPolynomial.C (frame (some k) i) * MvPolynomial.X k

theorem affineFramePolynomial_degree (frame : Option K → X → R) (i : X) :
    (affineFramePolynomial frame i).totalDegree ≤ 1 := by
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le (by simp)
  apply MvPolynomial.totalDegree_finsetSum_le
  intro k _
  exact (MvPolynomial.totalDegree_mul _ _).trans (by
    simp only [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X, zero_add, le_refl])

theorem affineFramePolynomial_support (frame : Option K → X → R) (i : X) :
    affineFramePolynomial frame i ∈ weightedSupportLE (fun _ : K => 1) 1 := by
  apply (mem_weightedSupportLE_iff _ _ _).mpr
  change (affineFramePolynomial frame i).weightedTotalDegree 1 ≤ 1
  rw [MvPolynomial.weightedTotalDegree_one]
  exact affineFramePolynomial_degree frame i

omit [Nontrivial R] in
@[simp] theorem affineFramePolynomial_eval (frame : Option K → X → R) (y : K → R) (i : X) :
    MvPolynomial.aeval y (affineFramePolynomial frame i) =
      frame none i + ∑ k, frame (some k) i * y k := by
  simp [affineFramePolynomial]

omit [Nontrivial R] in
theorem affineFramePolynomial_map {S : Type*} [CommRing S] [Nontrivial S] (φ : R →+* S)
    (frame : Option K → X → R) (i : X) :
    MvPolynomial.map φ (affineFramePolynomial frame i) =
      affineFramePolynomial (fun k i => φ (frame k i)) i := by
  simp [affineFramePolynomial]

end Erdos3

end

section

namespace Erdos3.PolynomialPatch.LowestLayerModel

open VectorPolynomial MvPolynomial
open scoped BigOperators TensorProduct

variable {X K : Type} [Fintype K] {s D E m : ℕ} {A : PolynomialPatch X s (D + E)}

theorem exists_freeze_prepared_affine (F : A.LowestLayerModel m)
    (L : RankPreparationFamily X (Fin D) m)
    (ip : Fin D → MvPolynomial X ℤ) (hip : ∀ i, (ip i).totalDegree ≤ m)
    (c : Fin D → ℝ) (err : VectorPolynomial X ℝ (Fin D → ℝ))
    (hprepare : VectorPolynomial.ofCoordinates (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin =
      L.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c) + err)
    (frame : Option K → X → ℤ)
    (β : ∀ u, (L u).Coord → MvPolynomial K ℤ)
    (hβ : ∀ u i, (β u i).totalDegree ≤ u.val + 1)
    (center : ∀ u, (L u).Coord → ℝ) (ε : Fin m → ℝ) (hε : ∀ u, 0 ≤ ε u)
    {δ : ℝ} (hδ : 0 ≤ δ) (Ω : Set (K → ℝ))
    (hinteger : ∀ x ∈ Ω, ∃ z : K → ℤ, x = fun i => (z i : ℝ))
    (hsmall : ∀ x ∈ Ω, ∀ u i,
      |VectorPolynomial.eval (fun v => (frame none v : ℝ) + ∑ k, (frame (some k) v : ℝ) * x k)
        (L u).poly i - center u i -
        MvPolynomial.eval x (MvPolynomial.map (Int.castRingHom ℝ) (β u i))| ≤ ε u)
    (herr : ∀ x ∈ Ω, ∀ i,
      |VectorPolynomial.eval (fun v => (frame none v : ℝ) + ∑ k, (frame (some k) v : ℝ) * x k)
        err i| ≤ δ)
    (x₀ : K → ℝ) (hx₀ : x₀ ∈ Ω) (bref : Fin (D + E) → ℤ)
    (href : A.kernel.value ((A.form.slots
      (fun v => (frame none v : ℝ) + ∑ k, (frame (some k) v : ℝ) * x₀ k)).residual bref) ≠ 0)
    (hbudget : (D : ℝ) * (2 * ((∑ u, (Fintype.card (L u).Coord : ℝ) * ε u) + δ)) < 1 / 12) :
    ∃ A' : PolynomialPatch K s E,
      A'.kernel.lip = A.kernel.lip ∧
      (∀ i, A'.weight i = A.weight (i.natAdd D)) ∧
      ∀ x ∈ Ω, dist (A.value
          (fun v => (frame none v : ℝ) + ∑ k, (frame (some k) v : ℝ) * x k)) (A'.value x) ≤
        A.kernel.lip * ((D : ℝ) * (2 * ((∑ u, (Fintype.card (L u).Coord : ℝ) * ε u) + δ))) := by
  let fi := affineFramePolynomial frame
  let f := affineFramePolynomial (fun k v => (frame k v : ℝ))
  have hf : ∀ v, f v ∈ weightedSupportLE (fun _ : K => 1) 1 :=
    affineFramePolynomial_support _
  have hmap : (fun v => MvPolynomial.map (Int.castRingHom ℝ) (fi v)) = f :=
    funext (affineFramePolynomial_map (Int.castRingHom ℝ) frame)
  let L' := L.pullback f
  let ip' := fun i => MvPolynomial.aeval fi (ip i)
  have hip' : ∀ i, (ip' i).totalDegree ≤ m := by
    intro i
    exact (aeval_polynomial_totalDegree_le (ip i) fi (hip i) (affineFramePolynomial_degree frame)).trans_eq
      (Nat.mul_one m)
  have hpull : VectorPolynomial.ofCoordinates (Pi.basisFun ℝ (Fin D)) (F.reparam f hf).normalizedOrigin =
      L'.polynomial + integerCoordinates ip' + (1 ⊗ₜ[ℝ] c) + substitute f err := by
    have he := L.pullback_identity
      (VectorPolynomial.ofCoordinates (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin) err ip c hprepare fi
    dsimp only at he
    rw [hmap, substitute_ofCoordinates] at he
    have hn : (F.reparam f hf).normalizedOrigin =
        fun i => MvPolynomial.aeval f (F.normalizedOrigin i) :=
      funext (reparam_normalizedOrigin F f hf)
    rw [hn]
    exact he
  have href' : (A.reparam f hf).kernel.value
      (((A.reparam f hf).form.slots x₀).residual bref) ≠ 0 := by
    change A.kernel.value (((A.form.reparam f hf).slots x₀).residual bref) ≠ 0
    rw [PolynomialSlots.reparam_slots]
    simpa only [f, affineFramePolynomial_eval] using href
  obtain ⟨A', hLip, hweight, hval⟩ := (F.reparam f hf).exists_freeze_prepared L' ip' hip' c
    (substitute f err) hpull β hβ center ε hε hδ Ω hinteger
    (by
      intro x hx u i
      change |VectorPolynomial.eval x (substitute f (L u).poly) i - center u i -
        MvPolynomial.eval x (MvPolynomial.map (Int.castRingHom ℝ) (β u i))| ≤ ε u
      rw [eval_substitute]
      simpa only [f, affineFramePolynomial_eval] using hsmall x hx u i)
    (by simpa only [eval_substitute, f, affineFramePolynomial_eval] using herr)
    x₀ hx₀ bref href' hbudget
  refine ⟨A', hLip, hweight, ?_⟩
  intro x hx
  have hv := hval x hx
  rw [PolynomialPatch.reparam_value] at hv
  change dist (A.value (fun v => MvPolynomial.aeval x (f v))) (A'.value x) ≤
    A.kernel.lip * ((D : ℝ) * (2 * ((∑ u, (Fintype.card (L u).Coord : ℝ) * ε u) + δ))) at hv
  simpa only [f, affineFramePolynomial_eval] using hv

end Erdos3.PolynomialPatch.LowestLayerModel

end

section

namespace Erdos3

open scoped BigOperators TensorProduct
open VectorPolynomial

namespace RankPreparationLayer

variable {I J K : Type}

theorem pullback_value [DecidableEq J] (L : RankPreparationLayer I J)
    (f : I → MvPolynomial K ℝ) (x : K → ℝ) :
    (L.pullback f).value x = L.value (fun i => MvPolynomial.aeval (R := ℝ) x (f i)) :=
  congrArg (coordinateCopySum L.label) (eval_substitute f x L.poly)

end RankPreparationLayer

namespace RankPreparationFamily

variable {I J K : Type} {s : ℕ}

@[simp] theorem pullback_potential (L : RankPreparationFamily I J s)
    (f : I → MvPolynomial K ℝ) : (L.pullback f).potential = L.potential := rfl

theorem pullback_value [DecidableEq J] (L : RankPreparationFamily I J s)
    (f : I → MvPolynomial K ℝ) (x : K → ℝ) :
    (L.pullback f).value x = L.value (fun i => MvPolynomial.aeval (R := ℝ) x (f i)) := by
  apply Finset.sum_congr rfl
  intro i _
  exact (L i).pullback_value f x

theorem Sized.pullback {L : RankPreparationFamily I J s} {D t : ℕ}
    (h : L.Sized D t) (f : I → MvPolynomial K ℝ) : (L.pullback f).Sized D t := h

theorem PreparedHeights.pullback {L : RankPreparationFamily I J s} {p : ℝ} {R : ℕ}
    (hL : L.PreparedHeights p R) (f : I → MvPolynomial K ℝ)
    (hf : ∀ i, (f i).totalDegree ≤ 1) : (L.pullback f).PreparedHeights p R :=
  fun i => (hL i).pullback f hf

end RankPreparationFamily

theorem prepared_polynomial_identity_pullback {I J K : Type} [Fintype J] [DecidableEq J]
    {s : ℕ} (P : VectorPolynomial I ℝ (J → ℝ)) (L : RankPreparationFamily I J s)
    (ip : J → MvPolynomial I ℤ) (c : J → ℝ) (E : VectorPolynomial I ℝ (J → ℝ))
    (hid : P = L.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c) + E)
    (f : I → MvPolynomial K ℝ) :
    substitute f P = (L.pullback f).polynomial + substitute f (integerCoordinates ip) +
      (1 ⊗ₜ[ℝ] c) + substitute f E := by
  rw [hid, map_add, map_add, map_add, substitute_tmul, map_one,
    RankPreparationFamily.pullback_polynomial]

theorem affineFramePolynomial_eq_parameter {I K : Type*} [Fintype K]
    (frame : Option K → I → ℝ) :
    affineFramePolynomial frame = affineParameterSubstitution frame := by
  funext i
  rfl

theorem integer_affineFramePolynomial_map {I K : Type*} [Fintype K]
    (frame : Option K → I → ℤ) :
    (fun i => MvPolynomial.map (Int.castRingHom ℝ) (affineFramePolynomial frame i)) =
      affineParameterSubstitution (fun k i => (frame k i : ℝ)) := by
  funext i
  exact affineFramePolynomial_map (Int.castRingHom ℝ) frame i

theorem integer_affineFramePolynomial_aeval_degree {I K : Type*} [Fintype K]
    (frame : Option K → I → ℤ) (p : MvPolynomial I ℤ) {d : ℕ}
    (hp : p.totalDegree ≤ d) :
    (MvPolynomial.aeval (affineFramePolynomial frame) p).totalDegree ≤ d := by
  exact (aeval_polynomial_totalDegree_le p (affineFramePolynomial frame) hp
    (affineFramePolynomial_degree frame)).trans_eq (Nat.mul_one d)

theorem RankPreparationFamily.pullback_affine_identity {I J K : Type}
    [Fintype J] [DecidableEq J] [Fintype K] {s : ℕ}
    (L : RankPreparationFamily I J s) (P E : VectorPolynomial I ℝ (J → ℝ))
    (ip : J → MvPolynomial I ℤ) (c : J → ℝ)
    (hid : P = L.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c) + E)
    (frame : Option K → I → ℤ) :
    let f := affineParameterSubstitution (fun k i => (frame k i : ℝ))
    substitute f P = (L.pullback f).polynomial +
      integerCoordinates (fun j => MvPolynomial.aeval (affineFramePolynomial frame) (ip j)) +
      (1 ⊗ₜ[ℝ] c) + substitute f E := by
  dsimp only
  have h := L.pullback_identity P E ip c hid (affineFramePolynomial frame)
  dsimp only at h
  rw [integer_affineFramePolynomial_map] at h
  exact h

end Erdos3

end

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators

variable {K X : Type*} [Fintype K]

theorem affineFramePolynomial_top_one (frame : Option K → X → ℝ) (x : X) :
    homogeneousComponent 1 (affineFramePolynomial frame x) =
      ∑ k, C (frame (some k) x) * MvPolynomial.X k := by
  rw [affineFramePolynomial, map_add,
    homogeneousComponent_eq_zero 1 (C (frame none x)) (by simp), zero_add,
    map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [homogeneousComponent_C_mul,
    homogeneousComponent_eq_self (isHomogeneous_X ℝ k)]

theorem scaleMvPolynomialAxes_affineFrame_top_one
    (frame : Option K → X → ℝ) (T : K → ℝ) (x : X) :
    scaleMvPolynomialAxes T (homogeneousComponent 1 (affineFramePolynomial frame x)) =
      ∑ k, C (frame (some k) x * T k) * MvPolynomial.X k := by
  apply MvPolynomial.funext
  intro y
  rw [scaleMvPolynomialAxes_eval, affineFramePolynomial_top_one]
  simp only [eval_sum, map_mul, eval_C, eval_X]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem scaleMvPolynomialAxes_C_mul {ι : Type*}
    (T : ι → ℝ) (c : ℝ) (p : MvPolynomial ι ℝ) :
    scaleMvPolynomialAxes T (C c * p) = C c * scaleMvPolynomialAxes T p := by
  apply MvPolynomial.funext
  intro y
  simp only [scaleMvPolynomialAxes_eval, map_mul, eval_C]

theorem spatialAffineTop_mass_le
    (frame : Option K → X → ℝ) (T : K → ℝ) (hT : ∀ k, 0 ≤ T k) (x : X) :
    realPolynomialMass
      (scaleMvPolynomialAxes T (homogeneousComponent 1 (affineFramePolynomial frame x))) ≤
        ∑ k, |frame (some k) x| * T k := by
  rw [scaleMvPolynomialAxes_affineFrame_top_one]
  apply (realPolynomialMass_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k _
  have h := realPolynomialMass_C_mul_le (frame (some k) x * T k) (MvPolynomial.X k)
  simpa only [realPolynomialMass_X, mul_one, abs_mul, abs_of_nonneg (hT k)] using h

theorem spatialAffineTop_inv_mul_mass_le
    (frame : Option K → X → ℝ) (T : K → ℝ) (hT : ∀ k, 0 ≤ T k)
    (x : X) (N : ℝ) (hN : 0 < N) :
    realPolynomialMass (C N⁻¹ *
      scaleMvPolynomialAxes T (homogeneousComponent 1 (affineFramePolynomial frame x))) ≤
        N⁻¹ * ∑ k, |frame (some k) x| * T k := by
  apply (realPolynomialMass_C_mul_le _ _).trans
  rw [abs_of_pos (inv_pos.mpr hN)]
  exact mul_le_mul_of_nonneg_left (spatialAffineTop_mass_le frame T hT x)
    (inv_nonneg.mpr hN.le)

theorem spatialAffineTop_scaled_inv_mul_mass_le
    (frame : Option K → X → ℝ) (T : K → ℝ) (hT : ∀ k, 0 ≤ T k)
    (x : X) (N : ℝ) (hN : 0 < N) :
    realPolynomialMass (scaleMvPolynomialAxes T
      (C N⁻¹ * homogeneousComponent 1 (affineFramePolynomial frame x))) ≤
        N⁻¹ * ∑ k, |frame (some k) x| * T k := by
  rw [scaleMvPolynomialAxes_C_mul]
  exact spatialAffineTop_inv_mul_mass_le frame T hT x N hN

end Erdos3

end

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators

variable {K X : Type*} [Fintype K]

theorem scaleMvPolynomialAxes_affineFrame_eq_const_add_top
    (frame : Option K → X → ℝ) (T : K → ℝ) (x : X) :
    scaleMvPolynomialAxes T (affineFramePolynomial frame x) =
      C (frame none x) +
        scaleMvPolynomialAxes T
          (homogeneousComponent 1 (affineFramePolynomial frame x)) := by
  apply MvPolynomial.funext
  intro y
  rw [affineFramePolynomial_top_one]
  simp only [scaleMvPolynomialAxes_eval, affineFramePolynomial,
    map_add, eval_C, eval_sum, map_mul, eval_X]

theorem spatialAffineFull_mass_le
    (frame : Option K → X → ℝ) (T : K → ℝ) (hT : ∀ k, 0 ≤ T k) (x : X) :
    realPolynomialMass (scaleMvPolynomialAxes T (affineFramePolynomial frame x)) ≤
      |frame none x| + ∑ k, |frame (some k) x| * T k := by
  rw [scaleMvPolynomialAxes_affineFrame_eq_const_add_top]
  exact (realPolynomialMass_add_le _ _).trans
    (add_le_add (le_of_eq (realPolynomialMass_C _))
      (spatialAffineTop_mass_le frame T hT x))

theorem spatialAffineFull_inv_mul_mass_le
    (frame : Option K → X → ℝ) (T : K → ℝ) (hT : ∀ k, 0 ≤ T k)
    (x : X) (N : ℝ) (hN : 0 < N) :
    realPolynomialMass (C N⁻¹ *
      scaleMvPolynomialAxes T (affineFramePolynomial frame x)) ≤
        |frame none x| / N + N⁻¹ * ∑ k, |frame (some k) x| * T k := by
  apply (realPolynomialMass_C_mul_le _ _).trans
  rw [abs_of_pos (inv_pos.mpr hN)]
  calc
    _ ≤ N⁻¹ * (|frame none x| + ∑ k, |frame (some k) x| * T k) :=
      mul_le_mul_of_nonneg_left (spatialAffineFull_mass_le frame T hT x)
        (inv_nonneg.mpr hN.le)
    _ = _ := by ring

theorem spatialAffineFull_scaled_inv_mul_mass_le
    (frame : Option K → X → ℝ) (T : K → ℝ) (hT : ∀ k, 0 ≤ T k)
    (x : X) (N : ℝ) (hN : 0 < N) :
    realPolynomialMass (scaleMvPolynomialAxes T
      (C N⁻¹ * affineFramePolynomial frame x)) ≤
        |frame none x| / N + N⁻¹ * ∑ k, |frame (some k) x| * T k := by
  rw [scaleMvPolynomialAxes_C_mul]
  exact spatialAffineFull_inv_mul_mass_le frame T hT x N hN

end Erdos3

end

end OAI
