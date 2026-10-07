/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Lattices.AffineLowestLayer
import OAI.Combinatorics.Progressions.Polynomial.MixedWeightedPolynomialRename

namespace OAI

section

namespace Erdos3

open MvPolynomial

def earlierSlot {d : ℕ} (i : Fin d) (j : Fin i.val) : Fin d :=
  ⟨j.val, lt_trans j.isLt i.isLt⟩

def patchVariableWeight {σ : Type*} {d : ℕ} (w : Fin d → ℕ) (i : Fin d) :
    σ ⊕ Fin i.val → ℕ := Sum.elim (fun _ => 1) (fun j => w (earlierSlot i j))

structure PolynomialSlots (σ : Type*) (d : ℕ) (w : Fin d → ℕ) where
  center : (i : Fin d) → MvPolynomial (σ ⊕ Fin i.val) ℝ
  degree : ∀ i, center i ∈ weightedSupportLE (patchVariableWeight w i) (w i)

namespace PolynomialSlots

variable {σ : Type*} {d D E : ℕ} {w : Fin d → ℕ}

noncomputable def slots (A : PolynomialSlots σ d w) (t : σ → ℝ) : TriangularSlots d where
  center x i := aeval (Sum.elim t (fun j => x (earlierSlot i j))) (A.center i)
  lower i x y hxy := by
    apply congrArg (fun f : σ ⊕ Fin i.val → ℝ => aeval f (A.center i))
    funext v
    cases v with
    | inl a => rfl
    | inr j => exact hxy (earlierSlot i j) (by simpa only [Fin.lt_def, earlierSlot] using j.isLt)

noncomputable def prefixSubstitution (I : Fin D → MvPolynomial σ ℝ) (i : Fin E) :
    σ ⊕ Fin (D + i.val) → MvPolynomial (σ ⊕ Fin i.val) ℝ :=
  Sum.elim (fun a => X (Sum.inl a))
    (Fin.addCases (fun j => aeval (fun a => X (Sum.inl a)) (I j))
      (fun j => X (Sum.inr j)))

theorem prefixSubstitution_degree {w : Fin (D + E) → ℕ}
    (I : Fin D → MvPolynomial σ ℝ)
    (hI : ∀ j, I j ∈ weightedSupportLE (fun _ : σ => 1) (w (j.castAdd E)))
    (i : Fin E) (v : σ ⊕ Fin (D + i.val)) :
    prefixSubstitution I i v ∈
      weightedSupportLE (patchVariableWeight (fun j => w (j.natAdd D)) i)
        (patchVariableWeight w (i.natAdd D) v) := by
  cases v with
  | inl a => exact weightedSupportLE_X _ (Sum.inl a)
  | inr j =>
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · simp only [prefixSubstitution, Sum.elim_inr, Fin.addCases_left]
      apply weightedSupportLE_aeval (fun _ : σ => 1)
        (patchVariableWeight (fun j => w (j.natAdd D)) i)
        (fun a => (X (Sum.inl a) : MvPolynomial (σ ⊕ Fin i.val) ℝ))
      · intro a
        exact weightedSupportLE_X _ (Sum.inl a)
      · exact hI k
    · simp only [prefixSubstitution, Sum.elim_inr, Fin.addCases_right]
      exact weightedSupportLE_X (R := ℝ)
        (patchVariableWeight (fun j => w (j.natAdd D)) i) (Sum.inr k)

noncomputable def freezePrefix {w : Fin (D + E) → ℕ}
    (A : PolynomialSlots σ (D + E) w) (I : Fin D → MvPolynomial σ ℝ)
    (hI : ∀ j, I j ∈ weightedSupportLE (fun _ : σ => 1) (w (j.castAdd E))) :
    PolynomialSlots σ E (fun j => w (j.natAdd D)) where
  center i := aeval (prefixSubstitution I i) (A.center (i.natAdd D))
  degree i := weightedSupportLE_aeval _ _ _ (prefixSubstitution_degree I hI i)
    (A.degree (i.natAdd D))

theorem freezePrefix_center_eval {w : Fin (D + E) → ℕ}
    (A : PolynomialSlots σ (D + E) w) (I : Fin D → MvPolynomial σ ℝ)
    (hI : ∀ j, I j ∈ weightedSupportLE (fun _ : σ => 1) (w (j.castAdd E)))
    (t : σ → ℝ) (x : Fin E → ℝ) (i : Fin E) :
    ((A.freezePrefix I hI).slots t).center x i =
      (A.slots t).center (Fin.append (fun j => aeval t (I j)) x) (i.natAdd D) := by
  simp only [slots, freezePrefix, MvPolynomial.comp_aeval_apply]
  apply congrArg (fun f : σ ⊕ Fin (D + i.val) → ℝ => aeval f (A.center (i.natAdd D)))
  funext v
  cases v with
  | inl a => simp [prefixSubstitution]
  | inr j =>
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · simp only [prefixSubstitution, Sum.elim_inr, Fin.addCases_left]
      change aeval (Sum.elim t (fun j => x (earlierSlot i j)))
        (aeval (fun a => (X (Sum.inl a) : MvPolynomial (σ ⊕ Fin i.val) ℝ)) (I k)) =
        Fin.append (fun j => aeval t (I j)) x (k.castAdd E)
      rw [MvPolynomial.comp_aeval_apply, Fin.append_left]
      simp only [aeval_X, Sum.elim_inl]
    · simp only [prefixSubstitution, Sum.elim_inr, Fin.addCases_right]
      change aeval (Sum.elim t (fun j => x (earlierSlot i j)))
        (X (Sum.inr k) : MvPolynomial (σ ⊕ Fin i.val) ℝ) =
        Fin.append (fun j => aeval t (I j)) x ((earlierSlot i k).natAdd D)
      simp only [aeval_X, Sum.elim_inr, Fin.append_right]

end PolynomialSlots

structure PolynomialPatch (σ : Type*) (s d : ℕ) where
  weight : Fin d → ℕ
  weight_pos : ∀ i, 1 ≤ weight i
  weight_le : ∀ i, weight i ≤ s
  weight_mono : Monotone weight
  form : PolynomialSlots σ d weight
  kernel : PatchKernel d

namespace PolynomialPatch

variable {σ : Type*} {s d D E : ℕ}

noncomputable def value (A : PolynomialPatch σ s d) (t : σ → ℝ) : ℝ :=
  (A.form.slots t).patchValue A.kernel

theorem value_mem_Icc (A : PolynomialPatch σ s d) (t : σ → ℝ) :
    A.value t ∈ Set.Icc (0 : ℝ) 1 := (A.form.slots t).patchValue_mem_Icc A.kernel

noncomputable def freezePrefix (A : PolynomialPatch σ s (D + E))
    (I : Fin D → MvPolynomial σ ℝ)
    (hI : ∀ j, I j ∈ weightedSupportLE (fun _ : σ => 1) (A.weight (j.castAdd E)))
    (z : Fin D → ℝ) : PolynomialPatch σ s E where
  weight i := A.weight (i.natAdd D)
  weight_pos i := A.weight_pos _
  weight_le i := A.weight_le _
  weight_mono i j hij := A.weight_mono (by simpa only [Fin.le_def, Fin.val_natAdd,
    Nat.add_le_add_iff_left] using hij)
  form := A.form.freezePrefix I hI
  kernel := A.kernel.freeze z

end PolynomialPatch

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

namespace PolynomialSlots

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}

noncomputable def ofCoordinates (P : Fin d → MvPolynomial σ ℝ)
    (hP : ∀ i, P i ∈ weightedSupportLE (fun _ : σ => 1) (w i)) : PolynomialSlots σ d w where
  center i := aeval (fun a => X (Sum.inl a)) (P i)
  degree i := weightedSupportLE_aeval (fun _ : σ => 1) (patchVariableWeight w i)
    (fun a => X (Sum.inl a)) (fun a => weightedSupportLE_X _ (Sum.inl a)) (hP i)

theorem ofCoordinates_center (P : Fin d → MvPolynomial σ ℝ)
    (hP : ∀ i, P i ∈ weightedSupportLE (fun _ : σ => 1) (w i))
    (t : σ → ℝ) (x : Fin d → ℝ) (i : Fin d) :
    ((ofCoordinates P hP).slots t).center x i = aeval t (P i) := by
  simp only [slots, ofCoordinates, MvPolynomial.comp_aeval_apply, aeval_X, Sum.elim_inl]

end PolynomialSlots

namespace PolynomialPatch

variable {σ : Type*} {s d : ℕ}

noncomputable def ofCoordinates (w : Fin d → ℕ) (hw : ∀ i, 1 ≤ w i)
    (hws : ∀ i, w i ≤ s) (hmono : Monotone w) (P : Fin d → MvPolynomial σ ℝ)
    (hP : ∀ i, P i ∈ weightedSupportLE (fun _ : σ => 1) (w i)) (Φ : PatchKernel d) :
    PolynomialPatch σ s d where
  weight := w
  weight_pos := hw
  weight_le := hws
  weight_mono := hmono
  form := PolynomialSlots.ofCoordinates P hP
  kernel := Φ

theorem ofCoordinates_residual (w : Fin d → ℕ) (hw : ∀ i, 1 ≤ w i)
    (hws : ∀ i, w i ≤ s) (hmono : Monotone w) (P : Fin d → MvPolynomial σ ℝ)
    (hP : ∀ i, P i ∈ weightedSupportLE (fun _ : σ => 1) (w i)) (Φ : PatchKernel d)
    (t : σ → ℝ) (b : Fin d → ℤ) :
    ((ofCoordinates w hw hws hmono P hP Φ).form.slots t).residual b =
      fun i => (b i : ℝ) - aeval t (P i) := by
  funext i
  change (b i : ℝ) - ((PolynomialSlots.ofCoordinates P hP).slots t).center _ i = _
  rw [PolynomialSlots.ofCoordinates_center]

end PolynomialPatch
end Erdos3

end

section

namespace Erdos3

open MvPolynomial

namespace PolynomialSlots

theorem slots_freezePrefix {σ : Type*} {D E : ℕ} {w : Fin (D + E) → ℕ}
    (A : PolynomialSlots σ (D + E) w) (I : Fin D → MvPolynomial σ ℝ)
    (hI : ∀ j, I j ∈ weightedSupportLE (fun _ : σ => 1) (w (j.castAdd E)))
    (t : σ → ℝ) :
    (A.freezePrefix I hI).slots t = (A.slots t).dropPrefix (fun j => aeval t (I j)) := by
  apply TriangularSlots.ext
  intro x i
  exact A.freezePrefix_center_eval I hI t x i

end PolynomialSlots

namespace PolynomialPatch

variable {σ : Type*} {s D E : ℕ}

theorem value_rank_zero (A : PolynomialPatch σ s 0) (t : σ → ℝ) :
    A.value t = A.kernel.value 0 := by
  have h := (A.form.slots t).patchValue_eq_at_residual A.kernel
    (b := 0) (fun i => Fin.elim0 i)
  have hr : (A.form.slots t).residual 0 = 0 := Subsingleton.elim _ _
  simpa only [value, hr] using h

theorem freezePrefix_value (A : PolynomialPatch σ s (D + E))
    (I : Fin D → MvPolynomial σ ℝ)
    (hI : ∀ j, I j ∈ weightedSupportLE (fun _ : σ => 1) (A.weight (j.castAdd E)))
    (z : Fin D → ℝ) (t : σ → ℝ) :
    (A.freezePrefix I (by exact hI) z).value t =
      ((A.form.slots t).dropPrefix (fun j => aeval t (I j))).patchValue (A.kernel.freeze z) := by
  change ((A.form.freezePrefix I hI).slots t).patchValue _ = _
  rw [PolynomialSlots.slots_freezePrefix]
  rfl

theorem freezePrefix_error (A : PolynomialPatch σ s (D + E))
    (I : Fin D → MvPolynomial σ ℝ)
    (hI : ∀ j, I j ∈ weightedSupportLE (fun _ : σ => 1) (A.weight (j.castAdd E)))
    (z : Fin D → ℝ) (t : σ → ℝ) (b : Fin D → ℤ) {ε : ℝ}
    (hint : ∀ j, aeval t (I j) = (b j : ℝ))
    (hz : ∀ i, |z i| ≤ 1 / 4) (hε : ε < 1 / 12)
    (hclose : dist ((A.form.slots t).takePrefix.residual b) z ≤ ε) :
    dist (A.value t) ((A.freezePrefix I hI z).value t) ≤ A.kernel.lip * ε := by
  have h := (A.form.slots t).takePrefix.patchValue_freeze_prefix
    (A.form.slots t).dropPrefix A.kernel b z hz hε hclose
  rw [TriangularSlots.append_take_drop] at h
  rw [freezePrefix_value, show (fun j => aeval t (I j)) = (fun j => (b j : ℝ)) from funext hint]
  exact h

end PolynomialPatch

noncomputable def shiftedParameterPolynomials {σ : Type*} {D : ℕ}
    (I : Fin D → MvPolynomial σ ℝ) (t₀ : σ → ℝ) (b₀ : Fin D → ℤ) :
    Fin D → MvPolynomial σ ℝ := fun i => C (b₀ i : ℝ) + I i - C (aeval t₀ (I i))

theorem shiftedParameterPolynomials_degree {σ : Type*} {D : ℕ}
    (I : Fin D → MvPolynomial σ ℝ) (t₀ : σ → ℝ) (b₀ : Fin D → ℤ)
    (w : Fin D → ℕ)
    (hI : ∀ i, I i ∈ weightedSupportLE (fun _ : σ => 1) (w i)) :
    ∀ i, shiftedParameterPolynomials I t₀ b₀ i ∈ weightedSupportLE (fun _ : σ => 1) (w i) := by
  intro i
  exact (weightedSupportLE _ _).sub_mem
    ((weightedSupportLE _ _).add_mem (weightedSupportLE_C _ _ _) (hI i))
    (weightedSupportLE_C _ _ _)

theorem shiftedParameterPolynomials_eval {σ : Type*} {D : ℕ}
    (I : Fin D → MvPolynomial σ ℝ) (t₀ t : σ → ℝ) (b₀ : Fin D → ℤ) :
    ∀ i, aeval t (shiftedParameterPolynomials I t₀ b₀ i) =
      (b₀ i : ℝ) + aeval t (I i) - aeval t₀ (I i) := by
  intro i
  simp only [shiftedParameterPolynomials, map_add, map_sub, aeval_C,
    Algebra.algebraMap_self, RingHom.id_apply]

namespace PolynomialPatch

theorem exists_freeze_affine_layer {σ : Type*} {s D E : ℕ}
    (A : PolynomialPatch σ s (D + E))
    (M : Matrix (Fin D) (Fin D) ℝ) (hM : ∀ i j, i ≤ j → M i j = 0)
    (U : Set (σ → ℝ)) (P : (σ → ℝ) → Fin D → ℝ)
    (I : Fin D → MvPolynomial σ ℝ) (v : (σ → ℝ) → Fin D → ℤ)
    (hI : ∀ j, I j ∈ weightedSupportLE (fun _ : σ => 1) (A.weight (j.castAdd E)))
    (hint : ∀ t ∈ U, ∀ j, aeval t (I j) = (v t j : ℝ))
    (hhead : ∀ t ∈ U, (A.form.slots t).takePrefix = TriangularSlots.affineBlock M hM (P t))
    (t₀ : σ → ℝ) (ht₀ : t₀ ∈ U) (bref : Fin (D + E) → ℤ)
    (href : A.kernel.value ((A.form.slots t₀).residual bref) ≠ 0)
    {ε : ℝ} (hε : ε < 1 / 12)
    (hosc : ∀ t ∈ U, ‖(1 - M).mulVec
      ((P t - fun j => aeval t (I j)) - (P t₀ - fun j => aeval t₀ (I j)))‖ ≤ ε) :
    ∃ F : PolynomialPatch σ s E, F.kernel.lip = A.kernel.lip ∧
      (∀ i, F.weight i = A.weight (i.natAdd D)) ∧
      ∀ t ∈ U, dist (A.value t) (F.value t) ≤ A.kernel.lip * ε := by
  let b₀ := slotPrefix bref
  let z := (A.form.slots t₀).takePrefix.residual b₀
  let J := shiftedParameterPolynomials I t₀ b₀
  have hJ : ∀ j, J j ∈ weightedSupportLE (fun _ : σ => 1) (A.weight (j.castAdd E)) :=
    shiftedParameterPolynomials_degree I t₀ b₀ _ hI
  refine ⟨A.freezePrefix J hJ z, rfl, (fun _ => rfl), ?_⟩
  have hz : ∀ i, |z i| ≤ 1 / 4 := by
    intro i
    have h := A.kernel.support _ href (i.castAdd E)
    simpa only [z, b₀, TriangularSlots.takePrefix_residual, slotPrefix] using h
  intro t ht
  have hJvalue : ∀ j, aeval t (J j) = (shiftedIntegerBlock v t₀ b₀ t j : ℝ) := by
    intro j
    simp only [J, shiftedParameterPolynomials_eval, hint t ht, hint t₀ ht₀,
      shiftedIntegerBlock, Pi.add_apply, Pi.sub_apply, Int.cast_sub, Int.cast_add]
  apply A.freezePrefix_error J hJ z t (shiftedIntegerBlock v t₀ b₀ t) hJvalue hz hε
  change dist ((A.form.slots t).takePrefix.residual (shiftedIntegerBlock v t₀ b₀ t))
    ((A.form.slots t₀).takePrefix.residual b₀) ≤ ε
  rw [hhead t ht, hhead t₀ ht₀, affine_residual_shift_dist]
  simpa only [hint t ht, hint t₀ ht₀] using hosc t ht

end PolynomialPatch

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

namespace PolynomialSlots

variable {σ τ : Type*} {d : ℕ} {w : Fin d → ℕ}

noncomputable def parameterSubstitution (f : σ → MvPolynomial τ ℝ) (i : Fin d) :
    σ ⊕ Fin i.val → MvPolynomial (τ ⊕ Fin i.val) ℝ :=
  Sum.elim (fun a => aeval (fun b => X (Sum.inl b)) (f a)) (fun j => X (Sum.inr j))

theorem parameterSubstitution_degree (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ a, f a ∈ weightedSupportLE (fun _ : τ => 1) 1) (i : Fin d)
    (v : σ ⊕ Fin i.val) :
    parameterSubstitution f i v ∈
      weightedSupportLE (patchVariableWeight (σ := τ) w i)
        (patchVariableWeight (σ := σ) w i v) := by
  cases v with
  | inl a =>
    apply weightedSupportLE_aeval (fun _ : τ => 1) (patchVariableWeight w i)
    · intro b
      exact weightedSupportLE_X _ (Sum.inl b)
    · exact hf a
  | inr j => exact weightedSupportLE_X _ (Sum.inr j)

noncomputable def reparam (A : PolynomialSlots σ d w) (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ a, f a ∈ weightedSupportLE (fun _ : τ => 1) 1) : PolynomialSlots τ d w where
  center i := aeval (parameterSubstitution f i) (A.center i)
  degree i := weightedSupportLE_aeval _ _ _ (parameterSubstitution_degree f hf i) (A.degree i)

theorem reparam_slots (A : PolynomialSlots σ d w) (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ a, f a ∈ weightedSupportLE (fun _ : τ => 1) 1) (t : τ → ℝ) :
    (A.reparam f hf).slots t = A.slots (fun a => aeval t (f a)) := by
  apply TriangularSlots.ext
  intro x i
  simp only [slots, reparam, MvPolynomial.comp_aeval_apply]
  apply congrArg (fun g : σ ⊕ Fin i.val → ℝ => aeval g (A.center i))
  funext v
  cases v with
  | inl a =>
    simp only [parameterSubstitution, Sum.elim_inl, MvPolynomial.comp_aeval_apply, aeval_X]
  | inr j => simp [parameterSubstitution]

end PolynomialSlots

namespace PolynomialPatch

variable {σ τ : Type*} {s d : ℕ}

noncomputable def reparam (A : PolynomialPatch σ s d) (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ a, f a ∈ weightedSupportLE (fun _ : τ => 1) 1) : PolynomialPatch τ s d where
  weight := A.weight
  weight_pos := A.weight_pos
  weight_le := A.weight_le
  weight_mono := A.weight_mono
  form := A.form.reparam f hf
  kernel := A.kernel

theorem reparam_value (A : PolynomialPatch σ s d) (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ a, f a ∈ weightedSupportLE (fun _ : τ => 1) 1) (t : τ → ℝ) :
    (A.reparam f hf).value t = A.value (fun a => aeval t (f a)) := by
  change ((A.form.reparam f hf).slots t).patchValue A.kernel = _
  rw [PolynomialSlots.reparam_slots]
  rfl

noncomputable def affineLineParameters (a q : σ → ℝ) : σ → MvPolynomial Unit ℝ :=
  fun i => C (a i) + q i • X ()

theorem affineLineParameters_degree (a q : σ → ℝ) (i : σ) :
    affineLineParameters a q i ∈ weightedSupportLE (fun _ : Unit => 1) 1 :=
  (weightedSupportLE _ _).add_mem (weightedSupportLE_C _ _ _)
    ((weightedSupportLE _ _).smul_mem _ (weightedSupportLE_X _ ()))

noncomputable def onAffineLine (A : PolynomialPatch σ s d) (a q : σ → ℝ) :
    PolynomialPatch Unit s d := A.reparam (affineLineParameters a q) (affineLineParameters_degree a q)

theorem onAffineLine_value (A : PolynomialPatch σ s d) (a q : σ → ℝ) (n : ℝ) :
    (A.onAffineLine a q).value (fun _ => n) = A.value (fun i => a i + q i * n) := by
  rw [onAffineLine, reparam_value]
  congr 1
  funext i
  simp [affineLineParameters]

end PolynomialPatch
end Erdos3

end

section

namespace Erdos3.PolynomialPatch

open MvPolynomial

variable {X : Type*} {s d : ℕ}

noncomputable def shiftedKernel (A : PolynomialPatch X s d)
    (v : Fin d → ℝ) (Φ : PatchKernel d) : PolynomialPatch X s d where
  weight := A.weight
  weight_pos := A.weight_pos
  weight_le := A.weight_le
  weight_mono := A.weight_mono
  form := {
    center := fun i => A.form.center i + C (v i)
    degree := fun i => (weightedSupportLE _ _).add_mem (A.form.degree i)
      (weightedSupportLE_C _ _ _) }
  kernel := Φ

theorem shiftedKernel_residual (A : PolynomialPatch X s d)
    (v : Fin d → ℝ) (Φ : PatchKernel d) (t : X → ℝ) (b : Fin d → ℤ) :
    ((A.shiftedKernel v Φ).form.slots t).residual b = (A.form.slots t).residual b - v := by
  funext i
  simp only [shiftedKernel, TriangularSlots.residual, PolynomialSlots.slots,
    map_add, aeval_C, Pi.sub_apply, Algebra.algebraMap_self, RingHom.id_apply]
  ring

theorem shiftedKernel_value (A : PolynomialPatch X s d)
    (v : Fin d → ℝ) (Φ : PatchKernel d) (t : X → ℝ) :
    (A.shiftedKernel v Φ).value t =
      ∑' b, Φ.value ((A.form.slots t).residual b - v) := by
  simp only [value, TriangularSlots.patchValue, shiftedKernel_residual]
  rfl

end Erdos3.PolynomialPatch

end

section

namespace Erdos3

open MvPolynomial

namespace PolynomialSlots

variable {σ : Type*} {d n D E : ℕ}

noncomputable def placementSubstitution (f : Fin d → Fin n) (k : Fin n) (i : Fin d) :
    σ ⊕ Fin i.val → MvPolynomial (σ ⊕ Fin k.val) ℝ :=
  Sum.elim (fun a => X (Sum.inl a)) (fun j =>
    if h : (f (earlierSlot i j)).val < k.val then X (Sum.inr ⟨_, h⟩) else 0)

theorem placementSubstitution_degree {w : Fin d → ℕ} {v : Fin n → ℕ}
    (f : Fin d → Fin n) (hweight : ∀ i, v (f i) = w i) (k : Fin n) (i : Fin d)
    (a : σ ⊕ Fin i.val) :
    placementSubstitution f k i a ∈
      weightedSupportLE (patchVariableWeight v k) (patchVariableWeight w i a) := by
  cases a with
  | inl a => exact weightedSupportLE_X _ (Sum.inl a)
  | inr j =>
    simp only [placementSubstitution, Sum.elim_inr]
    split_ifs with h
    · have hX := weightedSupportLE_X (R := ℝ) (patchVariableWeight (σ := σ) v k)
        (Sum.inr (⟨(f (earlierSlot i j)).val, h⟩ : Fin k.val))
      change _ ∈ weightedSupportLE _ (v (f (earlierSlot i j))) at hX
      rw [hweight] at hX
      exact hX
    · exact (weightedSupportLE _ _).zero_mem

noncomputable def placeCenter {w : Fin d → ℕ} (A : PolynomialSlots σ d w)
    (f : Fin d → Fin n) (k : Fin n) (i : Fin d) :
    MvPolynomial (σ ⊕ Fin k.val) ℝ := aeval (placementSubstitution f k i) (A.center i)

theorem placeCenter_degree {w : Fin d → ℕ} {v : Fin n → ℕ}
    (A : PolynomialSlots σ d w) (f : Fin d → Fin n)
    (hweight : ∀ i, v (f i) = w i) (k : Fin n) (i : Fin d) :
    A.placeCenter f k i ∈ weightedSupportLE (patchVariableWeight v k) (w i) :=
  weightedSupportLE_aeval _ _ _ (placementSubstitution_degree f hweight k i) (A.degree i)

theorem placeCenter_eval {w : Fin d → ℕ} (A : PolynomialSlots σ d w)
    (f : Fin d → Fin n) (hf : StrictMono f) (i : Fin d) (t : σ → ℝ) (x : Fin n → ℝ) :
    aeval (Sum.elim t (fun j => x (earlierSlot (f i) j))) (A.placeCenter f (f i) i) =
      (A.slots t).center (fun j => x (f j)) i := by
  simp only [placeCenter, MvPolynomial.comp_aeval_apply, slots]
  apply congrArg (fun g : σ ⊕ Fin i.val → ℝ => aeval g (A.center i))
  funext a
  cases a with
  | inl a => simp [placementSubstitution]
  | inr j =>
    have h : (f (earlierSlot i j)).val < (f i).val :=
      hf (show earlierSlot i j < i from j.isLt)
    simp only [placementSubstitution, Sum.elim_inr, dite_eq_left h, aeval_X]
    rfl

noncomputable def interleave {w : Fin D → ℕ} {v : Fin E → ℕ}
    (A : PolynomialSlots σ D w) (B : PolynomialSlots σ E v) (I : SlotInterleaving D E) :
    PolynomialSlots σ (D + E) (I.fill w v) where
  center k := Fin.addCases (A.placeCenter I.left k) (B.placeCenter I.right k) (I.perm k)
  degree k := by
    change Fin.addCases (A.placeCenter I.left k) (B.placeCenter I.right k) (I.perm k) ∈
      weightedSupportLE (patchVariableWeight (I.fill w v) k) (Fin.append w v (I.perm k))
    generalize I.perm k = z
    refine Fin.addCases (fun i => ?_) (fun i => ?_) z
    · simpa only [Fin.addCases_left, Fin.append_left] using
        A.placeCenter_degree I.left (fun j => I.fill_left w v j) k i
    · simpa only [Fin.addCases_right, Fin.append_right] using
        B.placeCenter_degree I.right (fun j => I.fill_right w v j) k i

@[simp] theorem interleave_center_left {w : Fin D → ℕ} {v : Fin E → ℕ}
    (A : PolynomialSlots σ D w) (B : PolynomialSlots σ E v) (I : SlotInterleaving D E)
    (i : Fin D) : (A.interleave B I).center (I.left i) = A.placeCenter I.left (I.left i) i := by
  simp [interleave, SlotInterleaving.left]

@[simp] theorem interleave_center_right {w : Fin D → ℕ} {v : Fin E → ℕ}
    (A : PolynomialSlots σ D w) (B : PolynomialSlots σ E v) (I : SlotInterleaving D E)
    (i : Fin E) : (A.interleave B I).center (I.right i) = B.placeCenter I.right (I.right i) i := by
  simp [interleave, SlotInterleaving.right]

theorem interleave_slots {w : Fin D → ℕ} {v : Fin E → ℕ}
    (A : PolynomialSlots σ D w) (B : PolynomialSlots σ E v) (I : SlotInterleaving D E)
    (t : σ → ℝ) : (A.interleave B I).slots t = (A.slots t).interleave (B.slots t) I := by
  apply TriangularSlots.ext
  intro x k
  apply I.cases (p := fun k => ((A.interleave B I).slots t).center x k =
    ((A.slots t).interleave (B.slots t) I).center x k) _ _ k
  · intro i
    change aeval _ ((A.interleave B I).center (I.left i)) = _
    rw [interleave_center_left]
    simpa only [TriangularSlots.interleave, SlotInterleaving.fill_left] using
      A.placeCenter_eval I.left I.left_strictMono i t x
  · intro i
    change aeval _ ((A.interleave B I).center (I.right i)) = _
    rw [interleave_center_right]
    simpa only [TriangularSlots.interleave, SlotInterleaving.fill_right] using
      B.placeCenter_eval I.right I.right_strictMono i t x

end PolynomialSlots

end Erdos3

end

section

namespace Erdos3

namespace PolynomialPatch

variable {σ : Type*} {s D E : ℕ}

def constant (σ : Type*) (s : ℕ) (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    PolynomialPatch σ s 0 where
  weight := Fin.elim0
  weight_pos := fun i => Fin.elim0 i
  weight_le := fun i => Fin.elim0 i
  weight_mono i := Fin.elim0 i
  form := { center := fun i => Fin.elim0 i, degree := fun i => Fin.elim0 i }
  kernel := {
    value := fun _ => c
    nonneg := fun _ => hc.1
    le_one := fun _ => hc.2
    support := fun _ _ i => Fin.elim0 i
    lip := 0
    lipschitz := LipschitzWith.const c }

@[simp] theorem constant_value (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) (t : σ → ℝ) :
    (constant σ s c hc).value t = c := by
  exact ((constant σ s c hc).form.slots t).patchValue_eq_at_residual (constant σ s c hc).kernel
    (b := 0) (fun i => Fin.elim0 i)

@[simp] theorem constant_lip (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    (constant σ s c hc).kernel.lip = 0 := rfl

noncomputable def product (A : PolynomialPatch σ s D) (B : PolynomialPatch σ s E) :
    PolynomialPatch σ s (D + E) :=
  let I := SlotInterleaving.sorted A.weight B.weight A.weight_mono B.weight_mono
  { weight := I.fill A.weight B.weight
    weight_pos := I.cases (fun i => by simpa only [SlotInterleaving.fill_left] using A.weight_pos i)
      (fun i => by simpa only [SlotInterleaving.fill_right] using B.weight_pos i)
    weight_le := I.cases (fun i => by simpa only [SlotInterleaving.fill_left] using A.weight_le i)
      (fun i => by simpa only [SlotInterleaving.fill_right] using B.weight_le i)
    weight_mono := SlotInterleaving.sorted_weight_mono _ _ _ _
    form := A.form.interleave B.form I
    kernel := A.kernel.product B.kernel I }

@[simp] theorem product_lip (A : PolynomialPatch σ s D) (B : PolynomialPatch σ s E) :
    (A.product B).kernel.lip = A.kernel.lip + B.kernel.lip := rfl

@[simp] theorem product_value (A : PolynomialPatch σ s D) (B : PolynomialPatch σ s E)
    (t : σ → ℝ) : (A.product B).value t = A.value t * B.value t := by
  let I := SlotInterleaving.sorted A.weight B.weight A.weight_mono B.weight_mono
  change ((A.form.interleave B.form I).slots t).patchValue (A.kernel.product B.kernel I) = _
  rw [PolynomialSlots.interleave_slots, TriangularSlots.interleave_patchValue]
  rfl

theorem exists_finset_product {ι : Type*} (T : Finset ι) (d : ι → ℕ)
    (A : ∀ i, PolynomialPatch σ s (d i)) :
    ∃ P : PolynomialPatch σ s (∑ i ∈ T, d i),
      (∀ t, P.value t = ∏ i ∈ T, (A i).value t) ∧
      P.kernel.lip = ∑ i ∈ T, (A i).kernel.lip := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, Finset.prod_empty]
    exact ⟨constant σ s 1 ⟨zero_le_one, le_rfl⟩,
      fun t => constant_value 1 ⟨zero_le_one, le_rfl⟩ t, rfl⟩
  | @insert i T hi ih =>
    obtain ⟨P, hP, hPlip⟩ := ih
    rw [Finset.sum_insert hi]
    refine ⟨(A i).product P, ?_, ?_⟩
    · intro t
      rw [product_value, hP, Finset.prod_insert hi]
    · rw [product_lip, hPlip, Finset.sum_insert hi]

theorem exists_fin_product {n d : ℕ} (A : Fin n → PolynomialPatch σ s d) :
    ∃ P : PolynomialPatch σ s (n * d),
      (∀ t, P.value t = ∏ i, (A i).value t) ∧ P.kernel.lip = ∑ i, (A i).kernel.lip := by
  have h := exists_finset_product Finset.univ (fun _ : Fin n => d) A
  have hsum : (∑ _i : Fin n, d) = n * d := by simp
  rw [hsum] at h
  exact h

theorem exists_background_product {d₀ n d : ℕ} (B : PolynomialPatch σ s d₀)
    (A : Fin n → PolynomialPatch σ s d) :
    ∃ P : PolynomialPatch σ s (d₀ + n * d),
      (∀ t, P.value t = B.value t * ∏ i, (A i).value t) ∧
      P.kernel.lip = B.kernel.lip + ∑ i, (A i).kernel.lip := by
  obtain ⟨P, hP, hPlip⟩ := exists_fin_product A
  exact ⟨B.product P, fun t => by rw [product_value, hP], by rw [product_lip, hPlip]⟩

end PolynomialPatch

end Erdos3

end

section

namespace Erdos3
namespace PolynomialPatch

open MvPolynomial

variable {σ τ : Type*} {s : ℕ}

theorem exists_reparam_product {ι : Type*} (T : Finset ι) (d : ι → ℕ)
    (ρ : ι → Type*) (A : ∀ i, PolynomialPatch (ρ i) s (d i))
    (f : ∀ i, ρ i → MvPolynomial τ ℝ)
    (hf : ∀ i a, f i a ∈ weightedSupportLE (fun _ : τ => 1) 1) :
    ∃ P : PolynomialPatch τ s (∑ i ∈ T, d i),
      (∀ t, P.value t = ∏ i ∈ T, (A i).value (fun a => aeval t (f i a))) ∧
      P.kernel.lip = ∑ i ∈ T, (A i).kernel.lip := by
  obtain ⟨P, hP, hPlip⟩ := exists_finset_product T d (fun i => (A i).reparam (f i) (hf i))
  exact ⟨P, fun t => by simpa only [reparam_value] using hP t, hPlip⟩

theorem product_lip_exp_le {D E : ℕ} (A : PolynomialPatch σ s D)
    (B : PolynomialPatch σ s E) {U V : ℝ}
    (hA : (A.kernel.lip : ℝ) + 1 ≤ Real.exp U)
    (hB : (B.kernel.lip : ℝ) + 1 ≤ Real.exp V) :
    ((A.product B).kernel.lip : ℝ) + 1 ≤ Real.exp (U + V) := by
  rw [product_lip, NNReal.coe_add, Real.exp_add]
  calc
    (A.kernel.lip : ℝ) + B.kernel.lip + 1 ≤
        (A.kernel.lip + 1) * (B.kernel.lip + 1) := by
      nlinarith [mul_nonneg A.kernel.lip.coe_nonneg B.kernel.lip.coe_nonneg]
    _ ≤ Real.exp U * Real.exp V :=
      mul_le_mul hA hB (by positivity) (Real.exp_pos _).le

theorem exists_fin_product_budget {n d : ℕ} (A : Fin n → PolynomialPatch σ s d)
    {U : ℝ} (hU : 0 ≤ U) (hA : ∀ i, ((A i).kernel.lip : ℝ) + 1 ≤ Real.exp U) :
    ∃ P : PolynomialPatch σ s (n * d),
      (∀ t, P.value t = ∏ i, (A i).value t) ∧
      P.kernel.lip = ∑ i, (A i).kernel.lip ∧
      (P.kernel.lip : ℝ) + 1 ≤ Real.exp (U + Real.log ((n : ℝ) + 1)) := by
  obtain ⟨P, hP, hPlip⟩ := exists_fin_product A
  refine ⟨P, hP, hPlip, ?_⟩
  have hsum : (∑ i, ((A i).kernel.lip : ℝ)) ≤ (n : ℝ) * Real.exp U := by
    have h := Finset.sum_le_sum (s := Finset.univ)
      (f := fun i : Fin n => ((A i).kernel.lip : ℝ))
      (g := fun _ => Real.exp U) (fun i _ => (le_add_of_nonneg_right zero_le_one).trans (hA i))
    simpa using h
  have hlip : (P.kernel.lip : ℝ) = ∑ i, ((A i).kernel.lip : ℝ) := by
    rw [hPlip, NNReal.coe_sum]
  rw [hlip, Real.exp_add, Real.exp_log (by positivity : 0 < (n : ℝ) + 1)]
  have hunit : 1 ≤ Real.exp U := Real.one_le_exp_iff.mpr hU
  nlinarith

theorem exists_background_product_budget {d₀ n d : ℕ} (B : PolynomialPatch σ s d₀)
    (A : Fin n → PolynomialPatch σ s d) {U : ℝ}
    (hB : (B.kernel.lip : ℝ) + 1 ≤ Real.exp U)
    (hA : ∀ i, ((A i).kernel.lip : ℝ) + 1 ≤ Real.exp U) :
    ∃ P : PolynomialPatch σ s (d₀ + n * d),
      (∀ t, P.value t = B.value t * ∏ i, (A i).value t) ∧
      P.kernel.lip = B.kernel.lip + ∑ i, (A i).kernel.lip ∧
      (P.kernel.lip : ℝ) + 1 ≤ Real.exp (U + Real.log ((n : ℝ) + 1)) := by
  obtain ⟨P, hP, hPlip⟩ := exists_background_product B A
  refine ⟨P, hP, hPlip, ?_⟩
  have hsum : (∑ i, ((A i).kernel.lip : ℝ)) ≤ (n : ℝ) * Real.exp U := by
    have h := Finset.sum_le_sum (s := Finset.univ)
      (f := fun i : Fin n => ((A i).kernel.lip : ℝ))
      (g := fun _ => Real.exp U) (fun i _ => (le_add_of_nonneg_right zero_le_one).trans (hA i))
    simpa using h
  rw [hPlip, NNReal.coe_add, NNReal.coe_sum, Real.exp_add,
    Real.exp_log (by positivity : 0 < (n : ℝ) + 1)]
  nlinarith

end PolynomialPatch
end Erdos3

end

end OAI
