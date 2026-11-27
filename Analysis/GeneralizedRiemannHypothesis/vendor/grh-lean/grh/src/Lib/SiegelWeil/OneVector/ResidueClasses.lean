import Lib.SiegelWeil.OneVector.FinitePlaceDensity

/-!
# Classes modulo a lattice at a finite place

Let `A` be a finite place, `R` its ring of integers, `κ` an index type, `L` the lattice `R^κ` of
integral vectors in `A^κ` and `g` a unit of `A`.

* `New.Floors.IntegralPlace.latticeMultiple`, `New.Floors.IntegralPlace.residueClass`: the lattice
  `g L` and its classes. They are compact and, for finite `κ`, open of volume `modulus g ^ card κ`.

Notions from other files:

* `New.Floors.IntegralPlace`: the structure `P` that makes `A` a finite place; `P.integers` is the
  ring of integers `R`, and `P.modulus x` is the inverse of the generalised index of `x R` in `R`.
-/

namespace New.Floors.IntegralPlace

open MeasureTheory ENNReal Fintype Place Set Function SemilocalField

variable {A κ : Type} [SemilocalField A] [StarRing A] [P : IntegralPlace A]

variable (κ) in
/-- The lattice `g L`, where `L = R^κ` is the lattice of vectors with entries in the ring of
integers `R` of the finite place `A`: the vectors `y` with every `g⁻¹ * y i` in `R`. -/
def latticeMultiple (g : Aˣ) : AddSubgroup (κ → A) :=
  .pi univ fun _ : κ ↦ P.integers.toAddSubgroup.comap (AddMonoidHom.mulLeft g⁻¹.val)

/-- A vector lies in the lattice `g L`, `L` the lattice of integral vectors, exactly when all its
entries, divided by `g`, lie in the ring of integers `P.integers` of the place. -/
lemma mem_latticeMultiple {g : Aˣ} {y : κ → A} :
    y ∈ latticeMultiple κ g ↔ ∀ i : κ, g⁻¹.val * y i ∈ P.integers := by
  simp [latticeMultiple, AddSubgroup.mem_pi]

/-- The lattice `g L`, `L = R^κ`, is the product of copies of the set `g R`, where `R` is the ring
of integers of the finite place `A`. -/
lemma coe_latticeMultiple (g : Aˣ) :
    (latticeMultiple κ g : Set (κ → A)) = univ.pi fun _ : κ ↦ {x : A | g⁻¹.val * x ∈ P.integers} :=
  rfl

/-- The lattice `g L`, where `L = R^κ` and `R = P.integers` is the ring of integers of the finite
place `A`, is compact. -/
lemma isCompact_latticeMultiple (g : Aˣ) : IsCompact (latticeMultiple κ g : Set (κ → A)) := by
  have h_factor : IsCompact {x : A | g⁻¹.val * x ∈ P.integers} := by
    change IsCompact ((fun x : A ↦ g⁻¹ • x) ⁻¹' (P.integers : Set A))
    exact (Homeomorph.smul g⁻¹).isCompact_preimage.2 isCompact_O
  rw [coe_latticeMultiple]
  exact isCompact_univ_pi fun _ ↦ h_factor

/-- The class `x₀ + g L` of `x₀` modulo the lattice `g L`, where `L` is the lattice of integral
vectors. -/
def residueClass (g : Aˣ) (x₀ : κ → A) : Set (κ → A) :=
  {x : κ → A | x - x₀ ∈ latticeMultiple κ g}

/-- The class `x₀ + g L` of a vector `x₀` modulo `g L`, `L` the lattice of integral vectors, is
compact. -/
lemma isCompact_residueClass (g : Aˣ) (x₀ : κ → A) : IsCompact (residueClass g x₀) :=
  (Homeomorph.subRight x₀).isCompact_preimage.2 (isCompact_latticeMultiple g)

variable [Fintype κ]

/-- For a finite index type `κ`, the lattice `g L` is open, where `L = R^κ` and `R = P.integers` is
the ring of integers of the finite place `A`. -/
lemma isOpen_latticeMultiple (g : Aˣ) : IsOpen (latticeMultiple κ g : Set (κ → A)) := by
  have h_factor : IsOpen {x : A | g⁻¹.val * x ∈ P.integers} :=
    isOpen_O.preimage (continuous_const_mul _)
  rw [coe_latticeMultiple]
  exact isOpen_set_pi finite_univ fun _ _ ↦ h_factor

/-- For a unit `g` of the finite place `A` and the lattice `L = R^κ` of integral vectors, the
lattice `g L` has volume `modulus g ^ card κ`; here `modulus g` is the volume of `g R`. -/
lemma volume_latticeMultiple (g : Aˣ) :
    volume (latticeMultiple κ g : Set (κ → A)) = P.modulus g ^ card κ := by
  rw [coe_latticeMultiple, volume_pi_pi, volume_setOf_mul_mem, modulus_inv, inv_inv,
    Finset.prod_const, Finset.card_univ]

/-- The class `x₀ + g L` of a vector `x₀` modulo `g L`, `L` the lattice of integral vectors, is
open when the index type is finite. -/
lemma isOpen_residueClass (g : Aˣ) (x₀ : κ → A) : IsOpen (residueClass g x₀) :=
  (isOpen_latticeMultiple g).preimage (continuous_sub_right x₀)

/-- For a unit `g` of the finite place `A` and the lattice `L` of integral vectors, each class
`x₀ + g L` has volume `modulus g ^ card κ`; here `modulus g` is the volume of `g R`. -/
lemma volume_residueClass (g : Aˣ) (x₀ : κ → A) :
    volume (residueClass g x₀) = P.modulus g ^ card κ := by
  rw [← volume_latticeMultiple]
  change volume ((fun x : κ → A ↦ x - x₀) ⁻¹' latticeMultiple κ g) = _
  exact (measurePreserving_sub_right volume x₀).measure_preimage
    (isOpen_latticeMultiple g).measurableSet.nullMeasurableSet

end New.Floors.IntegralPlace
