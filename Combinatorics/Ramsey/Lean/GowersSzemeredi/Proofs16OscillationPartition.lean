import GowersSzemeredi.Proofs16CellOscillation
import GowersSzemeredi.Proofs16Slicing
import GowersSzemeredi.Proofs05BoxTransport

/-! Oscillation partitions from the multilinear partition theorem.

`OscillationPartitionsExist` (`Proofs16CellOscillation`) is the only open
input of the variety route. Its conditions `L_k(y)·x` are only
Freiman-bilinear, so the multilinear partition theorem does not apply to
them directly. Two stages fix this.

1. **Linear stage.** Partition `P` so that every `γ x` (`γ ∈ Γ`) and every
   `ψ y` (`ψ ∈ Ψ`) has image diameter at most `4N/H₁ ≤ ρN/4` on each cell.
2. **Bilinear stage.** A cell that meets `V(ρ/2)` has its whole `y`-range in
   `B(Ψ;ρ)` (`ρN/2 + ρN/4 ≤ ρN`). There, along the cell's `y`-axis, each
   `L_k` is affine (second differences vanish by Freiman-linearity). So
   `x ↦ L_k(x₁)·x₀` agrees on the cell with a genuinely multilinear map
   (`freiman_column_multilinearOn`). Partition the cell again, so that
   these `r` maps have diameter at most `4N/H₂ ≤ ρN/2`. Cells that miss
   `V(ρ/2)` are kept whole.

Every final cell then misses `V(ρ/2)` or has oscillation at most `ρN/2`.

The multilinear partition theorem is the peer's
`exists_simultaneous_multilinear_partition_bound`
(`Proofs05SimultaneousMultiaffinePartition`), whose exponent is polynomial
in the number of maps. It imports the OAI port, which is not built on this
machine. So it enters as the hypothesis `MultilinearDiameterPartition K p`,
the verbatim dimension-two body of that theorem.
`Proofs16OscillationPartitionInst` discharges it.

* `freiman_column_multilinearOn`: Freiman-linear `ℓ` on `B` and a box whose
  `y`-range lies in `B` give `MultilinearOn (x ↦ ℓ(x₁)·x₀)`.
* `linearForms`: the `|Γ| + |Ψ|` linear maps.
* `oscillation_cell_refine`: the bilinear stage on one cell.
* `oscillation_partition_of_scales`: both stages, for explicit scales
  `H₁ ≥ H₂^(p(r+1)^8)` and `P.width ≥ H₁^(p(|Γ|+|Ψ|+1)^8)`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical

/-- The dimension-two multilinear partition theorem, as a hypothesis. This
is the body of `exists_simultaneous_multilinear_partition_bound 2`. -/
def MultilinearDiameterPartition (K : Real) (p : Nat) : Prop :=
  ∀ (N : Nat) [NeZero N] (q : Nat) (P : Box N 2), P.IsProper →
    ∀ mu : Fin q → Point N 2 → ZMod N, (∀ i, MultilinearOn P.carrier (mu i)) →
    ∀ H : Nat, 0 < H → K * ((q : Real) + 1) ≤ H →
      H ^ (p * (q + 1) ^ (2 * (2 ^ 2))) ≤ P.width →
      ∃ M : Nat, ∃ Q : Fin M → Box N 2,
        IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper) ∧
        (∀ j, (H : Real) ≤ (Q j).width) ∧
        ∀ i j, diameterAtMostReal ((Q j).carrier.image (mu i)) ((2 ^ 2 : Real) / H * N)

/-- **Freiman-linear columns are multilinear.** If `ℓ` is Freiman-linear on
`B` and every point of the box has its second coordinate in `B`, then
`x ↦ ℓ(x₁)·x₀` agrees on the box with a multilinear map. -/
theorem freiman_column_multilinearOn {N : Nat} [NeZero N] [Fact N.Prime]
    {B : Finset (ZMod N)} {ℓ : ZMod N → ZMod N} (hℓ : IsFreimanLinearOn B ℓ)
    (C : Box N 2) (hC : ∀ x ∈ C.carrier, x 1 ∈ B) :
    MultilinearOn C.carrier (fun x => ℓ (x 1) * x 0) := by
  set y₁ := (C.axis 1).start
  set c := C.commonDiff
  set L₂ := (C.axis 1).length
  by_cases hne : C.carrier.Nonempty
  swap
  · refine ⟨fun x : Point N 2 => 0 + 0 * x 0 + 0 * x 1 + 0 * (x 0 * x 1),
      isMultilinear_two _ _ _ _, fun x hx => absurd ⟨x, hx⟩ hne⟩
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨⟨i₀, hi₀, _⟩, _⟩ := (mem_box_two C x₀).mp hx₀
  -- every column point lies in `B`
  have hcol : ∀ j, j < L₂ → y₁ + (j : ZMod N) * c ∈ B := by
    intro j hj
    have hpt := hC ![(C.axis 0).start + (i₀ : ZMod N) * C.commonDiff, y₁ + (j : ZMod N) * c]
      ((mem_box_two C _).mpr ⟨⟨i₀, hi₀, rfl⟩, ⟨j, hj, rfl⟩⟩)
    simpa using hpt
  set f : Nat → ZMod N := fun j => ℓ (y₁ + (j : ZMod N) * c)
  have haff := affine_of_second_difference f L₂ (by
    intro j hj
    have hq := hℓ (y₁ + ((j + 2 : Nat) : ZMod N) * c) (y₁ + (j : ZMod N) * c)
      (y₁ + ((j + 1 : Nat) : ZMod N) * c) (y₁ + ((j + 1 : Nat) : ZMod N) * c)
      (hcol _ (by omega)) (hcol _ (by omega)) (hcol _ (by omega)) (hcol _ (by omega))
      (by push_cast; ring)
    show f (j + 2) - f (j + 1) = f (j + 1) - f j
    have hq' : f (j + 2) + f j = f (j + 1) + f (j + 1) := hq
    linear_combination hq')
  by_cases hc : c = 0
  · refine ⟨fun x : Point N 2 => 0 + ℓ y₁ * x 0 + 0 * x 1 + 0 * (x 0 * x 1),
      isMultilinear_two _ _ _ _, fun x hx => ?_⟩
    obtain ⟨_, ⟨j, _, hj⟩⟩ := (mem_box_two C x).mp hx
    have hc' : C.commonDiff = 0 := hc
    rw [hc', mul_zero, add_zero] at hj
    show ℓ (x 1) * x 0 = 0 + ℓ y₁ * x 0 + 0 * x 1 + 0 * (x 0 * x 1)
    rw [← hj]
    ring
  · have hci : c * c⁻¹ = 1 := mul_inv_cancel₀ hc
    refine ⟨fun x : Point N 2 => 0 + (f 0 - (f 1 - f 0) * c⁻¹ * y₁) * x 0 + 0 * x 1 +
        ((f 1 - f 0) * c⁻¹) * (x 0 * x 1), isMultilinear_two _ _ _ _, fun x hx => ?_⟩
    obtain ⟨_, ⟨j, hj, hjx⟩⟩ := (mem_box_two C x).mp hx
    have hfj := haff j hj
    have hjx' : x 1 = y₁ + (j : ZMod N) * c := hjx.symm
    show ℓ (x 1) * x 0 = 0 + (f 0 - (f 1 - f 0) * c⁻¹ * y₁) * x 0 + 0 * x 1 +
      ((f 1 - f 0) * c⁻¹) * (x 0 * x 1)
    rw [hjx']
    change f j * x 0 = _
    rw [hfj, nsmul_eq_mul]
    linear_combination (-(f 1 - f 0) * (j : ZMod N) * x 0) * hci

/-- The `|Γ| + |Ψ|` linear maps `x ↦ γ x₀` and `x ↦ ψ x₁`. -/
def linearForms {N : Nat} (Γ Ψ : Finset (ZMod N)) : Fin (Γ.card + Ψ.card) → Point N 2 → ZMod N :=
  Fin.addCases (fun a x => (Γ.equivFin.symm a : ZMod N) * x 0)
    (fun b x => (Ψ.equivFin.symm b : ZMod N) * x 1)

theorem linearForms_multilinearOn {N : Nat} (Γ Ψ : Finset (ZMod N)) (A : Finset (Point N 2))
    (i : Fin (Γ.card + Ψ.card)) : MultilinearOn A (linearForms Γ Ψ i) := by
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · refine ⟨fun x : Point N 2 => 0 + (Γ.equivFin.symm a : ZMod N) * x 0 + 0 * x 1 + 0 * (x 0 * x 1),
      isMultilinear_two _ _ _ _, fun x _ => ?_⟩
    simp only [linearForms, Fin.addCases_left]
    ring
  · refine ⟨fun x : Point N 2 => 0 + 0 * x 0 + (Ψ.equivFin.symm b : ZMod N) * x 1 + 0 * (x 0 * x 1),
      isMultilinear_two _ _ _ _, fun x _ => ?_⟩
    simp only [linearForms, Fin.addCases_right]
    ring

theorem linearForms_left {N : Nat} {Γ : Finset (ZMod N)} (Ψ : Finset (ZMod N)) {γ : ZMod N}
    (hγ : γ ∈ Γ) (x : Point N 2) :
    linearForms Γ Ψ (Fin.castAdd Ψ.card (Γ.equivFin ⟨γ, hγ⟩)) x = γ * x 0 := by
  simp [linearForms]

theorem linearForms_right {N : Nat} (Γ : Finset (ZMod N)) {Ψ : Finset (ZMod N)} {ψ : ZMod N}
    (hψ : ψ ∈ Ψ) (x : Point N 2) :
    linearForms Γ Ψ (Fin.natAdd Γ.card (Ψ.equivFin ⟨ψ, hψ⟩)) x = ψ * x 1 := by
  simp [linearForms]

/-- A box partitions itself. -/
theorem isBoxPartition_self {N k : Nat} [NeZero N] (C : Box N k) :
    IsBoxPartition (fun _ : Fin 1 => C) C := by
  refine ⟨fun x => ⟨fun hx => ⟨0, hx⟩, fun ⟨_, hx⟩ => hx⟩, fun i j hij => ?_⟩
  exact absurd (Subsingleton.elim i j) (bne_iff_ne.mp hij)

/-- Diameter bounds give centered-difference bounds. -/
theorem image_diam_sub_le {N : Nat} [NeZero N] {A : Finset (Point N 2)} {g : Point N 2 → ZMod N}
    {s : Real} (h : diameterAtMostReal (A.image g) s) {x y : Point N 2} (hx : x ∈ A) (hy : y ∈ A) :
    (centeredAbs (g y - g x) : Real) ≤ s :=
  h.centeredAbs_sub_le (Finset.mem_image_of_mem g hy) (Finset.mem_image_of_mem g hx)

/-- **The bilinear stage on one cell.** Let `C` be a proper cell on which
every `γ x₀` and `ψ x₁` has diameter at most `ρN/4`, and assume `C` is wide
enough for the second application. Then `C` has a partition into proper
cells of width at least `H₂`, each missing `V(ρ/2)` or oscillating by at
most `ρN/2`. -/
theorem oscillation_cell_refine {N : Nat} [NeZero N] [Fact N.Prime]
    {Γ Ψ : Finset (ZMod N)} {r : Nat} {L : Fin r → ZMod N → ZMod N} {ρ : Real}
    (hL : ∀ k, IsFreimanLinearOn (bohr Ψ ρ) (L k)) {K : Real} {p : Nat}
    (hMD : MultilinearDiameterPartition K p) (C : Box N 2) (hC : C.IsProper)
    (hγ : ∀ γ ∈ Γ, ∀ x ∈ C.carrier, ∀ y ∈ C.carrier,
      (centeredAbs (γ * y 0 - γ * x 0) : Real) ≤ ρ / 4 * N)
    (hψ : ∀ ψ ∈ Ψ, ∀ x ∈ C.carrier, ∀ y ∈ C.carrier,
      (centeredAbs (ψ * y 1 - ψ * x 1) : Real) ≤ ρ / 4 * N)
    (H₂ : Nat) (hH₂ : 0 < H₂) (hK₂ : K * ((r : Real) + 1) ≤ H₂) (hρ₂ : 8 ≤ ρ * H₂)
    (hwide : H₂ ^ (p * (r + 1) ^ (2 * (2 ^ 2))) ≤ C.width) (hH₂C : (H₂ : Real) ≤ C.width) :
    ∃ m : Nat, ∃ R : Fin m → Box N 2,
      IsBoxPartition R C ∧ (∀ j, (R j).IsProper) ∧ (∀ j, (H₂ : Real) ≤ (R j).width) ∧
      ∀ j, (∀ x ∈ (R j).carrier, (x 0, x 1) ∉ bilinearBohrVariety Γ Ψ L (ρ / 2)) ∨
        SmallOscillation Γ Ψ L (ρ / 2) (cellPairs (R j)) := by
  have hNR : (0 : Real) ≤ N := Nat.cast_nonneg N
  by_cases hmeet : ∃ x ∈ C.carrier, (x 0, x 1) ∈ bilinearBohrVariety Γ Ψ L (ρ / 2)
  swap
  · simp only [not_exists, not_and] at hmeet
    exact ⟨1, fun _ => C, isBoxPartition_self C, fun _ => hC, fun _ => hH₂C,
      fun _ => Or.inl hmeet⟩
  obtain ⟨x₀, hx₀C, hx₀V⟩ := hmeet
  obtain ⟨_, hΨx₀, _⟩ := (mem_bilinearBohrVariety_iff Γ Ψ L _ _).mp hx₀V
  -- the whole `y`-range lies in `B(Ψ;ρ)`
  have hyB : ∀ x ∈ C.carrier, x 1 ∈ bohr Ψ ρ := by
    intro x hx
    unfold bohr
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun ψ hψ' => ?_⟩
    have h := centeredAbs_le_of_close (hΨx₀ ψ hψ') (hψ ψ hψ' x₀ hx₀C x hx)
    have : ρ / 2 * N + ρ / 4 * N ≤ ρ * N := by
      have hρ : 0 ≤ ρ := by
        have : (0 : Real) < H₂ := by exact_mod_cast hH₂
        nlinarith
      nlinarith
    exact h.trans this
  -- the bilinear stage
  obtain ⟨m, R, hRpart, hRprop, hRwid, hRdiam⟩ :=
    hMD N r C hC (fun k x => L k (x 1) * x 0)
      (fun k => freiman_column_multilinearOn (hL k) C hyB) H₂ hH₂ hK₂ hwide
  refine ⟨m, R, hRpart, hRprop, hRwid, fun j => Or.inr ?_⟩
  have hsub : ∀ x ∈ (R j).carrier, x ∈ C.carrier := fun x hx => IsPartition.cell_subset hRpart j hx
  have hsmall : (2 ^ 2 : Real) / H₂ * N ≤ ρ / 2 * N := by
    apply mul_le_mul_of_nonneg_right _ hNR
    have : (0 : Real) < H₂ := by exact_mod_cast hH₂
    rw [div_le_iff₀ this]
    nlinarith
  intro p hp q hq
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hq
  have hρ4 : ρ / 4 * N ≤ ρ / 2 * N := by
    have hρ : 0 ≤ ρ := by
      have : (0 : Real) < H₂ := by exact_mod_cast hH₂
      nlinarith
    nlinarith
  refine ⟨fun γ hγ' => (hγ γ hγ' x (hsub x hx) y (hsub y hy)).trans hρ4,
    fun ψ hψ' => (hψ ψ hψ' x (hsub x hx) y (hsub y hy)).trans hρ4, fun k => ?_⟩
  exact (image_diam_sub_le (g := fun x => L k (x 1) * x 0) (hRdiam k j) hx hy).trans hsmall

/-- **Oscillation partitions at explicit scales.** -/
theorem oscillation_partition_of_scales {N : Nat} [NeZero N] [Fact N.Prime]
    {Γ Ψ : Finset (ZMod N)} {r : Nat} {L : Fin r → ZMod N → ZMod N} {ρ : Real}
    (hL : ∀ k, IsFreimanLinearOn (bohr Ψ ρ) (L k)) {K : Real} {p : Nat}
    (hMD : MultilinearDiameterPartition K p) (P : Box N 2) (hP : P.IsProper)
    (H₁ H₂ : Nat) (hH₂ : 0 < H₂) (hK₂ : K * ((r : Real) + 1) ≤ H₂) (hρ₂ : 8 ≤ ρ * H₂)
    (hK₁ : K * (((Γ.card + Ψ.card : Nat) : Real) + 1) ≤ H₁) (hρ₁ : 16 ≤ ρ * H₁)
    (h₂₁ : H₂ ^ (p * (r + 1) ^ (2 * (2 ^ 2))) ≤ H₁) (hH₂₁ : H₂ ≤ H₁)
    (hwide : H₁ ^ (p * (Γ.card + Ψ.card + 1) ^ (2 * (2 ^ 2))) ≤ P.width) :
    ∃ M : Nat, ∃ Q : Fin M → Box N 2,
      IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper) ∧ (∀ j, (H₂ : Real) ≤ (Q j).width) ∧
      ∀ j, (∀ x ∈ (Q j).carrier, (x 0, x 1) ∉ bilinearBohrVariety Γ Ψ L (ρ / 2)) ∨
        SmallOscillation Γ Ψ L (ρ / 2) (cellPairs (Q j)) := by
  have hNR : (0 : Real) ≤ N := Nat.cast_nonneg N
  have hH₁ : 0 < H₁ := lt_of_lt_of_le hH₂ hH₂₁
  have hH₁R : (0 : Real) < H₁ := by exact_mod_cast hH₁
  obtain ⟨M, Q, hQpart, hQprop, hQwid, hQdiam⟩ :=
    hMD N (Γ.card + Ψ.card) P hP (linearForms Γ Ψ) (fun i => linearForms_multilinearOn Γ Ψ _ i)
      H₁ hH₁ hK₁ hwide
  have hsmall₁ : (2 ^ 2 : Real) / H₁ * N ≤ ρ / 4 * N := by
    apply mul_le_mul_of_nonneg_right _ hNR
    rw [div_le_iff₀ hH₁R]
    nlinarith
  have hcell : ∀ j, ∃ m : Nat, ∃ R : Fin m → Box N 2,
      IsBoxPartition R (Q j) ∧ (∀ i, (R i).IsProper) ∧ (∀ i, (H₂ : Real) ≤ (R i).width) ∧
      ∀ i, (∀ x ∈ (R i).carrier, (x 0, x 1) ∉ bilinearBohrVariety Γ Ψ L (ρ / 2)) ∨
        SmallOscillation Γ Ψ L (ρ / 2) (cellPairs (R i)) := by
    intro j
    have hwj : H₂ ^ (p * (r + 1) ^ (2 * (2 ^ 2))) ≤ (Q j).width := by
      have h1 : ((H₂ ^ (p * (r + 1) ^ (2 * (2 ^ 2))) : Nat) : Real) ≤ (H₁ : Real) := by
        exact_mod_cast h₂₁
      exact_mod_cast h1.trans (hQwid j)
    have hH₂j : (H₂ : Real) ≤ (Q j).width :=
      (by exact_mod_cast hH₂₁ : (H₂ : Real) ≤ H₁).trans (hQwid j)
    apply oscillation_cell_refine hL hMD (Q j) (hQprop j) _ _ H₂ hH₂ hK₂ hρ₂ hwj hH₂j
    · intro γ hγ x hx y hy
      have h := image_diam_sub_le (hQdiam (Fin.castAdd Ψ.card (Γ.equivFin ⟨γ, hγ⟩)) j) hx hy
      rw [linearForms_left Ψ hγ, linearForms_left Ψ hγ] at h
      exact h.trans hsmall₁
    · intro ψ hψ x hx y hy
      have h := image_diam_sub_le (hQdiam (Fin.natAdd Γ.card (Ψ.equivFin ⟨ψ, hψ⟩)) j) hx hy
      rw [linearForms_right Γ hψ, linearForms_right Γ hψ] at h
      exact h.trans hsmall₁
  choose m R hRpart hRprop hRwid hRgood using hcell
  refine ⟨∑ j, m j, boxFlatten m R, boxFlatten_partition P Q m R hQpart hRpart,
    fun i => ?_, fun i => ?_, fun i => ?_⟩
  · exact hRprop _ _
  · exact hRwid _ _
  · exact hRgood _ _

end LeanProofs.GowersSzemeredi
