import GowersSzemeredi.Proofs16ColumnRepSystem
import GowersSzemeredi.Proofs16CommonWitnesses
import GowersSzemeredi.Proofs16FreimanFewValues
import GowersSzemeredi.Proofs16VarietyRegularStep

/-! Milićević's Proposition 5.1 (iii) for one quadruple of columns, in
`ℤ/N`.

Let `φ` be a map on `A ⊆ ℤ/N × ℤ/N` that is Freiman-linear along rows. Take
an additive quadruple of columns `x₀ + x₁ = x₂ + x₃`, with column sets
`Bᵢ ⊆ A_{xᵢ}` on which `φ(xᵢ, ·)` is a Freiman 8-homomorphism. Let `ψᵢ` be
the induced maps (`repMap`). Then:
* `alternating_repMap_vanishes`: at every common witness `w ∈ ⋂ Bᵢ⁴`,
  `ψ₀ + ψ₁ − ψ₂ − ψ₃` vanishes at `w₀ + w₁ − w₂ − w₃`. Each `ψᵢ` unfolds to
  `φ(xᵢ,w₀) + φ(xᵢ,w₁) − φ(xᵢ,w₂) − φ(xᵢ,w₃)`, and the four row identities
  cancel.
* `fourSum_fibre_card_le`: a point has at most `N³` representing
  four-tuples.
* `alternating_image_bound`: let `Sᵢ` be spectra on whose Bohr sets the
  `ψᵢ` are Freiman-linear, and suppose `θN⁴` common witnesses land in
  every `B(Sᵢ; 1/(4π))`. Write `Γ = ⋃ Sᵢ`. The combination is
  Freiman-linear on `B(Γ; 1/(4π))` and vanishes on at least `θN` points
  there, so by Lemma 2.42 (`freiman_image_card_mul_le`)
  `#Im(ψ₀ + ψ₁ − ψ₂ − ψ₃ on B(Γ; 1/(8π))) · θN · |B(Γ; 1/(16π))| ≤ N²`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical

/-- The column `{y : (x, y) ∈ A}`. -/
def bihomColumn {N : Nat} [NeZero N] (A : Finset (ZMod N × ZMod N)) (x : ZMod N) :
    Finset (ZMod N) :=
  Finset.univ.filter fun y => (x, y) ∈ A

/-- The row `{x : (x, y) ∈ A}`. -/
def bihomRow {N : Nat} [NeZero N] (A : Finset (ZMod N × ZMod N)) (y : ZMod N) :
    Finset (ZMod N) :=
  Finset.univ.filter fun x => (x, y) ∈ A

/-- The alternating combination of four column maps. -/
def alternatingColumnMap {N : Nat} (B : Fin 4 → Finset (ZMod N))
    (φ : ZMod N × ZMod N → ZMod N) (x : Fin 4 → ZMod N) (d : ZMod N) : ZMod N :=
  repMap (B 0) (fun y => φ (x 0, y)) d + repMap (B 1) (fun y => φ (x 1, y)) d -
    repMap (B 2) (fun y => φ (x 2, y)) d - repMap (B 3) (fun y => φ (x 3, y)) d

/-- **The alternating combination vanishes on common witnesses.** -/
theorem alternating_repMap_vanishes {N : Nat} [NeZero N] (A : Finset (ZMod N × ZMod N))
    (φ : ZMod N × ZMod N → ZMod N)
    (hrow : ∀ y, FreimanHom 2 (bihomRow A y) (fun x => φ (x, y)))
    (x : Fin 4 → ZMod N) (hx : IsAdditiveQuadruple x) (B : Fin 4 → Finset (ZMod N))
    (hB : ∀ i, B i ⊆ bihomColumn A (x i)) (h8 : ∀ i, FreimanHom 8 (B i) (fun y => φ (x i, y)))
    (w : Fin 4 → ZMod N) (hw : ∀ i j, w j ∈ B i) :
    alternatingColumnMap B φ x (fourSum w) = 0 := by
  unfold alternatingColumnMap
  rw [repMap_spec (h8 0) (fun j => hw 0 j), repMap_spec (h8 1) (fun j => hw 1 j),
    repMap_spec (h8 2) (fun j => hw 2 j), repMap_spec (h8 3) (fun j => hw 3 j)]
  have hxA : ∀ i j, x i ∈ bihomRow A (w j) := by
    intro i j
    have := hB i (hw i j)
    simp only [bihomColumn, Finset.mem_filter, Finset.mem_univ, true_and] at this
    simp only [bihomRow, Finset.mem_filter, Finset.mem_univ, true_and]
    exact this
  have hrowj : ∀ j, φ (x 0, w j) + φ (x 1, w j) = φ (x 2, w j) + φ (x 3, w j) := by
    intro j
    have h := hrow (w j)
    rw [FreimanHom, isAddFreimanHom_two] at h
    exact h.2 (x 0) (hxA 0 j) (x 1) (hxA 1 j) (x 2) (hxA 2 j) (x 3) (hxA 3 j) hx
  unfold repFourValue
  linear_combination hrowj 0 + hrowj 1 - hrowj 2 - hrowj 3

/-- **A point has at most `N³` representing four-tuples.** -/
theorem fourSum_fibre_card_le {N : Nat} [NeZero N] (C : Finset (Fin 4 → ZMod N)) (d : ZMod N) :
    (C.filter fun q => fourSum q = d).card ≤ N ^ 3 := by
  have hinj : Set.InjOn (fun q : Fin 4 → ZMod N => (q 0, q 1, q 2))
      ((C.filter fun q => fourSum q = d : Finset _) : Set _) := by
    intro q hq r hr h
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hq hr
    simp only [Prod.mk.injEq] at h
    obtain ⟨h0, h1, h2⟩ := h
    have hq' := hq.2
    have hr' := hr.2
    simp only [fourSum] at hq' hr'
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · show q 3 = r 3
      linear_combination hr' - hq' + h0 + h1 - h2
  have h := Finset.card_le_card_of_injOn _ (fun q _ => Finset.mem_univ (q 0, q 1, q 2)) hinj
  rw [Finset.card_univ, Fintype.card_prod, Fintype.card_prod, ZMod.card] at h
  calc _ ≤ N * (N * N) := h
    _ = N ^ 3 := by ring

/-- **Proposition 5.1 (iii) for one quadruple: few values.** -/
theorem alternating_image_bound {N : Nat} [NeZero N] (A : Finset (ZMod N × ZMod N))
    (φ : ZMod N × ZMod N → ZMod N)
    (hrow : ∀ y, FreimanHom 2 (bihomRow A y) (fun x => φ (x, y)))
    (x : Fin 4 → ZMod N) (hx : IsAdditiveQuadruple x) (B : Fin 4 → Finset (ZMod N))
    (hB : ∀ i, B i ⊆ bihomColumn A (x i)) (h8 : ∀ i, FreimanHom 8 (B i) (fun y => φ (x i, y)))
    (S : Fin 4 → Finset (ZMod N))
    (hlin : ∀ i, IsFreimanLinearOn (bohr (S i) (1 / (4 * Real.pi)))
      (repMap (B i) (fun y => φ (x i, y))))
    (C : Finset (Fin 4 → ZMod N))
    (hC : ∀ w ∈ C, (∀ i j, w j ∈ B i) ∧ ∀ i, fourSum w ∈ bohr (S i) (1 / (4 * Real.pi)))
    {θ : Real} (hθ : θ * (N : Real) ^ 4 ≤ C.card) :
    (((bohr (S 0 ∪ S 1 ∪ S 2 ∪ S 3) (1 / (8 * Real.pi))).image
        (alternatingColumnMap B φ x)).card : Real) *
      (θ * N * (bohr (S 0 ∪ S 1 ∪ S 2 ∪ S 3) (1 / (16 * Real.pi))).card) ≤
        (N : Real) * N := by
  have hNR : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  set Γ := S 0 ∪ S 1 ∪ S 2 ∪ S 3 with hΓ
  set ρ : Real := 1 / (4 * Real.pi) with hρ
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  have hD : bohr Γ ρ = bohr (S 0) ρ ∩ bohr (S 1) ρ ∩ bohr (S 2) ρ ∩ bohr (S 3) ρ := by
    rw [hΓ, bohr_union, bohr_union, bohr_union]
  have hDsub : ∀ i, bohr Γ ρ ⊆ bohr (S i) ρ := by
    intro i
    rw [hD]
    fin_cases i
    · exact fun y hy => (Finset.mem_inter.mp (Finset.mem_inter.mp (Finset.mem_inter.mp hy).1).1).1
    · exact fun y hy => (Finset.mem_inter.mp (Finset.mem_inter.mp (Finset.mem_inter.mp hy).1).1).2
    · exact fun y hy => (Finset.mem_inter.mp (Finset.mem_inter.mp hy).1).2
    · exact fun y hy => (Finset.mem_inter.mp hy).2
  -- the combination is Freiman-linear on the common Bohr set
  have hcomb : IsFreimanLinearOn (bohr Γ ρ) (alternatingColumnMap B φ x) := by
    have hL : ∀ i, IsFreimanLinearOn (bohr Γ ρ) (repMap (B i) (fun y => φ (x i, y))) :=
      fun i => IsFreimanLinearOn.mono (hlin i) (hDsub i)
    have h := IsFreimanLinearOn.linear_combination (B := bohr Γ ρ)
      (L := fun i : Fin 4 => repMap (B i) (fun y => φ (x i, y))) hL ![1, 1, -1, -1]
    intro y₁ y₂ y₃ y₄ h₁ h₂ h₃ h₄ hsum
    have := h y₁ y₂ y₃ y₄ h₁ h₂ h₃ h₄ hsum
    simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.vecHead,
      Matrix.vecTail, Function.comp, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at this
    unfold alternatingColumnMap
    linear_combination this
  -- the zero set
  set Z := C.image fourSum with hZ
  have hZsub : Z ⊆ bohr Γ ρ := by
    intro d hd
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hd
    have h := (hC w hw).2
    rw [hD]
    exact Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨h 0, h 1⟩, h 2⟩, h 3⟩
  have hZzero : ∀ d ∈ Z, alternatingColumnMap B φ x d = 0 := by
    intro d hd
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hd
    exact alternating_repMap_vanishes A φ hrow x hx B hB h8 w (hC w hw).1
  have hZcard : θ * N ≤ Z.card := by
    have hfib : C.card ≤ N ^ 3 * Z.card := by
      rw [Finset.card_eq_sum_card_fiberwise (f := fourSum) (t := Z)
        (fun w hw => Finset.mem_image_of_mem _ hw)]
      calc ∑ d ∈ Z, (C.filter fun q => fourSum q = d).card ≤ ∑ _d ∈ Z, N ^ 3 :=
            Finset.sum_le_sum fun d _ => fourSum_fibre_card_le C d
        _ = N ^ 3 * Z.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    have hfibR : (C.card : Real) ≤ (N : Real) ^ 3 * Z.card := by exact_mod_cast hfib
    have h3 : (0 : Real) < (N : Real) ^ 3 := by positivity
    have : θ * N * (N : Real) ^ 3 ≤ Z.card * (N : Real) ^ 3 := by nlinarith
    exact le_of_mul_le_mul_right this h3
  have hmain := freiman_image_card_mul_le Γ hρ0 _ hcomb Z hZsub hZzero
  have hρ2 : ρ / 2 = 1 / (8 * Real.pi) := by rw [hρ]; field_simp; ring
  have hρ4 : ρ / 4 = 1 / (16 * Real.pi) := by rw [hρ]; field_simp; ring
  rw [hρ2, hρ4] at hmain
  have hDN : ((bohr Γ ρ).card : Real) ≤ N := by
    exact_mod_cast (show (bohr Γ ρ).card ≤ N by simpa using Finset.card_le_univ (bohr Γ ρ))
  have hmainR : (((bohr Γ (1 / (8 * Real.pi))).image (alternatingColumnMap B φ x)).card : Real) *
      ((Z.card : Real) * (bohr Γ (1 / (16 * Real.pi))).card) ≤ N * (bohr Γ ρ).card := by
    exact_mod_cast hmain
  have hI0 : (0 : Real) ≤ (((bohr Γ (1 / (8 * Real.pi))).image
      (alternatingColumnMap B φ x)).card : Real) := Nat.cast_nonneg _
  have hB0 : (0 : Real) ≤ (bohr Γ (1 / (16 * Real.pi))).card := Nat.cast_nonneg _
  calc _ ≤ (((bohr Γ (1 / (8 * Real.pi))).image (alternatingColumnMap B φ x)).card : Real) *
        ((Z.card : Real) * (bohr Γ (1 / (16 * Real.pi))).card) := by
        apply mul_le_mul_of_nonneg_left _ hI0
        exact mul_le_mul_of_nonneg_right hZcard hB0
    _ ≤ N * (bohr Γ ρ).card := hmainR
    _ ≤ N * N := mul_le_mul_of_nonneg_left hDN hNR.le

end LeanProofs.GowersSzemeredi
