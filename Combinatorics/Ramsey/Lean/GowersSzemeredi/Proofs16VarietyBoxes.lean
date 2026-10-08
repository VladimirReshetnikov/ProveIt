import GowersSzemeredi.Proofs16BilinearBohrVariety
import GowersSzemeredi.Proofs05SimultaneousDirichlet

/-! Bilinear Bohr varieties contain product progressions through the origin.

Let `V = bilinearBohrVariety Γ Ψ L ρ` with every `L k` Freiman-linear on
`B(Ψ;ρ)`. Then `V` contains `{i·d : i < L₁} × {j·e : j < L₂}` for steps
`d = u`, `e = v` with `1 ≤ u ≤ M₁^(|Γ|+2r)` and `1 ≤ v ≤ M₂^|Ψ|`, provided
`L₂ ≤ ρ M₂` and `L₁ (1 + L₂) ≤ ρ M₁`.

1. Choose `v` by simultaneous Dirichlet over `Ψ`, so every `j·e` stays in
   `B(Ψ;ρ)`.
2. Each `L k` is then affine along `{j·e}`: Freiman-linearity kills its
   second differences.
3. Choose `u` by simultaneous Dirichlet over
   `Γ ∪ {L k 0} ∪ {L k e − L k 0}`. Then `i·d ∈ B(Γ;ρ)`, and every
   `L k (j·e) · i·d` is small.

The exponents `|Ψ|` and `|Γ| + 2r` are linear in the codimension and rank.
With `M^K < N` the steps are nonzero residues, so the progressions are
non-degenerate. Composed with `freiman_bihom_biaffine_on_product`, any
Freiman bihomomorphism on `V` is bi-affine on this box: the readout (R) at
the origin, research notes J.2. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical

/-- Simultaneous Dirichlet over any finite index type. -/
theorem simultaneous_small_multiplier_fintype {N M : Nat} [NeZero N] [NeZero M]
    {ι : Type*} [Fintype ι] (a : ι → ZMod N) :
    ∃ u : Nat, 0 < u ∧ u ≤ M ^ Fintype.card ι ∧
      ∀ i, centeredAbs ((u : ZMod N) * a i) * M < N := by
  obtain ⟨u, hu, huM, h⟩ := simultaneous_small_multiplier (N := N) (M := M)
    (fun t : Fin (Fintype.card ι) => a ((Fintype.equivFin ι).symm t))
  refine ⟨u, hu, huM, fun i => ?_⟩
  simpa using h (Fintype.equivFin ι i)

/-- The centered absolute value is subadditive. -/
theorem centeredAbs_add_le {N : Nat} (x y : ZMod N) :
    centeredAbs (x + y) ≤ centeredAbs x + centeredAbs y := by
  unfold centeredAbs
  exact (ZMod.natAbs_valMinAbs_add_le x y).trans (Int.natAbs_add_le _ _)

/-- `|j x| ≤ j |x|`. -/
theorem centeredAbs_natCast_mul_le {N : Nat} (j : Nat) (x : ZMod N) :
    centeredAbs ((j : ZMod N) * x) ≤ j * centeredAbs x := by
  induction j with
  | zero =>
    simp [centeredAbs]
  | succ j ih =>
    have h : ((j + 1 : Nat) : ZMod N) * x = (j : ZMod N) * x + x := by push_cast; ring
    rw [h]
    calc centeredAbs ((j : ZMod N) * x + x) ≤ centeredAbs ((j : ZMod N) * x) + centeredAbs x :=
          centeredAbs_add_le _ _
      _ ≤ j * centeredAbs x + centeredAbs x := Nat.add_le_add_right ih _
      _ = (j + 1) * centeredAbs x := by ring

/-- **Bilinear Bohr varieties contain product progressions through the
origin.** -/
theorem bilinearBohrVariety_contains_product {N : Nat} [NeZero N]
    {Γ Ψ : Finset (ZMod N)} {r : Nat} {L : Fin r → ZMod N → ZMod N} {ρ : Real}
    (hL : ∀ k, IsFreimanLinearOn (bohr Ψ ρ) (L k))
    (M₁ M₂ : Nat) [NeZero M₁] [NeZero M₂] (L₁ L₂ : Nat)
    (h₂ : (L₂ : Real) ≤ ρ * M₂) (h₁ : (L₁ : Real) * (1 + L₂) ≤ ρ * M₁) :
    ∃ u v : Nat, 0 < u ∧ u ≤ M₁ ^ (Γ.card + (r + r)) ∧ 0 < v ∧ v ≤ M₂ ^ Ψ.card ∧
      ∀ i j, i < L₁ → j < L₂ →
        ((i : ZMod N) * (u : ZMod N), (j : ZMod N) * (v : ZMod N)) ∈
          bilinearBohrVariety Γ Ψ L ρ := by
  have hNR : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hM₁ : (0 : Real) < M₁ := by exact_mod_cast NeZero.pos M₁
  have hM₂ : (0 : Real) < M₂ := by exact_mod_cast NeZero.pos M₂
  -- Step 1: the column step `e`
  obtain ⟨v, hv, hvM, hvsmall⟩ := simultaneous_small_multiplier_fintype (N := N) (M := M₂)
    (fun ψ : Ψ => ψ.1)
  set e : ZMod N := (v : ZMod N) with hedef
  have hsmall_of : ∀ (c : Nat) (M : Nat) (L₀ : Nat), (0 : Real) < M → c * M < N →
      ∀ j, j < L₀ → (j * c : Real) ≤ L₀ * N / M := by
    intro c M L₀ hM hc j hj
    have hcR : (c : Real) * M < N := by exact_mod_cast hc
    have hjR : (j : Real) ≤ L₀ := by exact_mod_cast hj.le
    have hc' : (c : Real) ≤ N / M := by rw [le_div_iff₀ hM]; linarith
    calc (j * c : Real) ≤ L₀ * (N / M) :=
          mul_le_mul hjR hc' (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      _ = L₀ * N / M := by ring
  have hcol : ∀ j, j < L₂ → (j : ZMod N) * e ∈ bohr Ψ ρ := by
    intro j hj
    unfold bohr
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun ψ hψ => ?_⟩
    have hrw : ψ * ((j : ZMod N) * e) = (j : ZMod N) * ((v : ZMod N) * ψ) := by rw [hedef]; ring
    rw [hrw]
    have h1 := centeredAbs_natCast_mul_le (N := N) j ((v : ZMod N) * ψ)
    have h2 := hsmall_of _ M₂ L₂ hM₂ (hvsmall ⟨ψ, hψ⟩) j hj
    have h3 : (L₂ * N / M₂ : Real) ≤ ρ * N := by
      rw [div_le_iff₀ hM₂]; nlinarith
    calc (centeredAbs ((j : ZMod N) * ((v : ZMod N) * ψ)) : Real)
        ≤ (j * centeredAbs ((v : ZMod N) * ψ) : Nat) := by exact_mod_cast h1
      _ = (j : Real) * centeredAbs ((v : ZMod N) * ψ) := by push_cast; ring
      _ ≤ _ := h2.trans h3
  -- Step 2: each `L k` is affine along the column
  have haff : ∀ k j, j < L₂ →
      L k ((j : ZMod N) * e) = L k 0 + (j : ZMod N) * (L k e - L k 0) := by
    intro k j hj
    have h := affine_of_second_difference (fun j => L k ((j : ZMod N) * e)) L₂
      (fun j hj2 => by
        have hq := hL k ((((j + 2 : Nat) : ZMod N)) * e) ((j : ZMod N) * e)
          (((j + 1 : Nat) : ZMod N) * e) (((j + 1 : Nat) : ZMod N) * e)
          (hcol _ hj2) (hcol _ (by omega)) (hcol _ (by omega)) (hcol _ (by omega))
          (by push_cast; ring)
        show L k (((j + 2 : Nat) : ZMod N) * e) - L k (((j + 1 : Nat) : ZMod N) * e) =
          L k (((j + 1 : Nat) : ZMod N) * e) - L k ((j : ZMod N) * e)
        linear_combination hq) j hj
    simpa [nsmul_eq_mul] using h
  -- Step 3: the row step `d`
  let fam : (Γ ⊕ (Fin r ⊕ Fin r)) → ZMod N := fun t =>
    match t with
    | Sum.inl γ => γ.1
    | Sum.inr (Sum.inl k) => L k 0
    | Sum.inr (Sum.inr k) => L k e - L k 0
  obtain ⟨u, hu, huM, husmall⟩ := simultaneous_small_multiplier_fintype (N := N) (M := M₁) fam
  have hcard : Fintype.card (Γ ⊕ (Fin r ⊕ Fin r)) = Γ.card + (r + r) := by simp
  refine ⟨u, v, hu, by rw [← hcard]; exact huM, hv, by simpa using hvM, ?_⟩
  intro i j hi hj
  have hL1 : (L₁ : Real) ≤ ρ * M₁ := by
    have : (L₁ : Real) ≤ L₁ * (1 + L₂) := by
      have : (0 : Real) ≤ L₁ := Nat.cast_nonneg _
      nlinarith [(Nat.cast_nonneg L₂ : (0 : Real) ≤ L₂)]
    linarith
  have hrow : (i : ZMod N) * (u : ZMod N) ∈ bohr Γ ρ := by
    unfold bohr
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun γ hγ => ?_⟩
    have hrw : γ * ((i : ZMod N) * (u : ZMod N)) = (i : ZMod N) * ((u : ZMod N) * γ) := by ring
    rw [hrw]
    have h1 := centeredAbs_natCast_mul_le (N := N) i ((u : ZMod N) * γ)
    have h2 := hsmall_of _ M₁ L₁ hM₁ (husmall (Sum.inl ⟨γ, hγ⟩)) i hi
    have h3 : (L₁ * N / M₁ : Real) ≤ ρ * N := by rw [div_le_iff₀ hM₁]; nlinarith
    calc (centeredAbs ((i : ZMod N) * ((u : ZMod N) * γ)) : Real)
        ≤ (i * centeredAbs ((u : ZMod N) * γ) : Nat) := by exact_mod_cast h1
      _ = (i : Real) * centeredAbs ((u : ZMod N) * γ) := by push_cast; ring
      _ ≤ _ := h2.trans h3
  apply product_mem_bilinearBohrVariety hrow (hcol j hj)
  intro k
  rw [haff k j hj]
  -- `(L k 0 + j Δ) · i u = i (u L k 0) + (i j)(u Δ)`
  have hrw : (L k 0 + (j : ZMod N) * (L k e - L k 0)) * ((i : ZMod N) * (u : ZMod N)) =
      (i : ZMod N) * ((u : ZMod N) * L k 0) +
        ((i * j : Nat) : ZMod N) * ((u : ZMod N) * (L k e - L k 0)) := by push_cast; ring
  rw [hrw]
  have hA := centeredAbs_natCast_mul_le (N := N) i ((u : ZMod N) * L k 0)
  have hB := centeredAbs_natCast_mul_le (N := N) (i * j) ((u : ZMod N) * (L k e - L k 0))
  have hsum := centeredAbs_add_le ((i : ZMod N) * ((u : ZMod N) * L k 0))
    (((i * j : Nat) : ZMod N) * ((u : ZMod N) * (L k e - L k 0)))
  have h0 := husmall (Sum.inr (Sum.inl k))
  have hΔ := husmall (Sum.inr (Sum.inr k))
  have h0R : (centeredAbs ((u : ZMod N) * L k 0) : Real) ≤ N / M₁ := by
    rw [le_div_iff₀ hM₁]; exact_mod_cast h0.le
  have hΔR : (centeredAbs ((u : ZMod N) * (L k e - L k 0)) : Real) ≤ N / M₁ := by
    rw [le_div_iff₀ hM₁]; exact_mod_cast hΔ.le
  have hiR : (i : Real) ≤ L₁ := by exact_mod_cast hi.le
  have hjR : (j : Real) ≤ L₂ := by exact_mod_cast hj.le
  have hNM : (0 : Real) ≤ N / M₁ := by positivity
  have hfin : (L₁ : Real) * (N / M₁) + (L₁ * L₂) * (N / M₁) ≤ ρ * N := by
    have : (L₁ : Real) * (N / M₁) + (L₁ * L₂) * (N / M₁) = L₁ * (1 + L₂) * N / M₁ := by ring
    rw [this, div_le_iff₀ hM₁]; nlinarith
  calc (centeredAbs ((i : ZMod N) * ((u : ZMod N) * L k 0) +
        ((i * j : Nat) : ZMod N) * ((u : ZMod N) * (L k e - L k 0))) : Real)
      ≤ (i * centeredAbs ((u : ZMod N) * L k 0) +
          (i * j) * centeredAbs ((u : ZMod N) * (L k e - L k 0)) : Nat) := by
        exact_mod_cast hsum.trans (Nat.add_le_add hA hB)
    _ = (i : Real) * centeredAbs ((u : ZMod N) * L k 0) +
          ((i : Real) * j) * centeredAbs ((u : ZMod N) * (L k e - L k 0)) := by push_cast; ring
    _ ≤ (L₁ : Real) * (N / M₁) + (L₁ * L₂) * (N / M₁) := by
        apply add_le_add
        · exact mul_le_mul hiR h0R (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        · exact mul_le_mul (mul_le_mul hiR hjR (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hΔR
            (Nat.cast_nonneg _) (by positivity)
    _ ≤ ρ * N := hfin

/-- **The readout at the origin.** A Freiman bihomomorphism on a bilinear
Bohr variety is bi-affine on a product progression through the origin, of
the sizes above. -/
theorem freiman_on_variety_biaffine_at_origin {N : Nat} [NeZero N]
    {Γ Ψ : Finset (ZMod N)} {r : Nat} {L : Fin r → ZMod N → ZMod N} {ρ : Real}
    {Φ : ZMod N × ZMod N → ZMod N}
    (hL : ∀ k, IsFreimanLinearOn (bohr Ψ ρ) (L k))
    (hΦ : IsEBihomomorphism (bilinearBohrVariety Γ Ψ L ρ) Φ {0})
    (M₁ M₂ : Nat) [NeZero M₁] [NeZero M₂] (L₁ L₂ : Nat) (hL₁ : 2 ≤ L₁) (hL₂ : 2 ≤ L₂)
    (h₂ : (L₂ : Real) ≤ ρ * M₂) (h₁ : (L₁ : Real) * (1 + L₂) ≤ ρ * M₁) :
    ∃ u v : Nat, 0 < u ∧ u ≤ M₁ ^ (Γ.card + (r + r)) ∧ 0 < v ∧ v ≤ M₂ ^ Ψ.card ∧
      let f : Nat → Nat → ZMod N := fun i j =>
        Φ (0 + (i : ZMod N) * (u : ZMod N), 0 + (j : ZMod N) * (v : ZMod N))
      ∀ i j, i < L₁ → j < L₂ →
        f i j = f 0 0 + i • (f 1 0 - f 0 0) + j • (f 0 1 - f 0 0) +
          (i * j) • (f 1 1 - f 1 0 - f 0 1 + f 0 0) := by
  obtain ⟨u, v, hu, huM, hv, hvM, hmem⟩ :=
    bilinearBohrVariety_contains_product hL M₁ M₂ L₁ L₂ h₂ h₁
  refine ⟨u, v, hu, huM, hv, hvM, ?_⟩
  exact freiman_bihom_biaffine_on_product hΦ 0 (u : ZMod N) 0 (v : ZMod N) L₁ L₂ hL₁ hL₂
    (fun i j hi hj => by simpa using hmem i j hi hj)

end LeanProofs.GowersSzemeredi
