import GowersSzemeredi.Proofs16VarietyBoxes

/-! Product boxes around deep points of a bilinear Bohr variety.

Let `(x₀, y₀)` be a deep point of `V = bilinearBohrVariety Γ Ψ L ρ`: all
of `γ x₀`, `ψ y₀` are at most `ρN/2` and every `L k y₀ · x₀` is at most
`ρN/4`. If every `L k` is Freiman-linear on `B(Ψ;ρ)`, then `V` contains a
box `{x₀ + i d} × {y₀ + j e}`. Three nested simultaneous-Dirichlet choices
produce it.

1. `e₁` over `Ψ`, fine enough that `{j' e₁ : j' ≤ T L₂}` stays in
   `B(Ψ;ρ/2)`. Then each `L k` is affine along it:
   `L k (t e₁) − L k 0 = t δ_k`.
2. `t ≤ T` over `{δ_k x₀}`, and `e = t e₁`. The quadruple
   `(y₀ + e) + 0 = y₀ + e` gives `L(y₀ + j e) = L(y₀) + j (L(e) − L(0))`, so
   the cross term is `j t δ_k x₀`.
3. `d` over `Γ ∪ {L k y₀} ∪ {t δ_k}`.

This answers the off-origin question of research notes J.2 for single
boxes. Partitioning an arbitrary box into such cells is the remaining
composition with the peer's Lemma 16.1. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical

/-- `|j x| ≤ j |x|` in reals, with an upper bound for `j` and for `|x|`. -/
theorem centeredAbs_natCast_mul_le_of {N : Nat} (j : Nat) (x : ZMod N) {J X : Real}
    (hj : (j : Real) ≤ J) (hx : (centeredAbs x : Real) ≤ X) :
    (centeredAbs ((j : ZMod N) * x) : Real) ≤ J * X := by
  have h := centeredAbs_natCast_mul_le (N := N) j x
  have h' : (centeredAbs ((j : ZMod N) * x) : Real) ≤ (j : Real) * centeredAbs x := by
    exact_mod_cast h
  have hX0 : (0 : Real) ≤ centeredAbs x := Nat.cast_nonneg _
  calc _ ≤ (j : Real) * centeredAbs x := h'
    _ ≤ J * X := mul_le_mul hj hx hX0 ((Nat.cast_nonneg j).trans hj)

/-- From `c * M < N` to `c ≤ N / M` in reals. -/
theorem natCast_le_div_of_mul_lt {N M c : Nat} (hM : 0 < M) (h : c * M < N) :
    (c : Real) ≤ (N : Real) / M := by
  have hMR : (0 : Real) < M := by exact_mod_cast hM
  rw [le_div_iff₀ hMR]
  exact_mod_cast h.le

/-- **A product box around a deep point of a bilinear Bohr variety.** -/
theorem bilinearBohrVariety_contains_box_at {N : Nat} [NeZero N]
    {Γ Ψ : Finset (ZMod N)} {r : Nat} {L : Fin r → ZMod N → ZMod N} {ρ : Real} (hρ : 0 < ρ)
    (hL : ∀ k, IsFreimanLinearOn (bohr Ψ ρ) (L k))
    (x₀ y₀ : ZMod N)
    (hx₀ : ∀ γ ∈ Γ, (centeredAbs (γ * x₀) : Real) ≤ ρ * N / 2)
    (hy₀ : ∀ ψ ∈ Ψ, (centeredAbs (ψ * y₀) : Real) ≤ ρ * N / 2)
    (hxy : ∀ k, (centeredAbs (L k y₀ * x₀) : Real) ≤ ρ * N / 4)
    (Mt Me Md : Nat) [NeZero Mt] [NeZero Me] [NeZero Md] (L₁ L₂ : Nat)
    (ht : (L₂ : Real) ≤ ρ * Mt / 4)
    (he : ((Mt ^ r : Nat) : Real) * (L₂ + 1) ≤ ρ * Me / 2)
    (hd : (L₁ : Real) * (1 + L₂) ≤ ρ * Md / 4) :
    ∃ d e : ZMod N, ∀ i j, i < L₁ → j < L₂ →
      (x₀ + (i : ZMod N) * d, y₀ + (j : ZMod N) * e) ∈ bilinearBohrVariety Γ Ψ L ρ := by
  have hNR : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hMt : (0 : Real) < Mt := by exact_mod_cast NeZero.pos Mt
  have hMe : (0 : Real) < Me := by exact_mod_cast NeZero.pos Me
  have hMd : (0 : Real) < Md := by exact_mod_cast NeZero.pos Md
  set T : Nat := Mt ^ r with hT
  -- Step 1: `e₁`
  obtain ⟨u₁, hu₁, _, hu₁small⟩ := simultaneous_small_multiplier_fintype (N := N) (M := Me)
    (fun ψ : Ψ => ψ.1)
  set e₁ : ZMod N := (u₁ : ZMod N) with he₁def
  have hψe₁ : ∀ ψ ∈ Ψ, (centeredAbs (ψ * e₁) : Real) ≤ N / Me := by
    intro ψ hψ
    have h := natCast_le_div_of_mul_lt (NeZero.pos Me) (hu₁small ⟨ψ, hψ⟩)
    simpa [he₁def, mul_comm] using h
  -- multiples of `e₁` up to `T (L₂ + 1)` stay in `B(Ψ; ρ/2)`
  have hmult : ∀ s : Nat, s ≤ T * (L₂ + 1) → ∀ ψ ∈ Ψ,
      (centeredAbs (ψ * ((s : ZMod N) * e₁)) : Real) ≤ ρ * N / 2 := by
    intro s hs ψ hψ
    have hsR : (s : Real) ≤ (T : Real) * (L₂ + 1) := by exact_mod_cast hs
    have hrw : ψ * ((s : ZMod N) * e₁) = (s : ZMod N) * (ψ * e₁) := by ring
    rw [hrw]
    calc (centeredAbs ((s : ZMod N) * (ψ * e₁)) : Real) ≤ ((T : Real) * (L₂ + 1)) * (N / Me) :=
          centeredAbs_natCast_mul_le_of s _ hsR (hψe₁ ψ hψ)
      _ = (T : Real) * (L₂ + 1) * N / Me := by ring
      _ ≤ ρ * N / 2 := by
          rw [div_le_iff₀ hMe]
          have := mul_le_mul_of_nonneg_right he hNR.le
          nlinarith
  have hmemΨ : ∀ s : Nat, s ≤ T * (L₂ + 1) → (s : ZMod N) * e₁ ∈ bohr Ψ ρ := by
    intro s hs
    unfold bohr
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun ψ hψ => ?_⟩
    have := hmult s hs ψ hψ
    nlinarith
  -- each `L k` is affine along multiples of `e₁`
  have haff₁ : ∀ k s, s ≤ T * (L₂ + 1) →
      L k ((s : ZMod N) * e₁) = L k 0 + (s : ZMod N) * (L k e₁ - L k 0) := by
    intro k s hs
    have h := affine_of_second_difference (fun s => L k ((s : ZMod N) * e₁)) (T * (L₂ + 1) + 1)
      (fun s hs2 => by
        have hq := hL k (((s + 2 : Nat) : ZMod N) * e₁) ((s : ZMod N) * e₁)
          (((s + 1 : Nat) : ZMod N) * e₁) (((s + 1 : Nat) : ZMod N) * e₁)
          (hmemΨ _ (by omega)) (hmemΨ _ (by omega)) (hmemΨ _ (by omega)) (hmemΨ _ (by omega))
          (by push_cast; ring)
        show L k (((s + 2 : Nat) : ZMod N) * e₁) - L k (((s + 1 : Nat) : ZMod N) * e₁) =
          L k (((s + 1 : Nat) : ZMod N) * e₁) - L k ((s : ZMod N) * e₁)
        linear_combination hq) s (by omega)
    simpa [nsmul_eq_mul] using h
  -- Step 2: `t`
  set δ : Fin r → ZMod N := fun k => L k e₁ - L k 0 with hδdef
  obtain ⟨t, ht0, htT, htsmall⟩ := simultaneous_small_multiplier (N := N) (M := Mt) (K := r)
    (fun k => δ k * x₀)
  set e : ZMod N := (t : ZMod N) * e₁ with hedef
  have htδ : ∀ k, (centeredAbs ((t : ZMod N) * (δ k * x₀)) : Real) ≤ N / Mt :=
    fun k => natCast_le_div_of_mul_lt (NeZero.pos Mt) (htsmall k)
  -- the column points stay in `B(Ψ; ρ)`
  have hcol : ∀ j, j ≤ L₂ → y₀ + (j : ZMod N) * e ∈ bohr Ψ ρ := by
    intro j hj
    unfold bohr
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun ψ hψ => ?_⟩
    have hjt : j * t ≤ T * (L₂ + 1) := by
      calc j * t ≤ (L₂ + 1) * T := Nat.mul_le_mul (by omega) htT
        _ = T * (L₂ + 1) := Nat.mul_comm _ _
    have hrw : ψ * (y₀ + (j : ZMod N) * e) = ψ * y₀ + ψ * (((j * t : Nat) : ZMod N) * e₁) := by
      rw [hedef]; push_cast; ring
    rw [hrw]
    have h1 := centeredAbs_add_le (ψ * y₀) (ψ * (((j * t : Nat) : ZMod N) * e₁))
    have h1R : (centeredAbs (ψ * y₀ + ψ * (((j * t : Nat) : ZMod N) * e₁)) : Real) ≤
        centeredAbs (ψ * y₀) + centeredAbs (ψ * (((j * t : Nat) : ZMod N) * e₁)) := by
      exact_mod_cast h1
    have h2 := hy₀ ψ hψ
    have h3 := hmult (j * t) hjt ψ hψ
    linarith
  have hzero : (0 : ZMod N) ∈ bohr Ψ ρ := by
    simpa using hmemΨ 0 (Nat.zero_le _)
  -- `L k` along the column through `y₀`
  have hLcol : ∀ k j, j < L₂ →
      L k (y₀ + (j : ZMod N) * e) = L k y₀ + (j : ZMod N) * ((t : ZMod N) * δ k) := by
    intro k j hj
    have h := affine_of_second_difference (fun j => L k (y₀ + (j : ZMod N) * e)) (L₂ + 1)
      (fun s hs => by
        have hq := hL k (y₀ + ((s + 2 : Nat) : ZMod N) * e) (y₀ + (s : ZMod N) * e)
          (y₀ + ((s + 1 : Nat) : ZMod N) * e) (y₀ + ((s + 1 : Nat) : ZMod N) * e)
          (hcol _ (by omega)) (hcol _ (by omega)) (hcol _ (by omega)) (hcol _ (by omega))
          (by push_cast; ring)
        show L k (y₀ + ((s + 2 : Nat) : ZMod N) * e) - L k (y₀ + ((s + 1 : Nat) : ZMod N) * e) =
          L k (y₀ + ((s + 1 : Nat) : ZMod N) * e) - L k (y₀ + (s : ZMod N) * e)
        linear_combination hq) j (by omega)
    simp only [nsmul_eq_mul] at h
    -- the first difference is `L k e - L k 0 = t δ_k`
    have hdiff : L k (y₀ + (1 : Nat) * e) - L k (y₀ + (0 : Nat) * e) = (t : ZMod N) * δ k := by
      have hq := hL k (y₀ + e) 0 y₀ e
        (by simpa using hcol 1 (by omega)) hzero (by simpa using hcol 0 (by omega))
        (by simpa [hedef] using hmemΨ t (by
          calc t ≤ T := htT
            _ ≤ T * (L₂ + 1) := Nat.le_mul_of_pos_right T (by omega)))
        (by ring)
      have hte : L k e = L k 0 + (t : ZMod N) * (L k e₁ - L k 0) := by
        rw [hedef]; exact haff₁ k t (by
          calc t ≤ T := htT
            _ ≤ T * (L₂ + 1) := Nat.le_mul_of_pos_right T (by omega))
      push_cast
      simp only [one_mul, zero_mul, add_zero]
      rw [hδdef]
      linear_combination hq + hte
    push_cast at h hdiff
    rw [h, hdiff]
    push_cast
    ring
  -- Step 3: `d`
  let fam : (Γ ⊕ (Fin r ⊕ Fin r)) → ZMod N := fun s =>
    match s with
    | Sum.inl γ => γ.1
    | Sum.inr (Sum.inl k) => L k y₀
    | Sum.inr (Sum.inr k) => (t : ZMod N) * δ k
  obtain ⟨u, _, _, husmall⟩ := simultaneous_small_multiplier_fintype (N := N) (M := Md) fam
  refine ⟨(u : ZMod N), e, fun i j hi hj => ?_⟩
  have hiR : (i : Real) ≤ L₁ := by exact_mod_cast hi.le
  have hjR : (j : Real) ≤ L₂ := by exact_mod_cast hj.le
  have hsm : ∀ s, (centeredAbs ((u : ZMod N) * fam s) : Real) ≤ N / Md :=
    fun s => natCast_le_div_of_mul_lt (NeZero.pos Md) (husmall s)
  have hNMd : (0 : Real) ≤ N / Md := by positivity
  -- the row point is in `B(Γ; ρ)`
  have hrow : x₀ + (i : ZMod N) * (u : ZMod N) ∈ bohr Γ ρ := by
    unfold bohr
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun γ hγ => ?_⟩
    have hrw : γ * (x₀ + (i : ZMod N) * (u : ZMod N)) =
        γ * x₀ + (i : ZMod N) * ((u : ZMod N) * γ) := by ring
    rw [hrw]
    have h1 : (centeredAbs (γ * x₀ + (i : ZMod N) * ((u : ZMod N) * γ)) : Real) ≤
        centeredAbs (γ * x₀) + centeredAbs ((i : ZMod N) * ((u : ZMod N) * γ)) := by
      exact_mod_cast centeredAbs_add_le _ _
    have h2 := centeredAbs_natCast_mul_le_of i ((u : ZMod N) * γ) hiR (hsm (Sum.inl ⟨γ, hγ⟩))
    have h3 : (L₁ : Real) * (N / Md) ≤ ρ * N / 4 := by
      have : (L₁ : Real) ≤ L₁ * (1 + L₂) := by
        nlinarith [(Nat.cast_nonneg L₁ : (0 : Real) ≤ L₁), (Nat.cast_nonneg L₂ : (0 : Real) ≤ L₂)]
      have h4 : (L₁ : Real) * (N / Md) = L₁ * N / Md := by ring
      rw [h4, div_le_iff₀ hMd]; nlinarith
    linarith [hx₀ γ hγ]
  apply product_mem_bilinearBohrVariety hrow (hcol j hj.le)
  intro k
  rw [hLcol k j hj]
  have hrw : (L k y₀ + (j : ZMod N) * ((t : ZMod N) * δ k)) * (x₀ + (i : ZMod N) * (u : ZMod N)) =
      L k y₀ * x₀ + (i : ZMod N) * ((u : ZMod N) * L k y₀) +
        (j : ZMod N) * ((t : ZMod N) * (δ k * x₀)) +
        ((i * j : Nat) : ZMod N) * ((u : ZMod N) * ((t : ZMod N) * δ k)) := by push_cast; ring
  rw [hrw]
  have hA := hxy k
  have hB := centeredAbs_natCast_mul_le_of i ((u : ZMod N) * L k y₀) hiR (hsm (Sum.inr (Sum.inl k)))
  have hC := centeredAbs_natCast_mul_le_of j ((t : ZMod N) * (δ k * x₀)) hjR (htδ k)
  have hD := centeredAbs_natCast_mul_le_of (i * j) ((u : ZMod N) * ((t : ZMod N) * δ k))
    (by push_cast; exact mul_le_mul hiR hjR (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (hsm (Sum.inr (Sum.inr k)))
  have htri : ∀ a b c d : ZMod N, (centeredAbs (a + b + c + d) : Real) ≤
      centeredAbs a + centeredAbs b + centeredAbs c + centeredAbs d := by
    intro a b c d
    have h1 := centeredAbs_add_le (a + b + c) d
    have h2 := centeredAbs_add_le (a + b) c
    have h3 := centeredAbs_add_le a b
    have : centeredAbs (a + b + c + d) ≤ centeredAbs a + centeredAbs b + centeredAbs c + centeredAbs d := by
      omega
    exact_mod_cast this
  have hsum := htri (L k y₀ * x₀) ((i : ZMod N) * ((u : ZMod N) * L k y₀))
    ((j : ZMod N) * ((t : ZMod N) * (δ k * x₀)))
    (((i * j : Nat) : ZMod N) * ((u : ZMod N) * ((t : ZMod N) * δ k)))
  have hCt : (L₂ : Real) * (N / Mt) ≤ ρ * N / 4 := by
    have h4 : (L₂ : Real) * (N / Mt) = L₂ * N / Mt := by ring
    rw [h4, div_le_iff₀ hMt]; nlinarith
  have hBD : (L₁ : Real) * (N / Md) + ((L₁ : Real) * L₂) * (N / Md) ≤ ρ * N / 4 := by
    have h4 : (L₁ : Real) * (N / Md) + ((L₁ : Real) * L₂) * (N / Md) = L₁ * (1 + L₂) * N / Md := by
      ring
    rw [h4, div_le_iff₀ hMd]; nlinarith
  linarith

end LeanProofs.GowersSzemeredi
