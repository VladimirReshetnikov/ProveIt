import GowersSzemeredi.Proofs16FreimanBilinearReadout

/-! The readout in the corpus's vocabulary: `MultilinearOn` product boxes.

`freiman_bihom_biaffine_on_product` gives the index form
`A + B i + C j + D i j` on `{(a + i d, b + j e)}`. When the steps `d`, `e`
are units of `ZMod N`, substituting `i = d⁻¹(x₀ − a)` and
`j = e⁻¹(x₁ − b)` makes the map multi-affine in the coordinates. So it
agrees on the box with an `IsMultilinear` map on `Point N 2`. This is the
form in which Gowers's multiply-linear covers (`MultiplyLinear`,
`MultiplyLinearWith`) count graphs. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical

/-- Every map `c₀₀ + c₁₀ x₀ + c₀₁ x₁ + c₁₁ x₀ x₁` on `Point N 2` is
multilinear in the corpus's sense. -/
theorem isMultilinear_two {N : Nat} (c₀₀ c₁₀ c₀₁ c₁₁ : ZMod N) :
    IsMultilinear (fun x : Point N 2 => c₀₀ + c₁₀ * x 0 + c₀₁ * x 1 + c₁₁ * (x 0 * x 1)) := by
  refine ⟨fun e => if e 0 then (if e 1 then c₁₁ else c₁₀) else (if e 1 then c₀₁ else c₀₀), ?_⟩
  intro x
  rw [← (piFinTwoEquiv fun _ => Bool).symm.sum_comp, Fintype.sum_prod_type]
  simp [Fin.prod_univ_two, piFinTwoEquiv]
  ring

/-- **The readout as `MultilinearOn`.** A Freiman bihomomorphism on `V`
agrees, on every product of progressions with unit steps inside `V`, with a
multilinear map. -/
theorem freiman_bihom_multilinearOn_product {N : Nat} {V : Finset (ZMod N × ZMod N)}
    {Φ : ZMod N × ZMod N → ZMod N} (hΦ : IsEBihomomorphism V Φ {0})
    (a d b e : ZMod N) (hd : IsUnit d) (he : IsUnit e) (L₁ L₂ : Nat) (hL₁ : 2 ≤ L₁) (hL₂ : 2 ≤ L₂)
    (hsub : ∀ i j, i < L₁ → j < L₂ → (a + (i : ZMod N) * d, b + (j : ZMod N) * e) ∈ V) :
    MultilinearOn ((Finset.range L₁ ×ˢ Finset.range L₂).image fun ij =>
        (![a + (ij.1 : ZMod N) * d, b + (ij.2 : ZMod N) * e] : Point N 2))
      (fun x => Φ (x 0, x 1)) := by
  have hba := freiman_bihom_biaffine_on_product hΦ a d b e L₁ L₂ hL₁ hL₂ hsub
  set f : Nat → Nat → ZMod N := fun i j => Φ (a + (i : ZMod N) * d, b + (j : ZMod N) * e)
  set A := f 0 0
  set B := f 1 0 - f 0 0
  set C := f 0 1 - f 0 0
  set D := f 1 1 - f 1 0 - f 0 1 + f 0 0
  obtain ⟨di, hdi⟩ := hd.exists_left_inv
  obtain ⟨ei, hei⟩ := he.exists_left_inv
  -- the multi-affine expression in the coordinates
  refine ⟨fun x : Point N 2 =>
      (A - B * di * a - C * ei * b + D * di * ei * (a * b)) + (B * di - D * di * ei * b) * x 0 +
        (C * ei - D * di * ei * a) * x 1 + (D * di * ei) * (x 0 * x 1),
    isMultilinear_two _ _ _ _, ?_⟩
  intro x hx
  obtain ⟨⟨i, j⟩, hij, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨hi, hj⟩ := Finset.mem_product.mp hij
  have hi' : i < L₁ := Finset.mem_range.mp hi
  have hj' : j < L₂ := Finset.mem_range.mp hj
  have h := hba i j hi' hj'
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  change f i j = _
  rw [h]
  simp only [nsmul_eq_mul]
  push_cast
  -- use `di * d = 1`, `ei * e = 1`
  linear_combination (-(B * (i : ZMod N)) - D * (i : ZMod N) * (j : ZMod N)) * hdi +
    (-(C * (j : ZMod N)) - D * (i : ZMod N) * (j : ZMod N) * (di * d)) * hei

end LeanProofs.GowersSzemeredi
