import GowersSzemeredi.Proofs16BihomPieceReduction

/-! The single extraction step `DenseBihomPiece`, from a line-wise Freiman input.

This follows Milićević's §15 (arXiv:2601.01682, proof of Theorem 15.1).
1. **Selection.** Choose one value of the relation over each projected point.
   The selection `φ` is a partial function inside the relation, so it has
   Gowers's product property, on every sub-domain.
2. **Line energy** (`line_energy_of_productProperty`). With `p = 1` and unit
   weights, the product property gives energy `≥ γ⁸|E|⁴/N` on any set `E` of
   points of a line in the domain.
3. **Row pass.** A row with `≥ θN/2` points has energy `≥ δ₁N³`. The
   line-wise input `LineFreimanExtraction κ` gives a sub-row of size
   `≥ κ(δ₁)N` on which `φ` is Freiman-linear. Rows carry `≥ θN²/2` of the
   points, so the union `A′` has `≥ κ(δ₁)θN²/2` points
   (`dense_section_pass`).
4. **Column pass.** The same argument on the columns of `A′`. The product
   property still applies, since `A′` is a sub-domain. The result `A″` has
   `≥ κ(δ₂)κ(δ₁)θN²/4` points. Its rows lie in Freiman sub-rows and its
   columns in Freiman sub-columns, so `φ` is a Freiman bihomomorphism on
   `A″`.

`LineFreimanExtraction κ` is what Theorem 2.26 of the paper gives for a
single line. Energy `≥ δN³` gives agreement with a Freiman homomorphism on a
coset progression, on `≥ κ(δ)N` points, with `κ` quasi-polynomial (Sanders).
On the agreement set, the map respects every additive quadruple. It is
stated as a hypothesis.

`densePiece_of_lineExtraction`: `LineFreimanExtraction κ` implies
`DenseBihomPiece`, with mass `κ(δ₂)κ(δ₁)θ/4`, where `δ₁ = γ⁸(θ/2)⁴` and
`δ₂ = γ⁸(κ(δ₁)θ/4)⁴`. With `bihomExtraction_of_densePiece` and
`variety_structure_side`, the covering half of `StackableStructureAt 2` then
rests on two inputs: `LineFreimanExtraction` and
`MilicevicDeepVarietyStructure`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical

/-- **Line-wise Freiman input** (a consequence of Theorem 2.26 of
arXiv:2601.01682). A hypothesis; not asserted. -/
def LineFreimanExtraction (κ : Real → Real) : Prop :=
  (∀ δ : Real, 0 < δ → 0 < κ δ) ∧
  ∀ (N : Nat) [NeZero N] [Fact N.Prime] (E : Finset (ZMod N)) (f : ZMod N → ZMod N) (δ : Real),
    0 < δ → δ * (N : Real) ^ 3 ≤ weightedSimultaneousAdditiveEnergy E (fun _ => 1) (fun _ : Fin 1 => f) →
    ∃ E' ⊆ E, κ δ * N ≤ E'.card ∧ IsFreimanLinearOn E' f

/-- **Line energy from the product property.** -/
theorem line_energy_of_productProperty {N : Nat} [NeZero N] {B : Finset (Point N 2)}
    {φ : Point N 2 → ZMod N} {γ : Real} (h : HasProductProperty B φ γ) (y : Point N 2) (j : Fin 2)
    (E : Finset (ZMod N)) (hE : ∀ x ∈ E, replaceCoordinate y j x ∈ B) :
    γ ^ 8 * (N : Real)⁻¹ * (E.card : Real) ^ 4 ≤
      weightedSimultaneousAdditiveEnergy E (fun _ => 1)
        (fun _ : Fin 1 => coordinateRestriction φ y j) := by
  have := h 1 j (fun _ => y) E (fun _ => 1) (fun _ => zero_le_one) (fun _ x hx => hE x hx)
  simpa using this

/-- Rows and columns through a pair. -/
theorem replaceCoordinate_row {N : Nat} (a b : ZMod N) :
    replaceCoordinate (pairPoint ((0 : ZMod N), b)) 0 a = pairPoint (a, b) := by
  funext i
  fin_cases i <;> simp [replaceCoordinate, pairPoint, Function.update]

theorem replaceCoordinate_col {N : Nat} (a b : ZMod N) :
    replaceCoordinate (pairPoint (a, (0 : ZMod N))) 1 b = pairPoint (a, b) := by
  funext i
  fin_cases i <;> simp [replaceCoordinate, pairPoint, Function.update]

/-- A set of pairs is the sum of its row sections. -/
theorem card_eq_sum_rows {N : Nat} [NeZero N] (S : Finset (ZMod N × ZMod N)) :
    (S.card : Real) = ∑ b : ZMod N, ((Finset.univ.filter fun a => (a, b) ∈ S).card : Real) := by
  have h1 : (S.card : Real) = ∑ q : ZMod N × ZMod N, if q ∈ S then (1 : Real) else 0 := by
    rw [Finset.sum_boole]
    simp
  rw [h1, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_boole]

/-- A set of pairs is the sum of its column sections. -/
theorem card_eq_sum_cols {N : Nat} [NeZero N] (S : Finset (ZMod N × ZMod N)) :
    (S.card : Real) = ∑ a : ZMod N, ((Finset.univ.filter fun b => (a, b) ∈ S).card : Real) := by
  have h1 : (S.card : Real) = ∑ q : ZMod N × ZMod N, if q ∈ S then (1 : Real) else 0 := by
    rw [Finset.sum_boole]
    simp
  rw [h1, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_boole]

/-- **One dense pass.** If the sections carry `≥ τN²` points, and every
section with `≥ τN/2` points contains a good subset of size `≥ κ'N`, then
the good subsets of the dense sections carry `≥ κ'τN²/2` points. -/
theorem dense_section_pass {N : Nat} [NeZero N] (sec : ZMod N → Finset (ZMod N))
    {τ κ' : Real} (hτ : 0 ≤ τ) (hκ' : 0 ≤ κ') (Pr : ZMod N → Finset (ZMod N) → Prop)
    (htotal : τ * (N : Real) ^ 2 ≤ ∑ b, ((sec b).card : Real))
    (hext : ∀ b, τ / 2 * N ≤ (sec b).card → ∃ E' ⊆ sec b, κ' * N ≤ E'.card ∧ Pr b E') :
    ∃ (G : Finset (ZMod N)) (E' : ZMod N → Finset (ZMod N)),
      (∀ b ∈ G, E' b ⊆ sec b ∧ Pr b (E' b)) ∧
      κ' * τ / 2 * (N : Real) ^ 2 ≤ ∑ b ∈ G, ((E' b).card : Real) := by
  have hNR : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  let G := Finset.univ.filter fun b : ZMod N => τ / 2 * N ≤ (sec b).card
  have hch : ∀ b, ∃ E' : Finset (ZMod N),
      b ∈ G → E' ⊆ sec b ∧ κ' * N ≤ E'.card ∧ Pr b E' := by
    intro b
    by_cases hb : b ∈ G
    · obtain ⟨E', hsub, hcard, hPr⟩ := hext b (Finset.mem_filter.mp hb).2
      exact ⟨E', fun _ => ⟨hsub, hcard, hPr⟩⟩
    · exact ⟨∅, fun h => absurd h hb⟩
  choose E' hE' using hch
  refine ⟨G, E', fun b hb => ⟨(hE' b hb).1, (hE' b hb).2.2⟩, ?_⟩
  -- the number of dense sections
  have hsecN : ∀ b, ((sec b).card : Real) ≤ N := by
    intro b
    have : (sec b).card ≤ N := by
      calc (sec b).card ≤ (Finset.univ : Finset (ZMod N)).card := Finset.card_le_univ _
        _ = N := ZMod.card N
    exact_mod_cast this
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (ZMod N))
    (fun b => τ / 2 * N ≤ (sec b).card) (fun b => ((sec b).card : Real))
  have hsparse : ∑ b ∈ Finset.univ.filter (fun b : ZMod N => ¬ τ / 2 * N ≤ (sec b).card),
      ((sec b).card : Real) ≤ N * (τ / 2 * N) := by
    calc _ ≤ ∑ _b ∈ Finset.univ.filter (fun b : ZMod N => ¬ τ / 2 * N ≤ (sec b).card),
          τ / 2 * (N : Real) := by
          apply Finset.sum_le_sum
          intro b hb
          exact (not_le.mp (Finset.mem_filter.mp hb).2).le
      _ = (Finset.univ.filter (fun b : ZMod N => ¬ τ / 2 * N ≤ (sec b).card)).card *
          (τ / 2 * (N : Real)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ N * (τ / 2 * N) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have : (Finset.univ.filter (fun b : ZMod N => ¬ τ / 2 * N ≤ (sec b).card)).card ≤ N := by
            calc _ ≤ (Finset.univ : Finset (ZMod N)).card := Finset.card_le_univ _
              _ = N := ZMod.card N
          exact_mod_cast this
  have hdense : ∑ b ∈ G, ((sec b).card : Real) ≤ G.card * N := by
    calc _ ≤ ∑ _b ∈ G, (N : Real) := Finset.sum_le_sum fun b _ => hsecN b
      _ = G.card * N := by rw [Finset.sum_const, nsmul_eq_mul]
  have hGcard : τ / 2 * N ≤ G.card := by
    have h1 : τ * (N : Real) ^ 2 ≤ G.card * N + N * (τ / 2 * N) := by
      have := hsplit
      linarith
    have h2 : τ / 2 * N * N ≤ G.card * N := by nlinarith
    exact le_of_mul_le_mul_right h2 hNR
  calc κ' * τ / 2 * (N : Real) ^ 2 = κ' * N * (τ / 2 * N) := by ring
    _ ≤ κ' * N * G.card := mul_le_mul_of_nonneg_left hGcard (by positivity)
    _ = ∑ _b ∈ G, κ' * (N : Real) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ ∑ b ∈ G, ((E' b).card : Real) := Finset.sum_le_sum fun b hb => (hE' b hb).2.1

/-- The mass of the single extraction step. -/
def densePieceDelta₁ (γ θ : Real) : Real := γ ^ 8 * (θ / 2) ^ 4

def densePieceDelta₂ (κ : Real → Real) (γ θ : Real) : Real :=
  γ ^ 8 * (κ (densePieceDelta₁ γ θ) * θ / 4) ^ 4

def densePieceMass (κ : Real → Real) (γ θ : Real) : Real :=
  κ (densePieceDelta₂ κ γ θ) * κ (densePieceDelta₁ γ θ) * θ / 4

/-- **The single extraction step from the line-wise Freiman input.** -/
theorem densePiece_of_lineExtraction {κ : Real → Real} (hκ : LineFreimanExtraction κ) :
    DenseBihomPiece (densePieceMass κ) := by
  obtain ⟨hκpos, hline⟩ := hκ
  intro γ θ hg _ ht _
  have hδ₁ : 0 < densePieceDelta₁ γ θ := by unfold densePieceDelta₁; positivity
  have hκ₁ := hκpos _ hδ₁
  have hδ₂ : 0 < densePieceDelta₂ κ γ θ := by unfold densePieceDelta₂; positivity
  have hκ₂ := hκpos _ hδ₂
  refine ⟨by unfold densePieceMass; positivity, 0, fun N _ _ _ Delta _ hprod hproj => ?_⟩
  have hNR : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  -- selection
  let φ : Point N 2 → ZMod N := fun x => if h : ∃ y, (x, y) ∈ Delta then h.choose else 0
  let P := relationProjection Delta
  have hsel : ∀ x ∈ P, (x, φ x) ∈ Delta := by
    intro x hx
    have hex : ∃ y, (x, y) ∈ Delta := by
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨z.2, hz⟩
    simp only [φ, dif_pos hex]
    exact hex.choose_spec
  let ψ : ZMod N × ZMod N → ZMod N := fun q => φ (pairPoint q)
  let S : Finset (ZMod N × ZMod N) := Finset.univ.filter fun q => pairPoint q ∈ P
  have hSP : (S.card : Real) = P.card := by
    have : S.image pairPoint = P := by
      ext x
      simp only [S, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨q, hq, rfl⟩; exact hq
      · intro hx; exact ⟨(x 0, x 1), by rwa [pairPoint_coords], pairPoint_coords x⟩
    rw [← this, Finset.card_image_of_injective _ pairPoint_injective]
  -- row pass
  obtain ⟨G, Er, hEr, hErsum⟩ := dense_section_pass (τ := θ)
    (fun b => Finset.univ.filter fun a => (a, b) ∈ S) ht.le hκ₁.le
    (fun b E' => IsFreimanLinearOn E' fun a => ψ (a, b))
    (by rw [← card_eq_sum_rows, hSP]; exact hproj)
    (by
      intro b hb
      have hE := line_energy_of_productProperty (hprod P φ hsel) (pairPoint ((0 : ZMod N), b)) 0
        (Finset.univ.filter fun a => (a, b) ∈ S) (by
          intro a ha
          rw [replaceCoordinate_row]
          exact (Finset.mem_filter.mp (Finset.mem_filter.mp ha).2).2)
      have henergy : densePieceDelta₁ γ θ * (N : Real) ^ 3 ≤
          weightedSimultaneousAdditiveEnergy (Finset.univ.filter fun a => (a, b) ∈ S) (fun _ => 1)
            (fun _ : Fin 1 => fun a => ψ (a, b)) := by
        have hfun : (fun a => ψ (a, b)) = coordinateRestriction φ (pairPoint ((0 : ZMod N), b)) 0 := by
          funext a
          simp only [ψ, coordinateRestriction, replaceCoordinate_row]
        rw [hfun]
        refine le_trans ?_ hE
        have h4 : (θ / 2 * N) ^ 4 ≤ (((Finset.univ.filter fun a => (a, b) ∈ S).card : Real)) ^ 4 :=
          pow_le_pow_left₀ (by positivity) hb 4
        unfold densePieceDelta₁
        have : γ ^ 8 * (N : Real)⁻¹ * (θ / 2 * N) ^ 4 = γ ^ 8 * (θ / 2) ^ 4 * (N : Real) ^ 3 := by
          field_simp
        rw [← this]
        exact mul_le_mul_of_nonneg_left h4 (by positivity)
      exact hline N _ _ _ hδ₁ henergy)
  -- the surviving set after the row pass
  let A₁ : Finset (ZMod N × ZMod N) := Finset.univ.filter fun q => q.2 ∈ G ∧ q.1 ∈ Er q.2
  have hA₁S : A₁ ⊆ S := by
    intro q hq
    obtain ⟨hqG, hqE⟩ := (Finset.mem_filter.mp hq).2
    have h := (Finset.mem_filter.mp ((hEr q.2 hqG).1 hqE)).2
    simpa using h
  have hA₁card : densePieceDelta₁ γ θ = densePieceDelta₁ γ θ ∧
      κ (densePieceDelta₁ γ θ) * θ / 2 * (N : Real) ^ 2 ≤ A₁.card := by
    refine ⟨rfl, ?_⟩
    rw [card_eq_sum_rows]
    refine hErsum.trans (le_of_eq_of_le rfl ?_)
    calc ∑ b ∈ G, ((Er b).card : Real) ≤ ∑ b, ((Er b).card : Real) * (if b ∈ G then 1 else 0) := by
          rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun b => b ∈ G)]
          simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
          have : ∑ x ∈ Finset.univ.filter (fun b => b ∉ G), ((Er x).card : Real) * (if x ∈ G then 1 else 0) = 0 := by
            apply Finset.sum_eq_zero
            intro b hb
            simp [(Finset.mem_filter.mp hb).2]
          rw [this, add_zero]
          apply le_of_eq
          apply Finset.sum_congr rfl
          intro b hb
          simp [hb]
      _ = ∑ b, ((Finset.univ.filter fun a => (a, b) ∈ A₁).card : Real) := by
          apply Finset.sum_congr rfl
          intro b _
          by_cases hb : b ∈ G
          · simp only [hb, if_true, mul_one]
            congr 2
            ext a
            simp [A₁, hb]
          · simp only [hb, if_false, mul_zero]
            have : (Finset.univ.filter fun a => (a, b) ∈ A₁) = ∅ := by
              apply Finset.filter_eq_empty_iff.mpr
              intro a _ ha
              exact hb (Finset.mem_filter.mp ha).2.1
            rw [this, Finset.card_empty, Nat.cast_zero]
  -- column pass
  let τ := κ (densePieceDelta₁ γ θ) * θ / 2
  let P₁ : Finset (Point N 2) := A₁.image pairPoint
  have hsel₁ : ∀ x ∈ P₁, (x, φ x) ∈ Delta := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
    exact hsel _ (Finset.mem_filter.mp (hA₁S hq)).2
  obtain ⟨H, Ec, hEc, hEcsum⟩ := dense_section_pass (τ := τ)
    (fun a => Finset.univ.filter fun b => (a, b) ∈ A₁) (by positivity) hκ₂.le
    (fun a E' => IsFreimanLinearOn E' fun b => ψ (a, b))
    (by rw [← card_eq_sum_cols]; exact hA₁card.2)
    (by
      intro a ha
      have hE := line_energy_of_productProperty (hprod P₁ φ hsel₁) (pairPoint (a, (0 : ZMod N))) 1
        (Finset.univ.filter fun b => (a, b) ∈ A₁) (by
          intro b hb
          rw [replaceCoordinate_col]
          exact Finset.mem_image_of_mem _ (Finset.mem_filter.mp hb).2)
      have henergy : densePieceDelta₂ κ γ θ * (N : Real) ^ 3 ≤
          weightedSimultaneousAdditiveEnergy (Finset.univ.filter fun b => (a, b) ∈ A₁) (fun _ => 1)
            (fun _ : Fin 1 => fun b => ψ (a, b)) := by
        have hfun : (fun b => ψ (a, b)) = coordinateRestriction φ (pairPoint (a, (0 : ZMod N))) 1 := by
          funext b
          simp only [ψ, coordinateRestriction, replaceCoordinate_col]
        rw [hfun]
        refine le_trans ?_ hE
        have hτ2 : τ / 2 * N = κ (densePieceDelta₁ γ θ) * θ / 4 * N := by ring
        have h4 : (κ (densePieceDelta₁ γ θ) * θ / 4 * N) ^ 4 ≤
            (((Finset.univ.filter fun b => (a, b) ∈ A₁).card : Real)) ^ 4 :=
          pow_le_pow_left₀ (by positivity) (hτ2 ▸ ha) 4
        unfold densePieceDelta₂
        have : γ ^ 8 * (N : Real)⁻¹ * (κ (densePieceDelta₁ γ θ) * θ / 4 * N) ^ 4 =
            γ ^ 8 * (κ (densePieceDelta₁ γ θ) * θ / 4) ^ 4 * (N : Real) ^ 3 := by
          field_simp
        rw [← this]
        exact mul_le_mul_of_nonneg_left h4 (by positivity)
      exact hline N _ _ _ hδ₂ henergy)
  -- the final domain
  let A₂ : Finset (ZMod N × ZMod N) := Finset.univ.filter fun q => q.1 ∈ H ∧ q.2 ∈ Ec q.1
  have hA₂A₁ : A₂ ⊆ A₁ := by
    intro q hq
    obtain ⟨hqH, hqE⟩ := (Finset.mem_filter.mp hq).2
    exact (Finset.mem_filter.mp ((hEc q.1 hqH).1 hqE)).2
  refine ⟨ψ, A₂, ⟨?_, ?_⟩, ?_, ?_⟩
  · -- horizontal quadruples: inside a Freiman sub-row
    intro x₁ x₂ x₃ x₄ y hsum h1 h2 h3 h4
    have hrow : ∀ x, (x, y) ∈ A₂ → y ∈ G ∧ x ∈ Er y := fun x hx =>
      (Finset.mem_filter.mp (hA₂A₁ hx)).2
    obtain ⟨hyG, hx1⟩ := hrow x₁ h1
    have hfr := (hEr y hyG).2 x₁ x₂ x₃ x₄ hx1 (hrow x₂ h2).2 (hrow x₃ h3).2 (hrow x₄ h4).2 hsum
    show ψ (x₁, y) + ψ (x₂, y) - ψ (x₃, y) - ψ (x₄, y) ∈ ({0} : Set (ZMod N))
    simp only [Set.mem_singleton_iff]
    linear_combination hfr
  · -- vertical quadruples: inside a Freiman sub-column
    intro x y₁ y₂ y₃ y₄ hsum h1 h2 h3 h4
    have hcol : ∀ y, (x, y) ∈ A₂ → x ∈ H ∧ y ∈ Ec x := fun y hy => (Finset.mem_filter.mp hy).2
    obtain ⟨hxH, hy1⟩ := hcol y₁ h1
    have hfc := (hEc x hxH).2 y₁ y₂ y₃ y₄ hy1 (hcol y₂ h2).2 (hcol y₃ h3).2 (hcol y₄ h4).2 hsum
    show ψ (x, y₁) + ψ (x, y₂) - ψ (x, y₃) - ψ (x, y₄) ∈ ({0} : Set (ZMod N))
    simp only [Set.mem_singleton_iff]
    linear_combination hfc
  · -- the mass
    have hsum : ∑ a ∈ H, ((Ec a).card : Real) ≤ A₂.card := by
      rw [card_eq_sum_cols]
      calc ∑ a ∈ H, ((Ec a).card : Real) ≤ ∑ a, ((Finset.univ.filter fun b => (a, b) ∈ A₂).card : Real) := by
            rw [← Finset.sum_subset (Finset.subset_univ H)]
            · apply Finset.sum_le_sum
              intro a ha
              apply Nat.cast_le.mpr
              apply Finset.card_le_card
              intro b hb
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_filter.mpr
                ⟨Finset.mem_univ _, ha, hb⟩⟩
            · intro a _ ha
              have : (Finset.univ.filter fun b => (a, b) ∈ A₂) = ∅ := by
                apply Finset.filter_eq_empty_iff.mpr
                intro b _ hb
                exact ha (Finset.mem_filter.mp hb).2.1
              rw [this, Finset.card_empty, Nat.cast_zero]
        _ = _ := rfl
    have heq : densePieceMass κ γ θ * (N : Real) ^ 2 =
        κ (densePieceDelta₂ κ γ θ) * τ / 2 * (N : Real) ^ 2 := by
      unfold densePieceMass
      ring
    rw [heq]
    exact hEcsum.trans hsum
  · -- inside the relation
    intro q hq
    exact hsel _ (Finset.mem_filter.mp (hA₁S (hA₂A₁ hq))).2

/-- **The covering half of `StackableStructureAt 2` from two inputs:**
the line-wise Freiman input (Theorem 2.26 of arXiv:2601.01682) and the
deep-agreement form of Milićević's structure theorem. -/
theorem structure_side_of_line_and_milicevic {κ : Real → Real} (hκ : LineFreimanExtraction κ)
    {D : Nat} (hM : MilicevicDeepVarietyStructure D)
    (gamma theta : Real) (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1) :
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ Gamma : Finset (Point N 2 × ZMod N),
        (Gamma.card : Real) ≤ gamma ^ (-(2 : Int)) * (N : Real) ^ 2 →
        RelationProductProperty gamma Gamma →
        ∃ J : Finset (Point N 2), (1 - theta) * (N : Real) ^ 2 ≤ J.card ∧
          ∃ (K : Nat) (G : Fin K → Finset (ZMod N × ZMod N))
            (f : Fin K → ZMod N × ZMod N → ZMod N),
            (K : Real) ≤ bihomFamilySize (densePieceMass κ) gamma (theta / 2) *
              Real.exp (milicevicBound D
                (theta / 2 / bihomFamilySize (densePieceMass κ) gamma (theta / 2))) ∧
            (∀ k, IsVarietyPiece D
              (theta / 2 / bihomFamilySize (densePieceMass κ) gamma (theta / 2)) (f k) (G k)) ∧
            restrictRelation Gamma J ⊆ section16FinsetUnion
              (fun k => partialGraph ((G k).image pairPoint) (fun x => f k (x 0, x 1))) :=
  variety_structure_side hM (bihomExtraction_of_densePiece (densePiece_of_lineExtraction hκ))
    gamma theta hg hg1 ht ht1

end LeanProofs.GowersSzemeredi
