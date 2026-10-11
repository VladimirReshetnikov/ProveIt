import GowersSzemeredi.Proofs16SinglePieceGradedGlobal

/-! Counting the remainder vertices by face dimension (Notes L.10, G4c).

Vertex `e ∈ {0,1}^k` of the remainder lives on a face of dimension
`|S_e| = |e| + 1` (`card_vertexDirections`). Graded providers cost
`Σ_{e ≠ top} f(|S_e|)` instead of `(2^k − 1)·f(k)`. For the class degrees
`f(l) = 68·2^l + 1` this is `136·3^k + 2^k − 136·2^k − 1`
(`vertexFaceCounts_weighted_le`), because `Σ_e 2^|e| = 3^k`
(`sum_two_pow_boolWeight`). -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem boolWeight_eq_card {k : Nat} (e : Fin k → Bool) :
    boolWeight e = (Finset.univ.filter fun i => e i = true).card := by
  unfold boolWeight countWhere
  congr 1
  ext i
  simp

/-- The face of vertex `e` has dimension `|e| + 1`. -/
theorem card_vertexDirections {k : Nat} (e : Fin k → Bool) :
    (section16VertexDirections e).card = boolWeight e + 1 := by
  classical
  have hset : section16VertexDirections e = insert (Fin.last k)
      ((Finset.univ.filter fun i => e i = true).map Fin.castSuccEmb) := by
    ext j
    cases j using Fin.lastCases with
    | last => simp
    | cast i =>
      rw [section16VertexDirections_castSucc]
      simp [Fin.castSucc_ne_last]
  have hnot : Fin.last k ∉ (Finset.univ.filter fun i => e i = true).map Fin.castSuccEmb := by
    simp [Fin.castSucc_ne_last]
  rw [hset, Finset.card_insert_of_notMem hnot, Finset.card_map, boolWeight_eq_card]

/-- `Σ_e 2^|e| = 3^k`. -/
theorem sum_two_pow_boolWeight (k : Nat) :
    ∑ e : Fin k → Bool, 2 ^ boolWeight e = 3 ^ k := by
  classical
  have h : ∀ e : Fin k → Bool, 2 ^ boolWeight e = ∏ i, (if e i = true then 2 else 1) := by
    intro e
    rw [boolWeight_eq_card, Finset.prod_ite]
    simp
  calc ∑ e : Fin k → Bool, 2 ^ boolWeight e
      = ∑ e : Fin k → Bool, ∏ i, (if e i = true then 2 else 1) := Finset.sum_congr rfl fun e _ => h e
    _ = ∏ _i : Fin k, ∑ b : Bool, (if b = true then 2 else 1) := by
        rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    _ = 3 ^ k := by simp

/-- Summing by blocks: `Σ_j |block j|·F(j) = Σ_{e ≠ top} F(g e)`. -/
theorem sum_vertexBlock_eq (k : Nat) (g : (Fin k → Bool) → Nat) (F : Nat → Nat) (K : Nat)
    (hgK : ∀ e, e ≠ (fun _ => true) → g e < K) :
    ∑ j ∈ Finset.range K, (vertexBlock k g j).card * F j =
      ∑ e ∈ Finset.univ.filter (fun e : Fin k → Bool => e ≠ fun _ => true), F (g e) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := g) (t := Finset.range K)
    (fun e he => Finset.mem_range.mpr (hgK e (Finset.mem_filter.mp he).2))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_congr rfl (fun e he => by rw [(Finset.mem_filter.mp he).2]), Finset.sum_const,
    smul_eq_mul]
  congr 1
  unfold vertexBlock
  rw [Finset.filter_filter]

/-- **The graded vertex count**, exactly:
`Σ_j n_j·(68·2^j + 1) ≤ 136·3^k + 2^k − (136·2^k + 1)` (the top vertex is excluded). -/
theorem vertexFaceCounts_weighted_le (k : Nat) :
    ∑ j ∈ Finset.range (k + 1), vertexFaceCounts k j * (68 * 2 ^ j + 1) ≤
      136 * 3 ^ k + 2 ^ k - (136 * 2 ^ k + 1) := by
  classical
  have hsum := sum_vertexBlock_eq k (fun e => (section16VertexDirections e).card)
    (fun j => 68 * 2 ^ j + 1) (k + 1) (fun e he => section16VertexDirections_card_lt he)
  unfold vertexFaceCounts
  rw [hsum]
  set f : (Fin k → Bool) → Nat := fun e => 68 * 2 ^ (section16VertexDirections e).card + 1 with hf
  have hf' : ∀ e, f e = 136 * 2 ^ boolWeight e + 1 := by
    intro e
    rw [hf]
    dsimp only
    rw [card_vertexDirections, pow_succ]
    ring
  have htotal : ∑ e : Fin k → Bool, f e = 136 * 3 ^ k + 2 ^ k := by
    rw [Finset.sum_congr rfl fun e _ => hf' e, Finset.sum_add_distrib, ← Finset.mul_sum,
      sum_two_pow_boolWeight]
    simp
  have htop : f (fun _ => true) = 136 * 2 ^ k + 1 := by
    rw [hf' (fun _ => true), boolWeight_eq_card]
    simp
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun e : Fin k → Bool => e ≠ fun _ => true) f
  have hnot : (Finset.univ.filter fun e : Fin k → Bool => ¬ e ≠ fun _ => true) =
      {fun _ => true} := by
    ext e
    simp
  rw [hnot, Finset.sum_singleton, htop, htotal] at hsplit
  show ∑ e ∈ Finset.univ.filter (fun e : Fin k → Bool => e ≠ fun _ => true), f e ≤ _
  omega

end LeanProofs.GowersSzemeredi
