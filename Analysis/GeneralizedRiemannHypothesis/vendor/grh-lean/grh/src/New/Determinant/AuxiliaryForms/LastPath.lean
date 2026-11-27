import New.Determinant.AuxiliaryForms.GridFirstColumns
import New.Determinant.AuxiliaryForms.RegularParameters

/-!
# The branching pairing and the periods on the last path

On the last path all spaces are positive definite. Forms are read as algebraic forms on the groups
`New.stdSpace`, and theta lifts become algebraic. Branching from `GL (n + 1)` to `GL n` for
interlacing parameters is an integral pairing with explicit bounds, so a period over the smaller
definite group is a constant times an integral of this pairing over the finite points. This gives
the finite sum `Ξ = New.Data.lastPathPeriod` to which all periods on the last path are proportional.
This is part of the construction of spanning forms on `U(Y_0)` with integral twisted lifts and
bounded conjugates; the denominators and the conjugates of `Ξ` are bounded in
`New.Determinant.AuxiliaryForms.SpanningForms`. The prefix `lastPath` of a name refers to the
last path, which consists of the edges between the nodes `(z, j, m)`, `j ≤ m`.

## Main definitions and results

* `New.Exchange.IsBranchingPairing`: an integer matrix whose pairing is equivariant for block
  matrices, is bounded, and computes the period of two algebraic forms over the smaller definite
  group as a constant times the integral of the pairing of their values at finite points.
* `New.Exchange.exists_isBranchingPairing`: such a matrix exists. It is the branching matrix of
  `New.exists_branching_matrix` followed by the duality of `New.exists_isDualPairing_of_isHCParam`.
* `New.Data.exists_lastPathPeriod_mem_smul_norm_le`: for a path datum, `Ξ` is a sum of a controlled
  number of terms, each with the bound that holds for the pairings of the vectors reached by the
  lifts.
* `New.Data.isProportional_lastPathPeriod`: every period on the last path is a constant times `Ξ`
  divided by the index of the level `J(𝔪₀)` on `Y_m`, which differs from the index of `J(𝔪)` by a
  constant factor.

Notions from other files:
* `New.IsHCParam`: `l` lists twice the Harish-Chandra parameter of the weight `(κ, e)`, in some
  order; `κ` counts the columns of each height and `e` is the exponent of the determinant.
* `New.ofAlgForm`: the function g ↦ ⟨v⁺, ρ(g_∞⁻¹) φ(g_f)⟩ on the adelic group attached to an
  algebraic form φ, with v⁺ = `New.highestVector` for the parameter.
* `New.classIntegral`: the integral over Γ \ G of a smooth left Γ-invariant function, for the Haar
  measure that gives the level K volume 1, written as a sum over classes.
* `New.StdClasses`: the double cosets of G_f by its rational points on the left and a level K on
  the right.
* `New.Data`: the admissible data `D` for the fixed parameters `P`. They give the CM field `D.E`,
  its infinite places `D.Φ` and the number `m = D.m` of lifts in the chain.
* `New.Data.gridSpace`: the Hermitian space at the node `(z, i, j)`, for the offset `0`. It is
  `Y^i_j` if `z = false` and `Ỹ^j_i` if `z = true`, and `Y_j = Y^0_j`.
* Moduli of a twist `ϑ` with places `Q`, where `ϖ = D.piM` and `b = D.natB`: `𝔪 = ϖ ^ b Q`
  (`New.Data.gridModulus`), `𝔪₀ = ϖ Q` and `𝔟 = ϖ ^ b` (`New.Data.triangleModulus`). The level
  `J(𝔞)` consists of the integral finite points that reduce to `1` modulo `𝔞`.
-/

noncomputable section

/-! ## Branching pairing of interlacing weights of GL(n+1) and GL(n) -/

namespace New.Exchange

open Matrix Finset Fintype «GL» Space Seesaw Real
open NumberField (InfinitePlace)

section Interlacing

variable {Φ : Type} [Fintype Φ] {κ κ₀ : Φ → ℕ → ℕ} {e e₀ : Φ → ℤ}

/-- Row `i` of the diagram in rank `N` exceeds row `i + 1` by the number `κ τ (i + 1)` of columns
of height `i + 1`, if `i + 1 < N`. -/
lemma diagramWeight_eq_add_succ {N i : ℕ} (τ : Φ) (hi : i + 1 < N) :
    diagramWeight (fun _ : Φ ↦ N) κ (τ, i) =
      κ τ (i + 1) + diagramWeight (fun _ : Φ ↦ N) κ (τ, i + 1) := by
  have h_Ioo : Ioo i N = insert (i + 1) (Ioo (i + 1) N) := by grind
  rw [diagramWeight_apply, diagramWeight_apply, h_Ioo, sum_insert (by simp)]

/-- With the constant bound `N`, `diagramWeight` vanishes at `(τ, i)` whenever `N ≤ i + 1`. Only
columns of height `h < N` count, and no such `h` has `i < h`. -/
lemma diagramWeight_eq_zero_of_le_succ {N i : ℕ} (τ : Φ) (hi : N ≤ i + 1) :
    diagramWeight (fun _ : Φ ↦ N) κ (τ, i) = 0 := by
  simp [diagramWeight_apply, show Ioo i N = ∅ by grind]

/-- Let `l'` list twice the Harish-Chandra parameter of the weight `(κ, e)` of `GL n'` and `l` that
of the weight `(κ₀, e₀)` of `GL n`, where `#n' = #n + 1`. If `l` and `l'` interlace, then the
highest weights interlace: entry `q` of the highest weight of `(κ₀, e₀)` lies between the entries
`q + 1` and `q` of that of `(κ, e)`. An entry is the exponent of the determinant plus a row length
`diagramWeight`. -/
lemma add_diagramWeight_mem_Icc_of_interlace {n n' : Type} [DecidableEq Φ] [Fintype n]
    [DecidableEq n] [Fintype n'] [DecidableEq n'] {l : Φ → n → ℤ} {l' : Φ → n' → ℤ}
    (hn : card n' = card n + 1) (hl' : IsHCParam κ e l') (hl : IsHCParam κ₀ e₀ l)
    (h_interlace : ∀ (w : Φ) (x : ℤ),
      (#{j : n' | x < l' w j} - #{i : n | x < l w i} : ℤ) ∈ Icc 0 1)
    (w : Φ) {q : ℕ} (hq : q < card n) :
    (e₀ w + diagramWeight (fun _ : Φ ↦ card n) κ₀ (w, q) : ℤ) ∈
      Icc (e w + diagramWeight (fun _ : Φ ↦ card n') κ (w, q + 1) : ℤ)
        (e w + diagramWeight (fun _ : Φ ↦ card n') κ (w, q)) := by
  -- Take the index `i` at position `q` of `l w` and `j`, `j'` at positions `q`, `q + 1` of `l' w`.
  obtain ⟨i, hi_pos, hi_val, hi_count⟩ := hl.exists_decreasingPosition_eq w hq
  obtain ⟨j, hj_pos, hj_val, -⟩ := hl'.exists_decreasingPosition_eq w (q := q) (by lia)
  obtain ⟨j', -, hj'_val, hj'_count⟩ := hl'.exists_decreasingPosition_eq w (q := q + 1) (by lia)
  rw [decreasingPosition] at hi_pos hj_pos
  have h_upper : l w i ≤ l' w j := by
    by_contra! h_lt
    -- More than `q` entries of `l w`, but only `q` entries of `l' w`, would exceed `l' w j`.
    have h_many : q < #{k : n | l' w j < l w k} := hi_count _ h_lt
    linarith [(mem_Icc.1 (h_interlace w (l' w j))).1]
  have h_lower : l' w j' ≤ l w i := by
    by_contra! h_lt
    -- More than `q + 1` entries of `l' w`, but only `q` entries of `l w`, would exceed `l w i`.
    have h_many : q + 1 < #{k : n' | l w i < l' w k} := hj'_count _ h_lt
    linarith [(mem_Icc.1 (h_interlace w (l w i))).2]
  simp only [hi_val, hj_val, hj'_val, hcParameter] at h_upper h_lower
  rw [mem_Icc]
  lia

/-- Suppose that at each place `w : Φ` the highest weight of `(κ₀, e₀)` for `GL n` interlaces that
of `(κ, e)` for `GL n'`, where `#n' = #n + 1`. Here `boxes κ N` is the total over all places of the
boxes in the columns of height less than `N`: the sum of `h * κ w h` over `w : Φ` and `h < N`. Then
`κ₀` has, in this total, at most as many boxes in columns of height below `#n` as `κ` has in columns
of height below `#n'`. -/
lemma boxes_le_boxes_of_interlace {n n' : Type} [Fintype n] [Fintype n'] (hn : card n' = card n + 1)
    (h_interlace : ∀ w : Φ, ∀ q < card n,
      (e₀ w + diagramWeight (fun _ : Φ ↦ card n) κ₀ (w, q) : ℤ) ∈
        Icc (e w + diagramWeight (fun _ : Φ ↦ card n') κ (w, q + 1) : ℤ)
          (e w + diagramWeight (fun _ : Φ ↦ card n') κ (w, q))) :
    boxes κ₀ (card n) ≤ boxes κ (card n') := by
  classical
  -- No height lies strictly between `#n` and `#n + 1`.
  have h_fits : FitsRanks (fun _ : Φ ↦ n) (fun _ : Φ ↦ n') κ := by grind
  rw [← FitsRanks.refl.sum_diagramWeight_eq_boxes, ← h_fits.sum_diagramWeight_eq_boxes]
  -- Each row of `κ₀` is at most the row of `κ` with the same number.
  refine sum_le_sum fun ⟨w, q, hq⟩ _ ↦ ?_
  have h_row : (e₀ w + diagramWeight (fun _ ↦ card n) κ₀ (w, q) : ℤ) ≤
      e w + diagramWeight (fun _ ↦ card n') κ (w, q) := (mem_Icc.1 (h_interlace w q hq)).2
  -- The last rows are empty, so the lower bound at the last entry compares the exponents.
  have h_exp : e w ≤ e₀ w := by
    simpa (disch := lia) [diagramWeight_eq_zero_of_le_succ] using
      (mem_Icc.1 (h_interlace w (card n - 1) (by lia))).1
  lia

/-- If the highest weight of `(κ₀, e₀)` in rank `N > 0` interlaces that of `(κ, e)` in rank `N + 1`,
then `κ₀` arises from `κ` by removing a horizontal strip: of the `κ τ q` columns of height `q`,
`γ τ q` lose a box and `κ₁ τ q` keep theirs, and the columns of height `N` that keep their box are
added to the exponent of the determinant. -/
lemma exists_add_eq_of_interlace {N : ℕ} (hN : 0 < N)
    (h_interlace : ∀ w : Φ, ∀ q < N,
      (e₀ w + diagramWeight (fun _ : Φ ↦ N) κ₀ (w, q) : ℤ) ∈
        Icc (e w + diagramWeight (fun _ : Φ ↦ N + 1) κ (w, q + 1) : ℤ)
          (e w + diagramWeight (fun _ : Φ ↦ N + 1) κ (w, q))) :
    ∃ γ κ₁ : Φ → ℕ → ℕ,
      γ + κ₁ = κ ∧
      (∀ τ : Φ, ∀ q ∈ Ioo 0 N, κ₀ τ q = κ₁ τ q + γ τ (q + 1)) ∧
      ∀ τ : Φ, e₀ τ = e τ + κ₁ τ N := by
  -- `d τ q` is entry `q` of the highest weight `(κ₀, e₀)` less entry `q + 1` of `(κ, e)`; that
  -- many of the `κ τ (q + 1)` columns of height `q + 1` keep their box.
  let d (τ : Φ) (q : ℕ) : ℤ :=
    e₀ τ + diagramWeight (fun _ ↦ N) κ₀ (τ, q) - (e τ + diagramWeight (fun _ ↦ N + 1) κ (τ, q + 1))
  have hd (τ : Φ) (q : ℕ) (hq : q < N) : 0 ≤ d τ q ∧ d τ q ≤ κ τ (q + 1) := by
    simpa [d, diagramWeight_eq_add_succ τ (Nat.succ_lt_succ hq), sub_le_iff_le_add,
      add_left_comm] using h_interlace τ q hq
  let γ (τ : Φ) (q : ℕ) : ℕ := κ τ q - (d τ (q - 1)).toNat
  let κ₁ (τ : Φ) (q : ℕ) : ℕ := min (κ τ q) (d τ (q - 1)).toNat
  refine ⟨γ, κ₁, funext₂ fun τ q ↦ Nat.sub_add_min_cancel (κ τ q) _, fun τ q hq ↦ ?_, fun τ ↦ ?_⟩
  · obtain _ | q := q
    · simp at hq
    have hq_lt : q + 1 < N := (mem_Ioo.1 hq).2
    have h_diff : d τ q - d τ (q + 1) = κ₀ τ (q + 1) - κ τ (q + 2) := by
      simp only [d, diagramWeight_eq_add_succ τ hq_lt,
        diagramWeight_eq_add_succ τ (Nat.succ_lt_succ hq_lt)]
      lia
    simp only [γ, κ₁, add_tsub_cancel_right]
    grind [hd τ q, hd τ (q + 1)]
  · have h_diff : d τ (N - 1) = e₀ τ - e τ := by
      simp (disch := lia) [d, diagramWeight_eq_zero_of_le_succ]
    simp only [κ₁]
    grind [hd τ (N - 1)]

end Interlacing

variable {E n n' : Type} [Field E] [CMType E] [Fintype n] [Fintype n']
  {κ κ' : InfinitePlace E → ℕ → ℕ} {e e' : InfinitePlace E → ℤ}

/-- Cauchy–Schwarz for a duality pairing. Let the integer matrix `A` be a duality (`IsDualPairing`)
between the weights `(κ', e')` and `(κ, e)` of `GL n` for the doubled Harish-Chandra parameter `l`:
its pairing `v' ⬝ᵥ A *ᵥ v` of coordinate vectors of the two Weyl modules is invariant under `GL n`,
and pairing with `v` is the Hermitian product with a vector of the same Gram norm as `v`. Then the
pairing is bounded by the product of the Gram norms, the square roots of `weylNormSq`. -/
lemma norm_dotProduct_mulVec_le_of_isDualPairing [DecidableEq n] {l : InfinitePlace E → n → ℤ}
    {A : Matrix (WeylIndex n κ') (WeylIndex n κ) ℤ} (hA : IsDualPairing κ κ' e e' l A)
    (v' : WeylIndex n κ' → ℂ) (v : WeylIndex n κ → ℂ) :
    ‖v' ⬝ᵥ A.map (↑) *ᵥ v‖ ≤ √(weylNormSq v' * weylNormSq v) := by
  obtain ⟨x, hx_norm, hx_pairing⟩ := hA.exists_eq_gramForm v
  rw [hx_pairing, gramForm_apply, ← hx_norm, weylNormSq, weylNormSq]
  exact le_sqrt_of_sq_le (posDef_cauchy_schwarz weylGramOver_posDef x v')

/-- The properties of a branching pairing over the CM field `E`. Here `(κ, e)` is a weight of
`GL n'` (column multiplicities and exponents of the determinant at the infinite places of `E`) with
doubled Harish-Chandra parameter `l'`, and `(κ', e')` is a weight of the smaller group `GL n` with
doubled parameter `-l`. The bijection `σ` adds one index to `n`, compatibly with the signs `s`, `r`
and `t` of the Hermitian forms. The integer matrix `B` pairs coordinate vectors `v'`, `v` of the two
Weyl modules (indexed by `WeylIndex`, with the action `weylRep`) to `v' ⬝ᵥ B *ᵥ v`. The properties
are that this pairing is equivariant for block matrices, is bounded in the Gram norms, and computes
periods: an integral over the rank-`n` adelic group of a product of two algebraic forms, read as
functions, is a constant times an integral over finite points of the pairing of their values. -/
structure IsBranchingPairing [DecidableEq n'] [DecidableEq n]
    {s : n → ℤˣ} {t : n' → ℤˣ} {r : Unit → ℤˣ} {σ : n ⊕ Unit ≃ n'} (hσ : (s ⊕ᵥ r) ∘ σ.symm = t)
    (e e' : InfinitePlace E → ℤ) (l : InfinitePlace E → n → ℤ) (l' : InfinitePlace E → n' → ℤ)
    (B : Matrix (WeylIndex n κ') (WeylIndex n' κ) ℤ) : Prop where
  /-- The pairing is invariant under a unitary matrix `g` acting on the left and `diag (g, u)` on
  the right, up to `∏ τ, det (f τ u) ^ N τ`, where the exponents `N τ` are bounded. -/
  exists_equivariant : ∃ N : InfinitePlace E → ℤ,
    (∀ (S R : Type) [CommRing S] [StarRing S] [Field R] [CharZero R]
        (f : InfinitePlace E → S →+* R) (g : U (1 : Matrix n n S)) (u : U (1 : Matrix Unit Unit S))
        (v' : WeylIndex n κ' → R) (v : WeylIndex n' κ → R),
      weylRep κ' e' (fun τ : InfinitePlace E ↦ g.val.map (f τ)) *ᵥ v' ⬝ᵥ
          B.map (↑) *ᵥ
            weylRep κ e (fun τ : InfinitePlace E ↦ (U.block σ (g, u)).val.map (f τ)) *ᵥ v =
        (∏ τ : InfinitePlace E, (u.val.map (f τ)).det ^ N τ : Rˣ) * v' ⬝ᵥ B.map (↑) *ᵥ v) ∧
    ∀ τ : InfinitePlace E, (N τ).natAbs ≤ boxes κ (Fintype.card n') + (e τ).natAbs
  /-- If `M` bounds the number of boxes of `κ`, the pairing is at most `(M ^ M) ^ 3` times the
  product of the Gram norms. -/
  norm_le : ∀ M : ℕ, boxes κ (Fintype.card n') ≤ M →
    ∀ (v' : WeylIndex n κ' → ℂ) (v : WeylIndex n' κ → ℂ),
      ‖v' ⬝ᵥ B.map (↑) *ᵥ v‖ ≤ ((M ^ M) ^ 3 : ℕ) * √(New.weylNormSq v') * √(New.weylNormSq v)
  /-- The pairing gives the periods over the group of rank `n`. Read algebraic forms `η`, `φ` as
  functions on the adelic groups by `ofAlgForm`. For each real point `g` there is a constant `c`
  with this property. Let `V` be standard (`IsStd`: all signs are `1` and its point is the
  identity). The integral of `η(x) φ(diag (x, u) g)` over the adelic quotient of `V` is `c` over
  the index `stdLevelIndex K = [K₀ : K ∩ K₀]` of the level `K` in the integral points `K₀`, times
  the integral (`classIntegral`) of the pairing of `η(h)` and `φ(diag (h, u))` over the finite
  points `h` modulo the rational points. -/
  exists_integral_eq : ∀ g : GInf E t, ∃ c : ℂ,
    ∀ (V : Space E n s) [V.IsStd] (η : AlgForm n κ' e') (φ : AlgForm n' κ e) (u : Gf E Unit)
      (K : Subgroup (Gf E n)) [IsLevel K],
    ∫ x : G E s, ofAlgForm (-l) s η x *
        ofAlgForm l' t φ (G.reindex σ hσ (G.sum (x, 1, u)) * (g, 1)) ∂V.quotMeasure =
      c / stdLevelIndex K *
        classIntegral stdRatPoints K fun h : Gf E n ↦
          η.val h ⬝ᵥ B.map (↑) *ᵥ φ.val (U.block σ (h, u))

/-- Let `(κ, e)` be a weight of `GL n'`, `#n' = #n + 1` by the bijection `σ`, with doubled
Harish-Chandra parameter `l'`. Let `(κ', e')` be a weight of the smaller group `GL n` with doubled
parameter `-l`, where `l` and `l'` interlace, and let all signs be `1`, so that the unitary groups
are definite. Then there is an integer matrix `B` that is a branching pairing. -/
lemma exists_isBranchingPairing [DecidableEq n'] [DecidableEq n] [Nonempty n]
    {l : InfinitePlace E → n → ℤ} {l' : InfinitePlace E → n' → ℤ}
    {s : n → ℤˣ} {t : n' → ℤˣ} {r : Unit → ℤˣ} {σ : n ⊕ Unit ≃ n'} (hσ : (s ⊕ᵥ r) ∘ σ.symm = t)
    (ht : t = 1) (hl' : IsHCParam κ e l') (hl : IsHCParam κ' e' (-l))
    (h_interlace : ∀ (w : InfinitePlace E) (x : ℤ),
      (#{j : n' | x < l' w j} - #{i : n | x < l w i} : ℤ) ∈ Icc 0 1) :
    ∃ B : Matrix (WeylIndex n κ') (WeylIndex n' κ) ℤ, IsBranchingPairing hσ e e' l l' B := by
  -- Take the weight `(κ₀, e₀)` of parameter `l`. Interlacing makes `κ / κ₀` a horizontal strip
  -- `γ`, so there is a branching matrix `b` from `κ` to `κ₀`; compose it with the duality
  -- pairing `A` between `κ'` and `κ₀`.
  subst ht
  obtain rfl : s = 1 := funext fun i ↦ by simpa using congrFun hσ (σ (.inl i))
  obtain rfl : r = 1 := funext fun i ↦ by simpa using congrFun hσ (σ (.inr i))
  have hn : card n' = card n + 1 := by simpa using card_congr σ.symm
  obtain ⟨κ₀, e₀, hl₀⟩ : ∃ κ₀ e₀, IsHCParam κ₀ e₀ l :=
    exists_isHCParam_of_hasGap fun w ↦ by simpa using (hl.hasGap w 0).neg
  have h_weights (w : InfinitePlace E) (q : ℕ) (hq : q < card n) :=
    add_diagramWeight_mem_Icc_of_interlace hn hl' hl₀ h_interlace w hq
  have h_boxes : boxes κ₀ (card n) ≤ boxes κ (card n') := boxes_le_boxes_of_interlace hn h_weights
  obtain ⟨γ, κ₁, h_split, h_strip, h_last⟩ := exists_add_eq_of_interlace (e := e) (e₀ := e₀)
    (κ := κ) (κ₀ := κ₀) card_pos (by simpa only [hn] using h_weights)
  obtain ⟨A, hA⟩ := exists_isDualPairing_of_isHCParam hl₀ hl
  -- `b` is equivariant for `diag (g, u)` up to a power of `u` (`hb_inv`), has bounded norm
  -- (`hb_norm`) and satisfies multiplicity one (`hb_uniq`).
  obtain ⟨b, hb_inv, hb_norm, hb_uniq⟩ :=
    exists_branching_matrix (fun _ ↦ σ) κ₀ 0 e e₀ h_split h_strip nofun h_last
  let N (τ : InfinitePlace E) : ℤ := diagramWeight (rankAt fun _ ↦ n') γ (τ, 0) + e τ
  refine ⟨A * b, ⟨N, ?_, fun τ ↦ ?_⟩, fun M hM v' v ↦ ?_, fun g ↦ ?_⟩
  · -- `b` turns `diag (g, u)` into `g` and a power of `u`; then `A` is invariant under `g`.
    intro S R _ _ _ _ f g u v' v
    have h_block : b.map (↑) *ᵥ weylRep κ e (fun τ ↦ (U.block σ (g, u)).val.map (f τ)) *ᵥ v =
        (∏ τ, (u.val.map (f τ)).det ^ N τ : Rˣ) •
          weylRep κ₀ e₀ (fun τ ↦ g.val.map (f τ)) *ᵥ b.map (↑) *ᵥ v := by
      rw [mulVec_mulVec v, hb_inv R (fun τ ↦ g.val.map (f τ)) (fun τ ↦ (u.val.map (f τ)).det) _
        (by simp [← ext_iff, GL.blockScalar, reindex_equiv σ]), smul_mulVec, ← mulVec_mulVec]
    rw [map_intCast_mul_mulVec, map_intCast_mul_mulVec, h_block, mulVec_smul, dotProduct_smul,
      hA.invariant, Units.smul_def, smul_eq_mul]
  · -- The first row of `γ` is at most the first row of `κ`, which is one term of `boxes`.
    have h_row : diagramWeight (rankAt fun _ ↦ n') γ (τ, 0) ≤
        diagramWeight (rankAt fun _ ↦ n') κ (τ, 0) := by
      simp only [diagramWeight_apply, ← h_split]
      exact sum_le_sum fun q _ ↦ Nat.le_add_right (γ τ q) (κ₁ τ q)
    have h_term : diagramWeight (rankAt fun _ ↦ n') κ (τ, 0) ≤ boxes κ (card n') := by
      grw [← FitsRanks.refl.sum_diagramWeight_eq_boxes,
        ← single_le_sum (by simp) (mem_univ (τ, ⟨0, by omega⟩))]
    grw [Int.natAbs_add_le, Int.natAbs_natCast, h_row, h_term]
  · calc ‖v' ⬝ᵥ (A * b).map (↑) *ᵥ v‖
        ≤ √(weylNormSq v' * weylNormSq (b.map (↑) *ᵥ v)) := by
          rw [map_intCast_mul_mulVec]
          exact norm_dotProduct_mulVec_le_of_isDualPairing hA v' _
      _ ≤ √(weylNormSq v' * (((M ^ M) ^ 3) ^ 2 * weylNormSq v)) := by
          grw [hb_norm M (by simpa using h_boxes.trans hM) v]
          simp
      _ = _ := by simp [field, sqrt_sq_eq_abs]
  · -- Right translation by `(g, 1)` only changes the linear form that is integrated. By
    -- multiplicity one, the integral over the real points is a multiple of the pairing.
    obtain ⟨c, hc⟩ := integral_algFormCoeff_blockEmb (stdSpace E n) (by simp) hb_uniq
      (gramForm (highestVector κ l') ∘ₗ conjWeylRep κ e g⁻¹) (highestVector κ₀ l)
    refine ⟨c, fun V _ η φ u K _ ↦ ?_⟩
    obtain rfl : V = stdSpace E n := IsStd.eq_stdSpace V
    -- By definition `G.blockEmb` is `G.sum` followed by `G.reindex`; its finite part is `U.block`.
    simpa [algFormCoeff, map_intCast_mul_mulVec] using!
      hc φ (ofAlgForm (-l) 1 η) u _ K (isAutomorphic_algFormCoeff η) (hA.ofAlgForm_eq_bilin 1 η)

omit [CMType E] in
/-- Let the doubled parameters `l` and `l'` of definite groups (all signs `1`) of ranks `#n < #n'`
correspond under a theta lift with exponents `γ`, `γ'` (`ParamsCorrespond`). This includes that at
each place `w` the shifted entries `l' w j - 2 γ w + #n` are the shifted entries
`l w i - 2 γ' w + #n'` together with a block of `#n' - #n` numbers centred at `0`, and that the
sign of a common entry is determined by the signs of the spaces. Then
`γ' w ≤ l w i / 2 + #n / 2` for every entry of `l`, in integer division, since every shifted entry
of `l` exceeds `#n' - #n`. -/
lemma le_div_two_add_of_paramsCorrespond {γ γ' : InfinitePlace E → ℤ} {l : InfinitePlace E → n → ℤ}
    {l' : InfinitePlace E → n' → ℤ}
    (h_corr : ParamsCorrespond (n := n) (n' := n') γ γ' l l' 1 1)
    (h_lt : card n < card n') (w : InfinitePlace E) (i : n) :
    γ' w ≤ l w i / 2 + card n / 2 := by
  obtain ⟨r, h_eq, h_outside⟩ :=
    (isBlockRule_iff_isMatch.1 (h_corr w)).exists_row_of_le h_lt.le i
  have h_large : |(card n' : ℤ) - card n| < l w i - 2 * γ' w + card n' := by
    rw [h_eq] at h_outside
    simpa [shiftedEntry, toHCParam] using h_outside
  rw [abs_lt] at h_large
  omega

end New.Exchange

namespace New.Data

/-!
## The last path: weights, levels, kernels and the finite sum

On the last path all spaces are positive definite. Its two halves run through the nodes `(z, j, m)`,
`j ≤ m`, which are the spaces `Y^j_m` and `Ỹ^m_j`.
-/

section LastPathDefs

open Fintype Subgroup Exchange Matrix

variable {P : Parameters} (D : Data P) (z : Bool) (j : ℕ)

/-- The index type of the space at the node `(z, j, m)` of the last path, which is `Y^j_m` if
`z = false` and `Ỹ^m_j` if `z = true`. Here `D` is a choice of admissible data for the parameters
`P`, `m = D.m` is the number of lifts, and `GridIndex` indexes the coordinates at a node. -/
abbrev LastPathIndex : Type := D.GridIndex z j D.m

/-- Let `D` be admissible data, with `m = D.m` lifts and with `D.Φ` the infinite places of the CM
field `D.E`. Fix a half `z` of the last path, through the nodes `(z, i, m)`: the Hermitian spaces
`Y^i_m` for `z = false` and `Ỹ^m_i` for `z = true`. For the edge from `i` to `i + 1`, let
`gridWeight z i n` be the weight of its character at the end with index type `n`. Along this half
every new block of the parameter lies below all old entries. So there are column multiplicities
`κ` and exponents `e i` of the determinant with three properties.
* `IsLiftWeight`: the rank grows from `i` to `i + 1`, no column has height strictly between the two
  ranks, and `e i` is the weight at the upper end plus the number of columns whose height is the
  rank at `i`.
* The weight at the lower end is `e (i + 1)`.
* For `i ≤ m` the weight `(κ, e i)` has the doubled Harish-Chandra parameter `-gridParam z 0 i m`
  of the forms moved along this half (the offset `0` selects the grids): conjugate forms on `Y^i_m`
  and forms on `Ỹ^m_i`. -/
theorem exists_isLiftWeight_isHCParam :
    ∃ (κ : D.Φ → ℕ → ℕ) (e : ℕ → D.Φ → ℤ),
      (∀ i : ℕ, IsLiftWeight (D.LastPathIndex z i) (D.LastPathIndex z (i + 1)) κ
        (D.gridWeight z i (D.LastPathIndex z (i + 1))) (e i)) ∧
      (∀ i : ℕ, D.gridWeight z i (D.LastPathIndex z i) = e (i + 1)) ∧
      ∀ i ≤ D.m, IsHCParam κ (e i) (-D.gridParam z 0 i D.m) := by
  -- Choose `κ` to fit the parameter at `j = 0`, with `D.gap - D.t - z` columns of each height
  -- `card (ι j)`, `j ≥ 1`, and no other columns higher than `card (ι 0)`. The parameters at larger
  -- `j` follow by induction: across an edge where the weight lifts, parameters correspond exactly
  -- when the second is that of the new weight.
  let ι : ℕ → Type := D.LastPathIndex z
  have h_edge (j : ℕ) (hj : j + 1 ≤ D.m) :
      ParamsCorrespond (D.gridWeight z j (ι j)) (D.gridWeight z j (ι (j + 1)))
        (-D.gridParam z 0 j D.m) (-D.gridParam z 0 (j + 1) D.m) 1 1 := by
    simpa [gridSigns_eq_one] using D.paramsCorrespond_grid_succ_left z j D.m hj le_rfl
  have h_mono : StrictMono fun j ↦ card (ι j) :=
    strictMono_nat_of_lt_succ (by simp [ι, card_gridIndex, D.t_odd.pos])
  have hm : 1 ≤ D.m := D.nat_le_of_hasLogBound
  let κ₁ : ℕ → ℕ := (Set.range fun j ↦ card (ι j)).indicator fun _ ↦ D.gap - D.t - z.toNat
  obtain ⟨κ, h_param, h_above⟩ :
      ∃ κ : D.Φ → ℕ → ℕ,
        IsHCParam κ (fun w ↦ D.gridWeight z 0 (ι 1) w + κ w (card (ι 0)))
          (-D.gridParam z 0 0 D.m) ∧
        ∀ w : D.Φ, ∀ k > card (ι 0), κ w k = κ₁ k :=
    exists_isHCParam_of_le (fun _ ↦ κ₁) (fun w ↦ (D.hasGap_gridParam w z 0 0 D.m).neg)
      (le_div_two_add_of_paramsCorrespond (h_edge 0 hm) (h_mono one_pos))
  let e (j : ℕ) (τ : D.Φ) : ℤ := D.gridWeight z j (ι (j + 1)) τ + κ τ (card (ι j))
  have h_up (j : ℕ) :
      IsLiftWeight (ι j) (ι (j + 1)) κ (D.gridWeight z j (ι (j + 1))) (e j) := by
    refine ⟨fun τ ↦ ⟨(h_mono j.lt_add_one).le, fun k hk ↦ ?_⟩, h_mono j.lt_add_one, rfl⟩
    obtain ⟨h_lower, h_upper⟩ := Finset.mem_Ioo.1 hk
    have h_not_rank (i : ℕ) : card (ι i) ≠ k :=
      h_mono.monotone.ne_of_lt_of_lt_nat j h_lower h_upper i
    rw [h_above τ k ((h_mono.monotone j.zero_le).trans_lt h_lower)]
    simp [κ₁, h_not_rank]
  have h_next (j : ℕ) : D.gridWeight z j (ι j) = e (j + 1) := by
    ext τ
    have h_columns : κ τ (card (ι (j + 1))) = D.gap - D.t - z.toNat := by
      simp [h_above τ _ (h_mono j.succ_pos), κ₁]
    simp only [e, h_columns]
    -- `D.liftWeight` grows by `D.gap` from `j + 1` to `j + 2`, and half the rank by `D.t + z` in
    -- two steps.
    simp only [gridWeight, card_gridIndex, ι]
    cases z <;> grind
  refine ⟨κ, e, h_up, h_next, fun j hj ↦ ?_⟩
  induction j with
  | zero => exact h_param
  | succ j ih =>
    rw [← h_next j]
    exact ((ih (by lia)).paramsCorrespond_iff (h_up j)).1 (h_edge j hj)

/-- The column multiplicities of the weights along the half `z` of the last path. -/
def lastPathColumns : D.Φ → ℕ → ℕ := (D.exists_isLiftWeight_isHCParam z).choose

/-- The exponents of the determinant in the weights along the half `z` of the last path. -/
def lastPathDetExp : ℕ → D.Φ → ℤ := (D.exists_isLiftWeight_isHCParam z).choose_spec.choose

/-- The weight at the node `(z, j, m)` goes up to the rank of the node `(z, j + 1, m)`, along the
weight at the upper end of the character of the edge between them. -/
lemma isLiftWeight_lastPathColumns :
    IsLiftWeight (D.LastPathIndex z j) (D.LastPathIndex z (j + 1)) (D.lastPathColumns z)
      (D.gridWeight z j (D.LastPathIndex z (j + 1))) (D.lastPathDetExp z j) := by
  obtain ⟨h_lift, -, -⟩ := (D.exists_isLiftWeight_isHCParam z).choose_spec.choose_spec
  exact h_lift j

/-- The weight at the lower end of the character of the edge from `(z, j, m)` to `(z, j + 1, m)` is
the exponent of the determinant at `(z, j + 1, m)`. -/
lemma gridWeight_eq_lastPathDetExp :
    D.gridWeight z j (D.LastPathIndex z j) = D.lastPathDetExp z (j + 1) := by
  obtain ⟨-, h_next, -⟩ := (D.exists_isLiftWeight_isHCParam z).choose_spec.choose_spec
  exact h_next j

/-- For `j ≤ m`, the weight at the node `(z, j, m)` has the doubled Harish-Chandra parameter
`-gridParam z 0 j m`. -/
lemma isHCParam_lastPathColumns {j : ℕ} (hj : j ≤ D.m) :
    IsHCParam (D.lastPathColumns z) (D.lastPathDetExp z j) (-D.gridParam z 0 j D.m) := by
  obtain ⟨-, -, h_param⟩ := (D.exists_isLiftWeight_isHCParam z).choose_spec.choose_spec
  exact h_param j hj

/-- The space of values of the algebraic forms at the node `(z, j, m)`. -/
abbrev LastPathVector : Type := WeylIndex (D.LastPathIndex z j) (D.lastPathColumns z) → ℂ

/-- Algebraic forms at the node `(z, j, m)`, of the weight given by `lastPathColumns` and
`lastPathDetExp`. -/
abbrev LastPathForm : Type := AlgForm (D.LastPathIndex z j) (D.lastPathColumns z)
  (D.lastPathDetExp z j)

/-- Finite data for the theta lift along the edge from `(z, j, m)` to `(z, j + 1, m)`. In the space
of data on the matrices (`hom`) between the standard spaces of the two ranks, this is the span
(`finitePart`) of the translates of the vacuum under the finite Heisenberg operators. -/
abbrev LastPathFiniteDatum : Type :=
  ((stdSpace D.E (D.LastPathIndex z j)).hom (stdSpace D.E (D.LastPathIndex z (j + 1)))).finitePart

/-- An integer matrix, chosen from `exists_isBranchingPairing`, that is a branching pairing between
the weight of the conjugate forms on `Y^m_m` (the node `(false, m, m)`) and the weight of the forms
on `Ỹ^m_m` (the node `(true, m, m)`). Its properties are stated in
`isBranchingPairing_lastPathBranching`. -/
def lastPathBranching : Matrix (WeylIndex (D.LastPathIndex false D.m) (D.lastPathColumns false))
    (WeylIndex (D.LastPathIndex true D.m) (D.lastPathColumns true)) ℤ :=
  (exists_isBranchingPairing (D.sumElim_gridSigns_comp_gridDiagEquiv_symm le_rfl)
    (D.gridSigns_eq_one le_rfl)
    (D.isHCParam_lastPathColumns true le_rfl) (D.isHCParam_lastPathColumns false le_rfl)
    D.gridParam_interlace).choose

/-- The matrix `lastPathBranching` is a branching pairing for the weights and parameters at the
nodes `(true, m, m)` and `(false, m, m)`. -/
lemma isBranchingPairing_lastPathBranching :
    IsBranchingPairing (D.sumElim_gridSigns_comp_gridDiagEquiv_symm le_rfl)
      (D.lastPathDetExp true D.m)
      (D.lastPathDetExp false D.m)
      (D.gridParam false 0 D.m D.m) (-D.gridParam true 0 D.m D.m) D.lastPathBranching :=
  (exists_isBranchingPairing (D.sumElim_gridSigns_comp_gridDiagEquiv_symm le_rfl)
    (D.gridSigns_eq_one le_rfl)
    (D.isHCParam_lastPathColumns true le_rfl) (D.isHCParam_lastPathColumns false le_rfl)
    D.gridParam_interlace).choose_spec

/-- The bilinear pairing `(v', v) ↦ v' ⬝ᵥ B *ᵥ v` of the matrix `B = D.lastPathBranching`. -/
abbrev lastPathPairing : D.LastPathVector false D.m →ₗ[ℂ] D.LastPathVector true D.m →ₗ[ℂ] ℂ :=
  (dotProductBilin ℂ ℂ).compl₂ (D.lastPathBranching.map (↑)).mulVecLin

/-- Let `D` be admissible data with `m = D.m` lifts and infinite places `D.Φ`. The weights on
`Y^m_m` (`false`) and `Ỹ^m_m` (`true`) have column multiplicities `lastPathColumns` and exponents of
the determinant `lastPathDetExp`; the integer matrix `B = lastPathBranching` pairs their Weyl
modules by `v' ⬝ᵥ B *ᵥ v`. There are integers `N τ` with two properties. Let `f τ : S →+* R` be
homomorphisms, one for each place `τ`, from a commutative star ring to a field of characteristic
zero, and let unitary matrices over `S` act through them (`weylRep`). Moving `v'` by `g` and `v` by
`diag (g, u)` multiplies the pairing by `∏ τ, det (f τ u) ^ N τ`. Also `|N τ|` is at most the number
of boxes of the weight on `Ỹ^m_m` plus the absolute value of its exponent of the determinant at
`τ`. -/
lemma exists_lastPathBranching_equivariant :
    ∃ N : D.Φ → ℤ,
      (∀ (S R : Type) [CommRing S] [StarRing S] [Field R] [CharZero R] (f : D.Φ → S →+* R)
          (g : U (1 : Matrix (D.LastPathIndex false D.m) (D.LastPathIndex false D.m) S))
          (u : U (1 : Matrix Unit Unit S))
          (v' : WeylIndex (D.LastPathIndex false D.m) (D.lastPathColumns false) → R)
          (v : WeylIndex (D.LastPathIndex true D.m) (D.lastPathColumns true) → R),
        weylRep (D.lastPathColumns false) (D.lastPathDetExp false D.m)
          (fun τ : D.Φ ↦ g.val.map (f τ)) *ᵥ
            v' ⬝ᵥ
            D.lastPathBranching.map (↑) *ᵥ weylRep (D.lastPathColumns true)
              (D.lastPathDetExp true D.m)
              (fun τ : D.Φ ↦ (U.block (D.gridDiagEquiv D.m) (g, u)).val.map (f τ)) *ᵥ v =
          (∏ τ : D.Φ, (u.val.map (f τ)).det ^ N τ : Rˣ) * v' ⬝ᵥ D.lastPathBranching.map (↑) *ᵥ v) ∧
      ∀ τ : D.Φ, (N τ).natAbs ≤ boxes (D.lastPathColumns true) (card (D.LastPathIndex true D.m)) +
        (D.lastPathDetExp true D.m τ).natAbs :=
  D.isBranchingPairing_lastPathBranching.exists_equivariant

/-- If `M` bounds the number of boxes of the weight at `(true, m, m)`, then
`‖v' ⬝ᵥ lastPathBranching *ᵥ v‖` is at most `(M ^ M) ^ 3 * √(weylNormSq v') * √(weylNormSq v)`, i.e.
`(M ^ M) ^ 3` times the product of the Gram norms of `v'` and `v`. -/
lemma norm_dotProduct_lastPathBranching_mulVec_le {M : ℕ}
    (hM : boxes (D.lastPathColumns true) (card (D.LastPathIndex true D.m)) ≤ M)
    (v' : D.LastPathVector false D.m) (v : D.LastPathVector true D.m) :
    ‖v' ⬝ᵥ D.lastPathBranching.map (↑) *ᵥ v‖ ≤
      ((M ^ M) ^ 3 : ℕ) * √(weylNormSq v') * √(weylNormSq v) :=
  D.isBranchingPairing_lastPathBranching.norm_le M hM v' v

/-- The period at `(m, m)`. For a real point `g` of `Ỹ^m_m` there is a constant `c` with the
following property. Read algebraic forms `η`, `φ` as functions on the adelic groups by `ofAlgForm`.
The integral of `η(x) φ(diag (x, u) g)` over the adelic quotient of a standard space `V` of the rank
of `Y^m_m` is `c` over the index of the level `K` times the integral (`classIntegral`) of the
branching pairing of `η(h)` and `φ(diag (h, u))` over the finite points `h` modulo the rational
points. -/
lemma exists_integral_eq_lastPathPairing (g : GInf D.E (D.gridSigns true 0 D.m D.m)) :
    ∃ c : ℂ,
      ∀ (V : Space D.E (D.LastPathIndex false D.m) (D.gridSigns false 0 D.m D.m)) [V.IsStd]
        (η : D.LastPathForm false D.m) (φ : D.LastPathForm true D.m) (u : Gf D.E Unit)
        (K : Subgroup (Gf D.E (D.LastPathIndex false D.m))) [IsLevel K],
      ∫ x : New.G D.E (D.gridSigns false 0 D.m D.m),
        ofAlgForm (-D.gridParam false 0 D.m D.m) (D.gridSigns false 0 D.m D.m) η x *
          ofAlgForm (-D.gridParam true 0 D.m D.m) (D.gridSigns true 0 D.m D.m) φ
            (G.reindex (D.gridDiagEquiv D.m) (D.sumElim_gridSigns_comp_gridDiagEquiv_symm le_rfl)
              (G.sum (x, 1, u)) *
              (g, 1)) ∂V.quotMeasure =
        c / stdLevelIndex K *
          classIntegral stdRatPoints K fun h : Gf D.E (D.LastPathIndex false D.m) ↦
            D.lastPathPairing (η.val h) (φ.val (U.block (D.gridDiagEquiv D.m) (h, u))) :=
  D.isBranchingPairing_lastPathBranching.exists_integral_eq g

/-- The spaces of the last path are standard positive definite spaces. -/
instance isStd_gridSpace_last {D : Data P} {z : Bool} {i : ℕ} :
    (D.gridSpace 0 z i D.m).IsStd := by
  -- The space is `Y_m` at `z = false`, `i = 0`, and diagonal with all signs `1` at the other nodes.
  -- Writing `D.m` as a successor decides the case distinction in `gridSpace`.
  have hm : D.m = 2 * D.ϱ + 2 := D.m_eq_two_mul_varrho_add_two
  obtain _ | i := i
  · cases z
    · exact D.isStd_spaceY_last
    · rw [hm]; exact isStd_signedSpace (D.gridSigns_eq_one hm.le)
  · rw [hm]; cases z <;> exact isStd_signedSpace (D.gridSigns_eq_one hm.le)

/-- Forms at the outer end `(z, 0, m)` of a half of the last path, as algebraic forms. -/
def lastPathToAlgForm : D.GridForm z 0 D.m ≃ₗ[ℂ] D.LastPathForm z 0 :=
  (D.gridSpace 0 z 0 D.m).toAlgForm (D.isHCParam_lastPathColumns z zero_le)

variable {D}

/-- The rank at the node `(z, j, m)` with `j ≤ m` is at most `2 n_m`, twice the rank `n_m = D.n m`
in the sequence `n_j = k + j (t + 1)` of the data. -/
lemma card_lastPathIndex_le (z : Bool) {j : ℕ} (hj : j ≤ D.m) :
    card (D.LastPathIndex z j) ≤ 2 * D.n D.m :=
  D.card_gridIndex_le hj le_rfl

/-- At the node `(z, j, m)` with `j ≤ m` the exponents of the determinant are at most `⌈20 b⌉` in
absolute value, where `b = D.b` is the large weight of the data. -/
lemma natAbs_lastPathDetExp_le (z : Bool) {j : ℕ} (hj : j ≤ D.m) (τ : D.Φ) :
    (D.lastPathDetExp z j τ).natAbs ≤ ⌈20 * D.b⌉₊ :=
  natAbs_le_of_isHCParam (D.isHCParam_lastPathColumns z hj)
    (by simpa using D.abs_gridParam_le τ hj le_rfl)

/-- At the node `(z, j, m)` with `j ≤ m`, the number of boxes of the weight `D.lastPathColumns z` is
at most `b r ^ 4`, where `b` is `D.natB` and `r` is `D.r`. -/
lemma boxes_lastPathColumns_le_natB_mul (z : Bool) {j : ℕ} (hj : j ≤ D.m) :
    boxes (D.lastPathColumns z) (card (D.LastPathIndex z j)) ≤ D.natB * D.r ^ 4 := by
  have h_entry (τ : D.Φ) (i : D.LastPathIndex z j) :
      |(-D.gridParam z 0 j D.m) τ i| ≤ (⌈20 * D.b⌉₊ : ℕ) := by
    simpa using D.abs_gridParam_le τ hj le_rfl i
  calc boxes (D.lastPathColumns z) (card (D.LastPathIndex z j))
      ≤ card D.Φ * card (D.LastPathIndex z j) * ⌈20 * D.b⌉₊ :=
        boxes_le_card_mul_of_isHCParam (D.isHCParam_lastPathColumns z hj) h_entry
    _ ≤ card D.Φ * (2 * D.n D.m) * ⌈20 * D.b⌉₊ := by grw [card_lastPathIndex_le z hj]
    -- This compares orders of magnitude of the constants of `D`.
    _ ≤ D.natB * D.r ^ 4 := by simpa using D.nat_le_of_hasLogBound

section Twist

variable (ϑ : D.MFoldTwist) (z : Bool) (j : ℕ)

/-- The level at the node `(z, j, m)` of the last path, inside `Gf D.E (D.LastPathIndex z j)`: the
integral points whose reduction modulo `𝔪 = gridModulus ϑ` lies in `nodeLevel`, which is trivial on
`Y_m` (the node `(false, 0, m)`) and elsewhere the kernel of the reduction modulo the part `𝔟` of
`𝔪` that does not depend on the twist `ϑ`. So it is `J(𝔪)` on `Y_m` and `J(𝔟)` on the other spaces,
where `J(𝔞)` consists of the integral points that reduce to `1` modulo `𝔞`. -/
def lastPathLevel : Subgroup (Gf D.E (D.LastPathIndex z j)) :=
  (gridModulus ϑ).levelOfSubgroup (n := D.LastPathIndex z j) (nodeLevel ϑ (z, j, D.m))
  deriving IsLevel

/-- For every twist `ϑ`, the level `lastPathLevel ϑ z j` at the node `(z, j, m)` of the last path
lies in the principal level `J(𝔟)`, the integral points that reduce to `1` modulo `𝔟`. Here `𝔟` is
generated by `D.gridLevelGen = ϖ ^ D.natB`, with `ϖ = D.piM`. It is the part of the modulus
`𝔪 = 𝔟 Q` of `ϑ` that does not depend on the places `Q` of `ϑ`. -/
theorem lastPathLevel_le_principalLevel (ϑ : D.MFoldTwist) (z : Bool) (j : ℕ) :
    lastPathLevel ϑ z j ≤ principalLevel (D.LastPathIndex z j) D.gridLevelGen := by
  rintro _ ⟨k, hk, rfl⟩
  -- `nodeLevel` is trivial or the kernel of the reduction to the modulus of the trivial twist.
  have h_le : nodeLevel ϑ (z, j, D.m) ≤ (GeneralLinearGroup.map (reduceToTriangle ϑ true)).ker := by
    aesop (add simp nodeLevel)
  -- Reducing in two steps is reducing modulo the modulus of the trivial twist.
  have h_factor : GeneralLinearGroup.map (reduceToTriangle ϑ true)
      ((gridModulus ϑ).reductionGL k) = (gridModulus 1).reductionGL k :=
    Units.ext Modulus.factor_reductionGL
  exact (Modulus.mem_principalLevel_iff gridModulus_one_ideal k).2
    (h_factor.symm.trans (h_le hk))

/-- The character at the lower end of the edge from `(z, j, m)` to `(z, j + 1, m)` has as its weight
the exponent of the determinant at `(z, j + 1, m)`. Its tame part, the family of characters of the
residue fields that gives it on integral finite points, is `gridTamePart ϑ z j`. -/
lemma gridChar_hasWeight_lastPathDetExp :
    (gridChar ϑ z j (D.LastPathIndex z j)).HasWeight (D.lastPathDetExp z (j + 1))
      (gridTamePart ϑ z j) := by
  rw [← D.gridWeight_eq_lastPathDetExp z j]
  exact gridChar_hasWeight ϑ z j (D.LastPathIndex z j)

/-- The theta kernel of the edge from `(z, j, m)` to `(z, j + 1, m)`, for the characters `gridChar`
at the two ends and the level at `(z, j, m)`. The derivatives in the Taylor series of the theta
functions are scaled by the constant `jetScale` of the field `D.E = P.E D.towerExp`. -/
def lastPathKernel : Kernel (D.LastPathIndex z j) (D.LastPathIndex z (j + 1)) (D.lastPathColumns z)
  (D.lastPathDetExp z j)
    (D.lastPathDetExp z (j + 1)) (lastPathLevel ϑ z j) (D.LastPathFiniteDatum z j) :=
  thetaKernel (D.isLiftWeight_lastPathColumns z j) (1 * P.jetScale D.towerExp)
    (gridChar_hasWeight_lastPathDetExp ϑ z j) (gridChar_hasWeight ϑ z j (D.LastPathIndex z (j + 1)))
    (lastPathLevel ϑ z j)

/-- The point `diag (h, u ^ m)` of `Ỹ^m_m` for a finite point `h` of `Y^m_m`, where `u` is the
scalar `flipScalar` of the modulus `𝔪`, acting on the line. -/
def lastPathBlockPoint (h : Gf D.E (D.LastPathIndex false D.m)) :
    Gf D.E (D.LastPathIndex true D.m) :=
  U.block (D.gridDiagEquiv D.m) (h, (gridModulus ϑ).flipScalar ^ D.m)

/-- The two forms have the levels at the outer ends of the last path: `J(𝔪)` for the conjugate form
`y false` on `Y_m` and `J(𝔟)` for the form `y true` on `Ỹ^m_0`. -/
abbrev FixedByOuterLevels (y : ∀ z : Bool, D.GridForm z 0 D.m) : Prop :=
  ∀ z : Bool, D.lastPathToAlgForm z (y z) ∈
    levelSpace (algFormRep (D.lastPathColumns z) (D.lastPathDetExp z 0)) (lastPathLevel ϑ z 0)

end Twist

variable {ϑ : D.MFoldTwist}

/-- The finite datum of an edge of the last path: the indicator of the matrix of the edge, on the
vacuum scaled by a power of `vacuumScale`. -/
def lastPathEdgeDatum (S : EdgeTuple ϑ) (z : Bool) (j : ℕ) : D.LastPathFiniteDatum z j :=
  P.vacuumScale D.towerExp ^ card (D.LastPathIndex z (j + 1) × D.LastPathIndex z j) •
    vacuumDatum (stdSpace D.E (D.LastPathIndex z j)) (stdSpace D.E (D.LastPathIndex z (j + 1)))
      (gridModulus ϑ) (Pi.single (S (rowEdge z j D.m)) 1)

/-- The algebraic form of `F` on the outer node `(z, 0, m)`, lifted along the first `j` edges of the
half `z` of the last path with the data that the tuple `S` gives. -/
abbrev lastPathChain (S : EdgeTuple ϑ) (z : Bool) (j : ℕ) (F : D.GridForm z 0 D.m) :
    D.LastPathForm z j :=
  chain (lastPathKernel ϑ z) (lastPathEdgeDatum S z) j (D.lastPathToAlgForm z F)

/-- The finite sum `Ξ` on the last path. An `EdgeTuple` is a matrix modulo `𝔪` for each pair of
nodes, and `tuplesOn` lists the tuples `S` that vanish off the edges of the last path. For each such
`S` the two chains of lifts of `y false` and `y true` are paired and integrated over the finite
points of `Y^m_m` modulo the rational points; `Ξ` is the sum of these integrals against `Ψ S`. -/
def lastPathPeriod (Ψ : EdgeTuple ϑ → ℂ) (y : ∀ z : Bool, D.GridForm z 0 D.m) : ℂ :=
  ∑ S ∈ tuplesOn ϑ (TwoGridPath.last D.m).edges, Ψ S *
    classIntegral stdRatPoints (lastPathLevel ϑ false D.m)
      fun h : Gf D.E (D.LastPathIndex false D.m) ↦
        D.lastPathPairing ((lastPathChain S false D.m (y false)).val h)
          ((lastPathChain S true D.m (y true)).val (lastPathBlockPoint ϑ h))

end LastPathDefs

/-!
## The last path: the sum over classes

The invariance of a path datum makes the integrand of the sum `Ξ = lastPathPeriod` invariant under
the levels, in each variable. These levels are sufficiently small, so `Ξ` is a plain sum over tuples
of classes.
-/

section LastPathPairingTerms

open Finset Subgroup Pointwise Exchange Rows Matrix TensorChain

variable {P : Parameters} {D : Data P} {ϑ : D.MFoldTwist} {N : ℕ} {Ψ : EdgeTuple ϑ → ℂ}

/-- The edges of the last path are those of the row `m` in both grids. -/
lemma edges_last : (TwoGridPath.last D.m).edges =
    (range D.m).image (fun j : ℕ ↦ rowEdge false j D.m) ∪
      (range D.m).image fun j : ℕ ↦ rowEdge true j D.m := by
  have h_row (z : Bool) (a : ℕ) :
      (GridPath.row D.m a).edges z = (range a).image fun j ↦ rowEdge z j D.m := by
    induction a with
    | zero => rfl
    | succ a ih => rw [GridPath.row, GridPath.edges, ih, range_add_one, image_insert]
  rw [← h_row, ← h_row]
  rfl

/-- For a family `g` of invertible matrices at the nodes, the product `edgeCharProd g` of the
characters of the edges of the last path splits into one factor for each of these edges. -/
lemma edgeCharProd_last (g : NodeFamily ϑ) : edgeCharProd g (TwoGridPath.last D.m).edges =
    ∏ z : Bool, ∏ j ∈ range D.m, edgeCharProd g {rowEdge z j D.m} := by
  have h_inj (z : Bool) : Set.InjOn (fun j ↦ rowEdge z j D.m) (range D.m) := by simp [Set.InjOn]
  simp only [edgeCharProd, prod_singleton]
  rw [edges_last, prod_union (by simp [disjoint_left]), prod_image (h_inj false),
    prod_image (h_inj true), Fintype.prod_bool, mul_comm]

/-- Let `g` be a family of invertible matrices modulo `gridModulus ϑ` at the nodes. Let the integral
points `u`, `u'` reduce modulo `gridModulus ϑ` to the values of `g` at the ends `(z, j, m)`,
`(z, j + 1, m)` of the edge `rowEdge z j D.m` of the last path. For a tuple `S` of matrices on the
edges, `tupleAction g S` has the matrix `(g q)⁻¹ * S (p, q) * g p` on the edge from `p` to `q`. Then
the action `ω` of `(u, u')` for `lastPathKernel ϑ z j` takes the datum `lastPathEdgeDatum` of
`tupleAction g S` on this edge to that of `S`, times `edgeCharProd g`, the value of the character of
the edge. -/
lemma lastPathKernel_omega_lastPathEdgeDatum {g : NodeFamily ϑ} {z : Bool} {j : ℕ}
    {u : stdLevel D.E (D.LastPathIndex z j)} {u' : stdLevel D.E (D.LastPathIndex z (j + 1))}
    (hu : g (z, j, D.m) = (gridModulus ϑ).reductionGL u)
    (hu' : g (z, j + 1, D.m) = (gridModulus ϑ).reductionGL u') (S : EdgeTuple ϑ) :
    (lastPathKernel ϑ z j).ω (u.val, u'.val) (lastPathEdgeDatum (tupleAction g S) z j) =
      edgeCharProd g {rowEdge z j D.m} • lastPathEdgeDatum S z j := by
  have h_char : edgeCharProd g {rowEdge z j D.m} =
      pairChar (s := 1) (s' := 1) (gridChar ϑ z j (D.LastPathIndex z j))
        (gridChar ϑ z j (D.LastPathIndex z (j + 1))) ((1, u.1), 1, u'.1) := by
    simp [gridChar_det, edgeCharProd, edgeChar, hu, hu', div_eq_mul_inv]
  rw [h_char, lastPathEdgeDatum, lastPathEdgeDatum, map_smul, smul_comm]
  congr 1
  -- What remains is the action of `pairWeil` on the indicator of the matrix of the edge.
  refine Subtype.ext ?_
  simp_rw [vacuumDatum, ← modDatum_vacVector]
  exact pairWeil_modDatum_single _ _ (by simp [tupleAction, hu, hu'])

/-- Let `Ψ` be a path datum: a function of the matrices on the edges, fixed by admissible families
up to the characters of the edges, with sums of roots of unity as values. Let `a` be a family of
elements of the levels along the last path with `a true m = diag (a false m, 1)`. Then moving the
data of all lifts by `a` does not change the sum against `Ψ` of the pairings of linear images `β`,
`β'` of the two tensors `pure` of data. -/
lemma IsPathDatum.sum_lastPathPairing_omega_invariant
    (hΨ : IsPathDatum N (TwoGridPath.last D.m).edges Ψ)
    (a : ∀ (z : Bool) (j : ℕ), lastPathLevel ϑ z j)
    (ha : (a true D.m).val = U.block (D.gridDiagEquiv D.m) ((a false D.m).val, 1))
    (β : TensorChain (D.LastPathFiniteDatum false) D.m →ₗ[ℂ] D.LastPathVector false D.m)
    (β' : TensorChain (D.LastPathFiniteDatum true) D.m →ₗ[ℂ] D.LastPathVector true D.m) :
    ∑ S ∈ tuplesOn ϑ (TwoGridPath.last D.m).edges, Ψ S * D.lastPathPairing
        (β (pure (fun j : ℕ ↦ (lastPathKernel ϑ false j).ω ((a false j).val, (a false (j + 1)).val)
          (lastPathEdgeDatum S false j)) D.m))
        (β' (pure (fun j : ℕ ↦ (lastPathKernel ϑ true j).ω ((a true j).val, (a true (j + 1)).val)
          (lastPathEdgeDatum S true j)) D.m)) =
      ∑ S ∈ tuplesOn ϑ (TwoGridPath.last D.m).edges, Ψ S * D.lastPathPairing
        (β (pure (lastPathEdgeDatum S false) D.m)) (β' (pure (lastPathEdgeDatum S true) D.m)) := by
  -- The residues of `a` form an admissible family, and `Ψ` is fixed by such families up to the
  -- characters of the edges.
  have h_mem (z : Bool) (j : ℕ) : ∃ u : stdLevel D.E (D.LastPathIndex z j),
      (gridModulus ϑ).reductionGL u ∈ nodeLevel ϑ (z, j, D.m) ∧ u.1 = (a z j).1 := (a z j).2
  choose u hu h_val using h_mem
  simp_rw [← h_val] at *
  -- The family on the grids: `u` modulo `𝔪` at the nodes of the last path, `1` elsewhere.
  let g : NodeFamily ϑ := fun ⟨z, j, b⟩ ↦
    Pi.mulSingle (M := fun b : ℕ ↦ GL (D.GridIndex z j b) _) D.m
      ((gridModulus ϑ).reductionGL (u z j)) b
  have hg (z : Bool) (j : ℕ) : g (z, j, D.m) = (gridModulus ϑ).reductionGL (u z j) :=
    Pi.mulSingle_eq_same ..
  have h_adm : IsAdmissibleFamily g := by
    refine ⟨fun z ↦ by simpa [hg] using hu z 0, fun j ↦ ?_⟩
    obtain rfl | hj := eq_or_ne D.m j
    · -- At `(m, m)` this is `ha`, reduced modulo `𝔪`.
      obtain ⟨h_int, h_red⟩ :=
        map_block_eq_blockGL (gridModulus ϑ).reduction (D.gridDiagEquiv D.m) (u false D.m) 1
      rw [hg, hg, (Subtype.ext ha : u true D.m = ⟨_, h_int⟩)]
      simpa using! h_red
    · simp [g, hj, Prod.mk_one_one]
  -- Acting by `u` on the data of `tupleAction g S` gives those of `S`, times the characters.
  have h_pure (z : Bool) (S : EdgeTuple ϑ) :
      pure (fun j : ℕ ↦ (lastPathKernel ϑ z j).ω (u z j, (u z (j + 1)).1)
          (lastPathEdgeDatum (tupleAction g S) z j)) D.m =
        (∏ j ∈ range D.m, edgeCharProd g {rowEdge z j D.m}) • pure (lastPathEdgeDatum S z) D.m :=
    pure_smul (lastPathEdgeDatum S z) _ D.m fun j _ ↦
      lastPathKernel_omega_lastPathEdgeDatum (hg z j) (hg z (j + 1)) S
  refine mul_left_cancel₀
    (isOfFinOrder_edgeCharProd g (TwoGridPath.last D.m).edges).isUnit.ne_zero ?_
  rw [← hΨ.sum_tupleAction h_adm, mul_sum]
  refine sum_congr rfl fun S _ ↦ ?_
  simp only [h_pure, edgeCharProd_last, Fintype.prod_bool, map_smul,
    LinearMap.smul_apply, smul_eq_mul]
  ring

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum Finset.prod Finset.univ in
/-- Let `S` be a tuple of matrices on the edges, which gives the data of the lifts, and let
`y false`, `y true` be forms at the outer ends of the last path. Lift both forms `m = D.m` times
along the last path (`lastPathChain`), to `Y^m_m` and `Ỹ^m_m`. Consider the function that sends a
finite point `h` of `Y^m_m` to the branching pairing `lastPathPairing` of the value of the first
lift at `h` and the value of the second lift at `lastPathBlockPoint ϑ h`. It lies in
`smoothInvariants stdRatPoints`: it is smooth and left invariant under the rational points. -/
lemma lastPathPairing_lastPathChain_mem_smoothInvariants (S : EdgeTuple ϑ)
    (y : ∀ z : Bool, D.GridForm z 0 D.m) :
    (fun h : Gf D.E (D.LastPathIndex false D.m) ↦
      D.lastPathPairing ((lastPathChain S false D.m (y false)).val h)
        ((lastPathChain S true D.m (y true)).val (lastPathBlockPoint ϑ h))) ∈
      smoothInvariants stdRatPoints := by
  -- Each lift is an algebraic form: it has an open stabiliser and is automorphic.
  obtain ⟨h_open, h_aut⟩ := (lastPathChain S false D.m (y false)).2
  obtain ⟨h_open', h_aut'⟩ := (lastPathChain S true D.m (y true)).2
  constructor
  · -- Both lifts are automorphic, and the pairing is invariant under `diag(γ, 1)`.
    rintro _ ⟨γ, rfl⟩ g
    obtain ⟨K, h_equiv, -⟩ := D.exists_lastPathBranching_equivariant
    have h_point : lastPathBlockPoint ϑ ((stdSpace D.E (D.LastPathIndex false D.m)).embFin γ * g) =
        (stdSpace D.E (D.LastPathIndex true D.m)).embFin (U.block (D.gridDiagEquiv D.m) (γ, 1)) *
          lastPathBlockPoint ϑ g := by
      simp [lastPathBlockPoint, ← map_mul, ← block_embFin]
    have h_false := (h_aut γ g).trans (stdSpace_weightRep_apply ..)
    have h_true := (h_aut' (U.block (D.gridDiagEquiv D.m) (γ, 1)) (lastPathBlockPoint ϑ g)).trans
      (stdSpace_weightRep_apply ..)
    dsimp only
    rw [h_point, h_false, h_true]
    exact (h_equiv D.E ℂ _ γ 1 _ _).trans (by simp)
  · -- The stabiliser contains the open intersection of that of the first lift with the
    -- preimage of that of the second under `h ↦ diag(h, 1)`.
    let incl : Gf D.E (D.LastPathIndex false D.m) →* Gf D.E (D.LastPathIndex true D.m) :=
      (U.block (D.gridDiagEquiv D.m)).comp (.inl _ _)
    have h_cont : Continuous incl := by
      change Continuous fun h : Gf D.E (D.LastPathIndex false D.m) ↦
        (G.blockEmb (s := 1) Sum.elim_one_one.symm ⟨⟨1, h⟩, 1⟩).2
      fun_prop
    refine Subgroup.isOpen_mono (H₁ := rightStabilizer (lastPathChain S false D.m (y false)).1 ⊓
      comap incl (rightStabilizer (lastPathChain S true D.m (y true)).1)) ?_
      (.and h_open (h_open'.preimage h_cont))
    rintro a ⟨ha_false, ha_true⟩ g
    have h_true : (lastPathChain S true D.m (y true)).1 (lastPathBlockPoint ϑ (g * a)) =
        (lastPathChain S true D.m (y true)).1 (lastPathBlockPoint ϑ g) := by
      simpa [incl, lastPathBlockPoint, ← map_mul] using ha_true (lastPathBlockPoint ϑ g)
    simp [ha_false g, h_true]

/-- Let `Ψ` be a path datum (`IsPathDatum N`) for the edges of the last path `TwoGridPath.last D.m`.
It is a function of tuples `S` of matrices modulo `𝔪 = gridModulus ϑ` on those edges. Let the forms
`y false`, `y true` have the levels at the outer ends of the path. For each `S`, lift both forms
`m = D.m` times with the data given by `S` (`lastPathChain`). Pair (`D.lastPathPairing`) the values
of the lifts at a finite point `g` of `Y^m_m` and at the block point `lastPathBlockPoint ϑ g` of
`Ỹ^m_m`. The sum over `S` of `Ψ S` times this pairing does not change if `g` is replaced by `g * u`.
Here `u` is an integral point whose reduction modulo `𝔪` lies in the level
`nodeLevel ϑ (false, D.m, D.m)` at `Y^m_m`. -/
lemma IsPathDatum.sum_lastPathPairing_mul_level (hΨ : IsPathDatum N (TwoGridPath.last D.m).edges Ψ)
    {y : ∀ z : Bool, D.GridForm z 0 D.m} (hy : FixedByOuterLevels ϑ y)
    {u : stdLevel D.E (D.LastPathIndex false D.m)}
    (hu : (gridModulus ϑ).reductionGL u ∈ nodeLevel ϑ (false, D.m, D.m))
    (g : Gf D.E (D.LastPathIndex false D.m)) :
    ∑ S ∈ tuplesOn ϑ (TwoGridPath.last D.m).edges, Ψ S *
        D.lastPathPairing ((lastPathChain S false D.m (y false)).val (g * u.val))
          ((lastPathChain S true D.m (y true)).val (lastPathBlockPoint ϑ (g * u.val))) =
      ∑ S ∈ tuplesOn ϑ (TwoGridPath.last D.m).edges, Ψ S *
        D.lastPathPairing ((lastPathChain S false D.m (y false)).val g)
          ((lastPathChain S true D.m (y true)).val (lastPathBlockPoint ϑ g)) := by
  -- Act by `u` and `diag(u, 1)` at the node `(m, m)` of the two grids.
  obtain ⟨h_int, h_red⟩ :=
    map_block_eq_blockGL (gridModulus ϑ).reduction (D.gridDiagEquiv D.m) u 1
  have h_level : U.block (D.gridDiagEquiv D.m) (u.1, 1) ∈ lastPathLevel ϑ true D.m := by
    refine ⟨⟨_, h_int⟩, ?_, rfl⟩
    -- By `h_red` its residue is `diag(r, 1)`, where `r` is that of `u` and lies in the level.
    simp_all [Modulus.reductionGL, nodeLevel, m_eq_two_mul_varrho_add_two, Units.ext_iff,
      ← submatrix_map, fromBlocks_map]
  -- The family that is `u`, `diag(u, 1)` at `(m, m)` in the two grids and `1` elsewhere.
  let a : ∀ (z : Bool) (j : ℕ), lastPathLevel ϑ z j
    | false => Pi.mulSingle D.m ⟨u.1, u, hu, rfl⟩
    | true => Pi.mulSingle D.m ⟨U.block (D.gridDiagEquiv D.m) (u.1, 1), h_level⟩
  have ha : (a true D.m).1 = U.block (D.gridDiagEquiv D.m) ((a false D.m).1, 1) := by simp [a]
  -- The values of the two chains at `g` and at `lastPathBlockPoint ϑ g` are linear images of the
  -- tensors of their data.
  obtain ⟨β, hβ⟩ :=
    exists_linearMap_chain_eq_apply_pure (lastPathKernel ϑ false) D.m
      (D.lastPathToAlgForm false (y false)) g
  obtain ⟨β', hβ'⟩ :=
    exists_linearMap_chain_eq_apply_pure (lastPathKernel ϑ true) D.m
      (D.lastPathToAlgForm true (y true))
      (lastPathBlockPoint ϑ g)
  convert hΨ.sum_lastPathPairing_omega_invariant a ha β β' <;>
    simp [a, ← hβ, ← hβ', chain_equivariant, hy _, lastPathBlockPoint, ← map_mul]

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.univ in
/-- Let `Ψ` be a path datum whose values are sums of at most `N` roots of unity, and let the forms
`y` have the levels at the outer ends. Let `σ` be a homomorphism from `ℂ` to a normed field. Let
`IsReached z j g v` be a property of a vector `v` at a finite point `g` of the node `(z, j, m)`,
such as membership in a set that contains all vectors reached by the lifts: it holds at `j = 0` for
the values of the two forms and is preserved by the kernels. Suppose that `‖σ (M * a)‖ ≤ R`, for a
fixed number `M`, for each pairing `a` of vectors with this property at corresponding points `g` and
`lastPathBlockPoint g` of `Y^m_m` and `Ỹ^m_m`.

Then the sum `Ξ = lastPathPeriod Ψ y` over the last path is a sum of numbers with this bound. The
number of summands is `L` times the product of the numbers of classes (`StdClasses`) of the
`2 * m + 1` levels that occur, for some `L ≤ N * edgeMatrixCountBound ^ (2 * m)`. -/
theorem exists_lastPathPeriod_mem_smul_norm_le {ϑ : D.MFoldTwist} {N : ℕ} {Ψ : EdgeTuple ϑ → ℂ}
    (hΨ : IsPathDatum N (TwoGridPath.last D.m).edges Ψ)
    {y : ∀ z : Bool, D.GridForm z 0 D.m} (hy : FixedByOuterLevels ϑ y)
    (IsReached : ∀ (z : Bool) (j : ℕ), Gf D.E (D.LastPathIndex z j) → D.LastPathVector z j → Prop)
    {F : Type*} {M : ℂ} {R : ℝ} [NormedField F] (σ : ℂ →+* F)
    (h_step : ∀ (S : EdgeTuple ϑ) (z : Bool), ∀ j < D.m, ∀ (g : Gf D.E (D.LastPathIndex z j))
      (h : Gf D.E (D.LastPathIndex z (j + 1))) (v : D.LastPathVector z j), IsReached z j g v →
      IsReached z (j + 1) h ((lastPathKernel ϑ z j).jetMap
        ((lastPathKernel ϑ z j).ω (g, h) (lastPathEdgeDatum S z j)) v))
    (h_start : ∀ (z : Bool) (g : Gf D.E (D.LastPathIndex z 0)),
      IsReached z 0 g ((D.lastPathToAlgForm z (y z)).val g))
    (h_bound : ∀ {g : Gf D.E (D.LastPathIndex false D.m)} {v' : D.LastPathVector false D.m}
      {v : D.LastPathVector true D.m}, IsReached false D.m g v' →
      IsReached true D.m (lastPathBlockPoint ϑ g) v →
      ‖σ (M * D.lastPathPairing v' v)‖ ≤ R) :
    ∃ L ≤ N * edgeMatrixCountBound ϑ ^ (2 * D.m), lastPathPeriod Ψ y ∈
      (L * ∏ z : Bool, ∏ j ∈ range (D.m + (!z).toNat),
        Nat.card (StdClasses (lastPathLevel ϑ z j))) • {a : ℂ | ‖σ (M * a)‖ ≤ R} := by
  -- The sum against `Ψ` is invariant under the levels, so the last integral and both chains of
  -- lifts are plain sums over classes. Each term is a sum over the tuples `S` of pairings of
  -- reached vectors, with coefficients `Ψ S`.
  let W : Finset (EdgeTuple ϑ) := tuplesOn ϑ (TwoGridPath.last D.m).edges
  let A : Set ℂ := {a : ℂ | ‖σ (M * a)‖ ≤ R}
  let classes (z : Bool) : ℕ := ∏ j ∈ range D.m, Nat.card (StdClasses (lastPathLevel ϑ z j))
  -- For the half `z` and the tuple `S`: the tensor of the data of the lifts, and the lifted form.
  let data (z : Bool) (S : EdgeTuple ϑ) : TensorChain (D.LastPathFiniteDatum z) D.m :=
    pure (lastPathEdgeDatum S z) D.m
  let value (z : Bool) (S : EdgeTuple ϑ) :
      Gf D.E (D.LastPathIndex z D.m) → D.LastPathVector z D.m :=
    (lastPathChain S z D.m (y z)).val
  have h_free (z : Bool) (j : ℕ) (hj : j ≤ D.m) :
      ∀ g : Gf D.E (D.LastPathIndex z j), classAut stdRatPoints (lastPathLevel ϑ z j) g = ⊥ :=
    D.classAut_eq_bot_of_le_chosenLevel ((lastPathLevel_le_principalLevel ϑ z j).trans
      (D.principalLevel_le_chosenLevel piM_dvd_gridLevelGen)) (card_lastPathIndex_le z hj)
  -- As `Ψ S` is a sum of at most `N` roots of unity, each tuple gives `N` numbers in `A`.
  have h_tuples {g : Gf D.E (D.LastPathIndex false D.m)}
      {v' : EdgeTuple ϑ → D.LastPathVector false D.m} {v : EdgeTuple ϑ → D.LastPathVector true D.m}
      (hv' : ∀ S ∈ W, IsReached false D.m g (v' S))
      (hv : ∀ S ∈ W, IsReached true D.m (lastPathBlockPoint ϑ g) (v S)) :
      ∑ S ∈ W, Ψ S * D.lastPathPairing (v' S) (v S) ∈ #W • N • A := by
    rw [← sum_const]
    refine Set.finsetSum_mem_finsetSum _ _ _ fun S hS ↦ ?_
    have h_pair : ‖σ (M * D.lastPathPairing (v' S) (v S))‖ ≤ R := h_bound (hv' S hS) (hv S hS)
    have h_zero : 0 ∈ A := by simpa [A] using (norm_nonneg _).trans h_pair
    refine (hΨ.isSumOfRootsOfUnity S).mul_mem_nsmul h_zero fun c hc ↦ ?_
    have h_norm : ‖σ c‖ = 1 := (σ.isOfFinOrder hc).norm_eq_one
    rwa [Set.mem_ofPred_eq, mul_left_comm, map_mul, norm_mul, h_norm, one_mul]
  -- The chain in the grid of the `Ỹ` is a sum over classes.
  have h_sum_tilde_chain (g : Gf D.E (D.LastPathIndex false D.m))
      (β : TensorChain (D.LastPathFiniteDatum false) D.m →ₗ[ℂ] D.LastPathVector false D.m)
      (hβ : ∀ S ∈ W, IsReached false D.m g (β (data false S))) :
      ∑ S ∈ W, Ψ S * D.lastPathPairing (β (data false S)) (value true S (lastPathBlockPoint ϑ g)) ∈
        classes true • #W • N • A := by
    have h_inv : IsJointlyInvariant (lastPathKernel ϑ true) D.m W
        (fun S ↦ Ψ S • D.lastPathPairing (β (data false S)))
        fun S ↦ lastPathEdgeDatum S true := by
      -- Use the family that is `a` in this grid and `1` in the other one.
      intro a ha β'
      have h_ends : (a D.m).val =
          U.block (D.gridDiagEquiv D.m) ((1 : lastPathLevel ϑ false D.m).val, 1) := by
        simp [ha, Prod.mk_one_one]
      simpa [data, Prod.mk_one_one] using hΨ.sum_lastPathPairing_omega_invariant (Bool.rec 1 a)
        h_ends β β'
    exact h_inv.sum_chain_mem_nsmul (lastPathKernel ϑ true) (fun j hj ↦ h_free true j hj.le)
      (hy true) (IsReached true) (fun S _ ↦ h_step S true) (h_start true)
      fun _ hβ' ↦ h_tuples hβ hβ'
  -- So is the chain in the grid of the `Y`.
  have h_sum_both_chains (g : Gf D.E (D.LastPathIndex false D.m)) :
      ∑ S ∈ W, Ψ S * D.lastPathPairing (value false S g) (value true S (lastPathBlockPoint ϑ g)) ∈
        classes false • classes true • #W • N • A := by
    obtain ⟨β', hβ'⟩ :
        ∃ β' : TensorChain (D.LastPathFiniteDatum true) D.m →ₗ[ℂ] D.LastPathVector true D.m,
          ∀ S : EdgeTuple ϑ, value true S (lastPathBlockPoint ϑ g) = β' (data true S) :=
      (exists_linearMap_chain_eq_apply_pure (lastPathKernel ϑ true) D.m
        (D.lastPathToAlgForm true (y true)) (lastPathBlockPoint ϑ g)).imp
        fun _ h_value S ↦ h_value (lastPathEdgeDatum S true)
    have h_inv : IsJointlyInvariant (lastPathKernel ϑ false) D.m W
        (fun S ↦ Ψ S • D.lastPathPairing.flip (value true S (lastPathBlockPoint ϑ g)))
        fun S ↦ lastPathEdgeDatum S false := by
      intro a ha β
      have h_ends : (1 : lastPathLevel ϑ true D.m).val =
          U.block (D.gridDiagEquiv D.m) ((a D.m).val, 1) := by
        simp [ha, Prod.mk_one_one]
      simpa [hβ', data, Prod.mk_one_one] using hΨ.sum_lastPathPairing_omega_invariant (Bool.rec a 1)
        h_ends β β'
    exact h_inv.sum_chain_mem_nsmul (lastPathKernel ϑ false) (fun j hj ↦ h_free false j hj.le)
      (hy false) (IsReached false) (fun S _ ↦ h_step S false) (h_start false) (h_sum_tilde_chain g)
  -- The integrands are smooth and left invariant, so the integral commutes with the sum.
  have h_swap : lastPathPeriod Ψ y = classIntegral stdRatPoints (lastPathLevel ϑ false D.m) fun g ↦
      ∑ S ∈ W, Ψ S * D.lastPathPairing (value false S g) (value true S (lastPathBlockPoint ϑ g)) :=
    (classIntegral_sum W (fun S ↦ .mulLeft (Ψ S)) 1
      (fun S ↦ lastPathPairing_lastPathChain_mem_smoothInvariants S y) (by simp [value])).symm
  have h_count : ∏ z : Bool, ∏ j ∈ range (D.m + (!z).toNat),
      Nat.card (StdClasses (lastPathLevel ϑ z j)) =
        classes true * classes false * Nat.card (StdClasses (lastPathLevel ϑ false D.m)) := by
    simp [classes, prod_range_succ, mul_assoc]
  refine ⟨N * #W, Nat.mul_le_mul_left N (card_tuplesOn_edges_le _), ?_⟩
  rw [h_swap, h_count, mul_nsmul, mul_nsmul, mul_nsmul, mul_nsmul]
  refine classIntegral_mem_nsmul (h_free false D.m le_rfl) ?_ h_sum_both_chains
  -- The integrand is right invariant under the level of `Y^m_m`.
  rintro _ ⟨u, hu, rfl⟩ g
  exact hΨ.sum_lastPathPairing_mul_level hy hu g

end LastPathPairingTerms

/-!
## The last path: the periods

On the last path the lifts are multiples of algebraic lifts, and the period over `U(Y^m_m)` is a
multiple of the branching pairing.
-/

section LastPathPeriods

open Space Fintype Modulus

variable {P : Parameters} (D : Data P)

/-- Let `D` be admissible data with `m = D.m` lifts, let `z` be a half of the last path, through
the nodes `(z, i, m)`, and let `j ≤ m`. Here `GridPath.row m j` is the path along the first `j`
edges of this half, from the node `(z, 0, m)` to `(z, j, m)`, and its map `formMap` is the composite
of the theta lifts along these edges, for the data given by a tuple `S` of matrices on the
edges. There is a constant `c` such that, for every twist `ϑ`, tuple `S` and form `F` at
`(z, 0, m)`, the function of the lifted form is that given by `ofAlgForm` from `c` times the ratio
of the indices of the levels at the two ends (`levelIndex`) times the algebraic chain of lifts
`lastPathChain S z j F`. -/
theorem exists_gridPathMap_eq_ofAlgForm_smul_lastPathChain (D : Data P) (z : Bool) {j : ℕ}
    (hj : j ≤ D.m) :
    ∃ c : ℂ, ∀ (ϑ : D.MFoldTwist) (S : EdgeTuple ϑ) (F : D.GridForm z 0 D.m),
      ((GridPath.row D.m j).formMap S z F).val =
        ofAlgForm (-D.gridParam z 0 j D.m) (D.gridSigns z 0 j D.m)
          ((c * levelIndex ϑ z j D.m / levelIndex ϑ z 0 D.m) • lastPathChain S z j F) := by
  -- Each edge multiplies the lift by a constant over the index of the level at its lower end, and
  -- the index at its upper end does not depend on `ϑ`.
  induction j with
  | zero =>
    -- No lift is made, and `F` is recovered from its algebraic form by `ofAlgForm`.
    refine ⟨1, fun ϑ S F ↦ ?_⟩
    suffices h_form :
        F.val = ofAlgForm (-D.gridParam z 0 0 D.m) (D.gridSigns z 0 0 D.m)
          (lastPathChain S z 0 F) by
      simpa [GridPath.row, GridPath.formMap, Subgroup.index_ne_zero_of_finite] using h_form
    -- By definition `lastPathChain S z 0 F` is the algebraic form of `F`.
    exact (ofAlgForm_toAlgForm (D.isHCParam_lastPathColumns z hj) F).symm
  | succ j ih =>
    have hj_le : j ≤ D.m := Nat.le_of_succ_le hj
    obtain ⟨c, hc⟩ := ih hj_le
    obtain ⟨β, hβ⟩ := exists_lift_ofAlgForm_eq_smul
      (D.isHCParam_lastPathColumns z hj_le) (D.isHCParam_lastPathColumns z hj)
      (D.isLiftWeight_lastPathColumns z j) (c := 1 * P.jetScale D.towerExp) (by simp)
    -- `s` is the factor of the vacuum in `lastPathEdgeDatum`.
    let s : ℂ :=
      P.vacuumScale D.towerExp ^ card (D.LastPathIndex z (j + 1) × D.LastPathIndex z j)
    refine ⟨β * c / s / D.levelIndex 1 z (j + 1) D.m, fun ϑ S F ↦ ?_⟩
    -- `f` is the datum of the last edge without the factor `s`, and `T` its algebraic lift.
    let f : D.LastPathFiniteDatum z j :=
      vacuumDatum (stdSpace D.E (D.LastPathIndex z j)) (stdSpace D.E (D.LastPathIndex z (j + 1)))
        (gridModulus ϑ) (Pi.single (S (rowEdge z j D.m)) 1)
    let T : D.LastPathForm z j →ₗ[ℂ] D.LastPathForm z (j + 1) := (lastPathKernel ϑ z j).lift f
    have h_chain : lastPathChain S z (j + 1) F = s • T (lastPathChain S z j F) := by
      change (lastPathKernel ϑ z j).lift (s • f) (lastPathChain S z j F) =
        s • T (lastPathChain S z j F)
      rw [map_smul, LinearMap.smul_apply]
    -- The last edge is a theta lift between standard definite spaces. So it is `β` over the index
    -- of the level, times the algebraic lift.
    have h_edge (y : D.GridForm z j D.m) (φ : D.LastPathForm z j)
        (hy : y.val = ofAlgForm (-D.gridParam z 0 j D.m) (D.gridSigns z 0 j D.m) φ) :
        (liftMove (S (rowEdge z j D.m)) y).val = (β / stdLevelIndex (lastPathLevel ϑ z j)) •
          ofAlgForm (-D.gridParam z 0 (j + 1) D.m) (D.gridSigns z 0 (j + 1) D.m) (T φ) := by
      refine ((isEdgeFamily_grid_succ_left id hj le_rfl).isArrow_modDatum.1.coe_formLift y).trans ?_
      rw [hy, gridHarmonic, D.gridWeight_eq_lastPathDetExp z j]
      -- Replace both spaces by `stdSpace`, where `hβ` applies.
      refine isStd_gridSpace_last.std_induction ?_
      refine isStd_gridSpace_last.std_induction ?_
      exact hβ (gridChar_hasWeight_lastPathDetExp ϑ z j)
        (gridChar_hasWeight ϑ z j (D.LastPathIndex z (j + 1))) (lastPathLevel ϑ z j) f φ
    -- Compare the constants.
    have h_lower : (stdLevelIndex (lastPathLevel ϑ z j) : ℂ) = levelIndex ϑ z j D.m :=
      congrArg Nat.cast stdLevelIndex_levelOfSubgroup
    have h_upper : levelIndex ϑ z (j + 1) D.m = D.levelIndex 1 z (j + 1) D.m := by
      rw [levelIndex_eq_card_GL_untwisted (.inr j.succ_ne_zero),
        levelIndex_eq_card_GL_untwisted (.inr j.succ_ne_zero)]
    have h_const : β / levelIndex ϑ z j D.m * (c * levelIndex ϑ z j D.m / levelIndex ϑ z 0 D.m) =
        β * c / s / D.levelIndex 1 z (j + 1) D.m * levelIndex ϑ z (j + 1) D.m /
          levelIndex ϑ z 0 D.m * s := by
      have hs : s ≠ 0 := by simp [s]
      have h_index (ϑ' : D.MFoldTwist) (i : ℕ) : levelIndex ϑ' z i D.m ≠ 0 :=
        Nat.cast_ne_zero.2 Subgroup.index_ne_zero_of_finite
      rw [h_upper]
      field_simp [h_index]
    calc ((GridPath.row D.m (j + 1)).formMap S z F).val
        = (liftMove (S (rowEdge z j D.m)) ((GridPath.row D.m j).formMap S z F)).val := rfl
      _ = (β / stdLevelIndex (lastPathLevel ϑ z j)) •
            ofAlgForm (-D.gridParam z 0 (j + 1) D.m) (D.gridSigns z 0 (j + 1) D.m)
              (T ((c * levelIndex ϑ z j D.m / levelIndex ϑ z 0 D.m) • lastPathChain S z j F)) :=
          h_edge _ _ (hc ϑ S F)
      _ = _ := by
          rw [h_lower, h_chain, map_smul T, map_smul, smul_smul, h_const, smul_smul, map_smul]

/-- Let `Ψ` be a family of functions on edge tuples, one for each twist. At each real point `g`
there is a number `β` such that, for every twist `ϑ`, conjugate form `y` on `Y_m` and form `φ` on
`Ỹ^m_0`, the period of `Ψ` on the last path at `g` is `β` times the sum `lastPathPeriod (Ψ ϑ)` at
`(y, φ)` divided by `triangleGLCard false ϑ m`. This last number is the order of the general linear
group of the rank of `Y_m` modulo `𝔪₀ = ϖ Q`, with `ϖ = D.piM` and `Q` the product of the places of
`ϑ`. -/
theorem isProportional_lastPathPeriod (Ψ : ∀ ϑ : D.MFoldTwist, EdgeTuple ϑ → ℂ) :
    IsProportional (.last D.m) Ψ fun ((ϑ, y, φ) : D.PeriodTriple) ↦
      lastPathPeriod (Ψ ϑ) (fun z : Bool ↦ z.rec y φ) / triangleGLCard false ϑ D.m := by
  intro g
  have h_chain (z : Bool) : ∃ c : ℂ,
      ∀ (ϑ : D.MFoldTwist) (S : EdgeTuple ϑ) (F : D.GridForm z 0 D.m),
        ((GridPath.row D.m D.m).formMap S z F).1 =
          ofAlgForm (-D.gridParam z 0 D.m D.m) (D.gridSigns z 0 D.m D.m)
            ((c * levelIndex ϑ z D.m D.m / levelIndex ϑ z 0 D.m) • lastPathChain S z D.m F) :=
    D.exists_gridPathMap_eq_ofAlgForm_smul_lastPathChain z le_rfl
  choose c hc using h_chain
  obtain ⟨β, hβ⟩ := D.exists_integral_eq_lastPathPairing g
  obtain ⟨κ, hκ⟩ : ∃ κ : ℂ, ∀ ϑ : D.MFoldTwist,
      D.triangleGLCard false ϑ D.m = κ * levelIndex ϑ false 0 D.m :=
    D.exists_triangleGLCard_eq_mul_levelIndex D.m
  let γ : ℂ := β * (∏ z : Bool, c z) * D.levelIndex 1 true D.m D.m / D.levelIndex 1 true 0 D.m
  refine ⟨γ * κ, fun ⟨ϑ, y, φ⟩ ↦ ?_⟩
  -- Compare the two sides for each tuple `S`; `I S` is its term of `Ξ` without the factor `Ψ S`.
  let I (S : EdgeTuple ϑ) : ℂ := classIntegral stdRatPoints (lastPathLevel ϑ false D.m) fun h ↦
    D.lastPathPairing ((lastPathChain S false D.m y).1 h)
      ((lastPathChain S true D.m φ).1 (lastPathBlockPoint ϑ h))
  have h_term (S : EdgeTuple ϑ) :
      diagonalPeriodForm ϑ le_rfl g ((GridPath.row D.m D.m).formMap S false y)
          ((GridPath.row D.m D.m).formMap S true φ) = γ / levelIndex ϑ false 0 D.m * I S := by
    suffices h_integral : ∫ x : New.G D.E (D.gridSigns false 0 D.m D.m),
        ((GridPath.row D.m D.m).formMap S false y).1 x *
          ((GridPath.row D.m D.m).formMap S true φ).1
            (G.reindex (D.gridDiagEquiv D.m) (D.sumElim_gridSigns_comp_gridDiagEquiv_symm le_rfl)
              (.sum (x, 1, (gridModulus ϑ).flipScalar ^ D.m)) *
              ((g, 1) : New.G D.E (D.gridSigns true 0 D.m D.m)))
          ∂(D.gridSpace 0 false D.m D.m).quotMeasure = γ / levelIndex ϑ false 0 D.m * I S by
      simpa [periodPairing] using h_integral
    -- `erw`, as the grid spaces at `(m, m)` agree with those of `hc` and `hβ` by definition.
    erw [hc, hc, hβ _ _ _ _ (lastPathLevel ϑ false D.m)]
    -- The index at `Y^m_m` cancels, and those in the grid of the `Ỹ` do not depend on the twist.
    simp [I, γ, lastPathLevel, stdLevelIndex_levelOfSubgroup, levelIndex_eq_card_GL_untwisted,
      lastPathBlockPoint]
    field_simp [Subgroup.index_ne_zero_of_finite]
  -- The index of the level on `Y_m` and `triangleGLCard` differ by the constant `κ`.
  have h_index : γ / levelIndex ϑ false 0 D.m = γ * κ / triangleGLCard false ϑ D.m := by
    have h_order_ne : (triangleGLCard false ϑ D.m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 card_ne_zero
    have hκ_ne : κ ≠ 0 := left_ne_zero_of_mul (by rwa [← hκ ϑ])
    rw [hκ ϑ, mul_comm γ κ, mul_div_mul_left _ _ hκ_ne]
  change gridPeriod (.last D.m) Ψ g (ϑ, y, φ) =
    γ * κ * (lastPathPeriod (Ψ ϑ) (fun z : Bool ↦ z.rec y φ) / triangleGLCard false ϑ D.m)
  rw [mul_div_assoc', ← div_mul_eq_mul_div, ← h_index, gridPeriod, lastPathPeriod, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  rw [mul_left_comm, ← h_term S]
  -- The period along `TwoGridPath.last` is `diagonalPeriodForm` at `(m, m)` by definition.
  rfl

end LastPathPeriods

end New.Data

end
