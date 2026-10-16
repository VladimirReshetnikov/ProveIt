import GowersSzemeredi.Proofs16PolyPieceTwoData
import GowersSzemeredi.Proofs16UniformCoverTwo
import GowersSzemeredi.Proofs16WithSum

/-! Cylinders in dimension three and the three-term remainder (Notes L.5, D2).

In dimension three the remainder of Gowers's identity is
`g₁(z₀, z₂) + g₂(z₁, z₂) - g₃(z₂)`: two face functions of two coordinates and
one function of the last coordinate. This module covers such sums.
* `dropMid z = (z₀, z₂)`, `dropFirst z = (z₁, z₂)` and `lastPt3 z = z₂`, with
  the cylinders `cylMid`, `cylFirst`, `cylLast` of relations over them.
* `MultiplyLinearWith.cylMid`, `.cylFirst` and `.cylLast`: a cover of the
  base relation, with bounded fibres, lifts to the cylinder. The proof is
  `relation_lift_last` along a new last coordinate, then a coordinate
  permutation (`Equiv.swap 1 2`, `finRotate 3`).
* `cylinder_fiber_le` and `polyPieceTwoGraphs_fiber_le`: the fibre bounds.
  A union of `M` piece graphs has fibres of size at most `M`.
* `MultiplyLinearWith.three_remainder`: the cover of
  `relationSum (relationSum (cylMid Λ₁) (cylFirst Λ₂)) (relationScale (-1) (cylLast Λ₃))`. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi
open BaseCase

/-! ### Coordinate drops -/

/-- Drop the middle coordinate: `(z₀, z₂)`. -/
def dropMid {N : Nat} (z : Point N 3) : Point N 2 := fun i => z (if i = 0 then 0 else 2)

/-- Drop the first coordinate: `(z₁, z₂)`. -/
def dropFirst {N : Nat} (z : Point N 3) : Point N 2 := fun i => z (if i = 0 then 1 else 2)

/-- The last coordinate of a point of `Z_N^3`. -/
def lastPt3 {N : Nat} (z : Point N 3) : Point N 1 := fun _ => z 2

/-- The cylinder over `(z₀, z₂)`. -/
def cylMid {N : Nat} [NeZero N] (Λ : Finset (Point N 2 × ZMod N)) : Finset (Point N 3 × ZMod N) := by
  classical
  exact Finset.univ.filter fun z => (dropMid z.1, z.2) ∈ Λ

/-- The cylinder over `(z₁, z₂)`. -/
def cylFirst {N : Nat} [NeZero N] (Λ : Finset (Point N 2 × ZMod N)) :
    Finset (Point N 3 × ZMod N) := by
  classical
  exact Finset.univ.filter fun z => (dropFirst z.1, z.2) ∈ Λ

/-- The cylinder over `z₂`. -/
def cylLast {N : Nat} [NeZero N] (Λ : Finset (Point N 1 × ZMod N)) :
    Finset (Point N 3 × ZMod N) := by
  classical
  exact Finset.univ.filter fun z => (lastPt3 z.1, z.2) ∈ Λ

theorem mem_cylMid {N : Nat} [NeZero N] {Λ : Finset (Point N 2 × ZMod N)}
    {z : Point N 3 × ZMod N} : z ∈ cylMid Λ ↔ (dropMid z.1, z.2) ∈ Λ := by
  simp [cylMid]

theorem mem_cylFirst {N : Nat} [NeZero N] {Λ : Finset (Point N 2 × ZMod N)}
    {z : Point N 3 × ZMod N} : z ∈ cylFirst Λ ↔ (dropFirst z.1, z.2) ∈ Λ := by
  simp [cylFirst]

theorem mem_cylLast {N : Nat} [NeZero N] {Λ : Finset (Point N 1 × ZMod N)}
    {z : Point N 3 × ZMod N} : z ∈ cylLast Λ ↔ (lastPt3 z.1, z.2) ∈ Λ := by
  simp [cylLast]

/-! ### Fibre bounds -/

/-- A cylinder has the fibres of its base. -/
theorem cylinder_fiber_le {N a b : Nat} [NeZero N] (pi : Point N a → Point N b)
    (Λ : Finset (Point N b × ZMod N)) (w : Point N a) :
    (((Finset.univ : Finset (Point N a × ZMod N)).filter fun z => (pi z.1, z.2) ∈ Λ).filter
      fun z => z.1 = w).card ≤ (Λ.filter fun z => z.1 = pi w).card := by
  refine Finset.card_le_card_of_injOn (fun z => (pi z.1, z.2)) (fun z hz => ?_) ?_
  · obtain ⟨hz1, hz2⟩ := Finset.mem_filter.mp hz
    obtain ⟨-, hzΛ⟩ := Finset.mem_filter.mp hz1
    refine Finset.mem_filter.mpr ⟨hzΛ, ?_⟩
    show pi z.1 = pi w
    rw [hz2]
  · intro z hz z' hz' hzz
    have h1 := (Finset.mem_filter.mp hz).2
    have h2 := (Finset.mem_filter.mp hz').2
    have h3 : z.2 = z'.2 := by simpa using congrArg Prod.snd hzz
    exact Prod.ext (h1.trans h2.symm) h3

/-- A union of `M` piece graphs has fibres of size at most `M`. -/
theorem polyPieceTwoGraphs_fiber_le {N : Nat} [NeZero N] {theta gamma : Real} {M : Nat}
    (P : Fin M → PolyPieceTwo N theta gamma) (x : Point N 2) :
    ((polyPieceTwoGraphs P).filter fun z => z.1 = x).card ≤ M := by
  unfold polyPieceTwoGraphs
  rw [Finset.filter_biUnion]
  calc (Finset.univ.biUnion fun c => (partialGraph (P c).D (P c).phi).filter fun z => z.1 = x).card
      ≤ ∑ c, ((partialGraph (P c).D (P c).phi).filter fun z => z.1 = x).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _c : Fin M, 1 := Finset.sum_le_sum fun c _ => partialGraph_fiber_card_le_one _ _ x
    _ = M := by simp

theorem fiber_le_of_subset {N k : Nat} [NeZero N] {Γ Δ : Finset (Point N k × ZMod N)}
    (h : Γ ⊆ Δ) {M : Nat} (hfib : ∀ x, (Δ.filter fun z => z.1 = x).card ≤ M) (x : Point N k) :
    (Γ.filter fun z => z.1 = x).card ≤ M :=
  (Finset.card_le_card (Finset.filter_subset_filter _ h)).trans (hfib x)

/-! ### Covers of the cylinders -/

theorem dropMid_init_swap {N : Nat} (z : Point N 3) :
    section16Init (LeanProofs.GowersSzemeredi.coordinateReindex (Equiv.swap (1 : Fin 3) 2) z) =
      dropMid z := by
  funext i
  fin_cases i <;> rfl

theorem coordinateReindex_swap_twice {N : Nat} (z : Point N 3) :
    LeanProofs.GowersSzemeredi.coordinateReindex (Equiv.swap (1 : Fin 3) 2)
      (LeanProofs.GowersSzemeredi.coordinateReindex (Equiv.swap (1 : Fin 3) 2) z) = z := by
  funext i
  simp

theorem dropFirst_init_rotate {N : Nat} (z : Point N 3) :
    section16Init (LeanProofs.GowersSzemeredi.coordinateReindex (finRotate 3) z) = dropFirst z := by
  funext i
  fin_cases i <;> rfl

theorem coordinateReindex_rotate_symm {N : Nat} (z : Point N 3) :
    LeanProofs.GowersSzemeredi.coordinateReindex (finRotate 3).symm
      (LeanProofs.GowersSzemeredi.coordinateReindex (finRotate 3) z) = z := by
  funext i
  simp

/-- **The cylinder over `(z₀, z₂)` inherits a cover.** -/
theorem MultiplyLinearWith.cylMid {N : Nat} [NeZero N] [Fact N.Prime]
    {Qb Eb : Real → Real} {Λ : Finset (Point N 2 × ZMod N)}
    (hML : MultiplyLinearWith Qb Eb Λ)
    (M : Nat) (hfib : ∀ x : Point N 2, (Λ.filter fun z => z.1 = x).card ≤ M)
    (hQ : ∀ t, 0 < t → t ≤ 1 → 0 ≤ Qb t)
    (hE : ∀ t, 0 < t → t ≤ 1 → 0 < Eb t ∧ Eb t ≤ 1) :
    MultiplyLinearWith (fun t => max (Qb t) ((3 ^ (2 + 1) * M : Nat) : Real))
      (fun t => Eb t / 16) (cylMid Λ) := by
  have h := hML.relation_lift_last M hfib hQ hE (by norm_num)
  have h2 := MultiplyLinearWith.coordinateReindex h (Equiv.swap (1 : Fin 3) 2)
  refine MultiplyLinearWith.subset h2 ?_
  intro z hz
  have hzΛ := mem_cylMid.mp hz
  refine Finset.mem_image.mpr
    ⟨(LeanProofs.GowersSzemeredi.coordinateReindex (Equiv.swap (1 : Fin 3) 2) z.1, z.2), ?_, ?_⟩
  · apply mem_lastLiftRelation.mpr
    rw [dropMid_init_swap]
    exact hzΛ
  · exact Prod.ext (coordinateReindex_swap_twice z.1) rfl

/-- **The cylinder over `(z₁, z₂)` inherits a cover.** -/
theorem MultiplyLinearWith.cylFirst {N : Nat} [NeZero N] [Fact N.Prime]
    {Qb Eb : Real → Real} {Λ : Finset (Point N 2 × ZMod N)}
    (hML : MultiplyLinearWith Qb Eb Λ)
    (M : Nat) (hfib : ∀ x : Point N 2, (Λ.filter fun z => z.1 = x).card ≤ M)
    (hQ : ∀ t, 0 < t → t ≤ 1 → 0 ≤ Qb t)
    (hE : ∀ t, 0 < t → t ≤ 1 → 0 < Eb t ∧ Eb t ≤ 1) :
    MultiplyLinearWith (fun t => max (Qb t) ((3 ^ (2 + 1) * M : Nat) : Real))
      (fun t => Eb t / 16) (cylFirst Λ) := by
  have h := hML.relation_lift_last M hfib hQ hE (by norm_num)
  have h2 := MultiplyLinearWith.coordinateReindex h (finRotate 3).symm
  refine MultiplyLinearWith.subset h2 ?_
  intro z hz
  have hzΛ := mem_cylFirst.mp hz
  refine Finset.mem_image.mpr
    ⟨(LeanProofs.GowersSzemeredi.coordinateReindex (finRotate 3) z.1, z.2), ?_, ?_⟩
  · apply mem_lastLiftRelation.mpr
    rw [dropFirst_init_rotate]
    exact hzΛ
  · exact Prod.ext (coordinateReindex_rotate_symm z.1) rfl

theorem lastPt_dropFirst {N : Nat} (z : Point N 3) : lastPt (dropFirst z) = lastPt3 z := by
  funext i
  rfl

/-- **The cylinder over `z₂` inherits a cover.** -/
theorem MultiplyLinearWith.cylLast {N : Nat} [NeZero N] [Fact N.Prime]
    {Qb Eb : Real → Real} {Λ : Finset (Point N 1 × ZMod N)}
    (hML : MultiplyLinearWith Qb Eb Λ)
    (M : Nat) (hfib : ∀ x : Point N 1, (Λ.filter fun z => z.1 = x).card ≤ M)
    (hQ : ∀ t, 0 < t → t ≤ 1 → 0 ≤ Qb t)
    (hE : ∀ t, 0 < t → t ≤ 1 → 0 < Eb t ∧ Eb t ≤ 1) :
    MultiplyLinearWith
      (fun t => max (max (Qb t) ((3 ^ (1 + 1) * M : Nat) : Real)) ((3 ^ (2 + 1) * M : Nat) : Real))
      (fun t => Eb t / 16 / 16) (cylLast Λ) := by
  have h1 := hML.last_cylinder M hfib hQ hE
  have hfib1 : ∀ x : Point N 2, ((lastCylinder Λ).filter fun z => z.1 = x).card ≤ M := by
    intro x
    refine le_trans ?_ (hfib (lastPt x))
    have hEq : lastCylinder Λ = Finset.univ.filter (fun z : Point N 2 × ZMod N => (lastPt z.1, z.2) ∈ Λ) := by
      ext z
      rw [mem_lastCylinder]
      simp
    rw [hEq]
    exact cylinder_fiber_le (a := 2) (b := 1) lastPt Λ x
  have hQ1 : ∀ t, 0 < t → t ≤ 1 → 0 ≤ max (Qb t) ((3 ^ (1 + 1) * M : Nat) : Real) :=
    fun t ht ht1 => le_max_of_le_left (hQ t ht ht1)
  have hE1 : ∀ t, 0 < t → t ≤ 1 → 0 < Eb t / 16 ∧ Eb t / 16 ≤ 1 := by
    intro t ht ht1
    obtain ⟨a, b⟩ := hE t ht ht1
    exact ⟨by positivity, by linarith⟩
  have h2 := h1.cylFirst M hfib1 hQ1 hE1
  refine MultiplyLinearWith.subset h2 ?_
  intro z hz
  apply mem_cylFirst.mpr
  apply mem_lastCylinder.mpr
  rw [lastPt_dropFirst]
  exact mem_cylLast.mp hz

/-! ### The three-term remainder -/

/-- The remainder relation of a dimension-three piece. -/
def threeRemainderRel {N : Nat} [NeZero N] (Λ1 Λ2 : Finset (Point N 2 × ZMod N))
    (Λ3 : Finset (Point N 1 × ZMod N)) : Finset (Point N 3 × ZMod N) :=
  relationSum (relationSum (cylMid Λ1) (cylFirst Λ2)) (relationScale (-1) (cylLast Λ3))

theorem mem_threeRemainderRel {N : Nat} [NeZero N] {Λ1 Λ2 : Finset (Point N 2 × ZMod N)}
    {Λ3 : Finset (Point N 1 × ZMod N)} {z : Point N 3} {a b c : ZMod N}
    (h1 : (dropMid z, a) ∈ Λ1) (h2 : (dropFirst z, b) ∈ Λ2) (h3 : (lastPt3 z, c) ∈ Λ3) :
    (z, a + b - c) ∈ threeRemainderRel Λ1 Λ2 Λ3 := by
  unfold threeRemainderRel relationSum relationScale
  refine Finset.mem_image.mpr ⟨((z, a + b), (z, -1 * c)), Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, rfl⟩, by simp only [Prod.mk.injEq, true_and]; ring⟩
  · exact Finset.mem_image.mpr ⟨((z, a), (z, b)), Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨mem_cylMid.mpr h1, mem_cylFirst.mpr h2⟩, rfl⟩, rfl⟩
  · exact Finset.mem_image.mpr ⟨(z, c), mem_cylLast.mpr h3, rfl⟩

/-- The count control of the three-term remainder. -/
def threeRemQ (Q1 Q2 Q3 : Real → Real) (M1 M2 M3 : Nat) : Real → Real :=
  fun s => (max (Q1 (s / 4)) ((3 ^ (2 + 1) * M1 : Nat) : Real) *
      max (Q2 (s / 4)) ((3 ^ (2 + 1) * M2 : Nat) : Real)) *
    max (max (Q3 (s / 2)) ((3 ^ (1 + 1) * M3 : Nat) : Real)) ((3 ^ (2 + 1) * M3 : Nat) : Real)

/-- The width-exponent control of the three-term remainder. -/
def threeRemE (E1 E2 E3 : Real → Real) : Real → Real :=
  fun s => (E1 (s / 4) / 16 * (E2 (s / 4) / 16)) * (E3 (s / 2) / 16 / 16)

/-- **The cover of the three-term remainder.** -/
theorem MultiplyLinearWith.three_remainder {N : Nat} [NeZero N] [Fact N.Prime]
    {Q1 E1 Q2 E2 Q3 E3 : Real → Real} {Λ1 Λ2 : Finset (Point N 2 × ZMod N)}
    {Λ3 : Finset (Point N 1 × ZMod N)}
    (h1 : MultiplyLinearWith Q1 E1 Λ1) (h2 : MultiplyLinearWith Q2 E2 Λ2)
    (h3 : MultiplyLinearWith Q3 E3 Λ3) {M1 M2 M3 : Nat}
    (hf1 : ∀ x, (Λ1.filter fun z => z.1 = x).card ≤ M1)
    (hf2 : ∀ x, (Λ2.filter fun z => z.1 = x).card ≤ M2)
    (hf3 : ∀ x, (Λ3.filter fun z => z.1 = x).card ≤ M3)
    (hQ1 : ∀ t, 0 < t → t ≤ 1 → 0 ≤ Q1 t) (hQ2 : ∀ t, 0 < t → t ≤ 1 → 0 ≤ Q2 t)
    (hQ3 : ∀ t, 0 < t → t ≤ 1 → 0 ≤ Q3 t)
    (hE1 : ∀ t, 0 < t → t ≤ 1 → 0 < E1 t ∧ E1 t ≤ 1)
    (hE2 : ∀ t, 0 < t → t ≤ 1 → 0 < E2 t ∧ E2 t ≤ 1)
    (hE3 : ∀ t, 0 < t → t ≤ 1 → 0 < E3 t ∧ E3 t ≤ 1) :
    MultiplyLinearWith (threeRemQ Q1 Q2 Q3 M1 M2 M3) (threeRemE E1 E2 E3)
      (threeRemainderRel Λ1 Λ2 Λ3) := by
  have c1 := h1.cylMid M1 hf1 hQ1 hE1
  have c2 := h2.cylFirst M2 hf2 hQ2 hE2
  have c3 := (h3.cylLast M3 hf3 hQ3 hE3).relationScale (-1)
  have hQc2 : ∀ s, 0 < s → s ≤ 1 → 0 ≤ max (Q2 s) ((3 ^ (2 + 1) * M2 : Nat) : Real) :=
    fun s hs hs1 => le_max_of_le_left (hQ2 s hs hs1)
  have hEc2 : ∀ s, 0 < s → s ≤ 1 → 0 ≤ E2 s / 16 := fun s hs hs1 =>
    by have := (hE2 s hs hs1).1; positivity
  have s12 := c1.relationSum c2 (lam := 1 / 2) (by norm_num) (by norm_num) hQc2 hEc2
  have hQc3 : ∀ s, 0 < s → s ≤ 1 → 0 ≤ max (max (Q3 s) ((3 ^ (1 + 1) * M3 : Nat) : Real))
      ((3 ^ (2 + 1) * M3 : Nat) : Real) :=
    fun s hs hs1 => le_max_of_le_left (le_max_of_le_left (hQ3 s hs hs1))
  have hEc3 : ∀ s, 0 < s → s ≤ 1 → 0 ≤ E3 s / 16 / 16 := fun s hs hs1 =>
    by have := (hE3 s hs hs1).1; positivity
  have s123 := s12.relationSum c3 (lam := 1 / 2) (by norm_num) (by norm_num) hQc3 hEc3
  unfold threeRemainderRel
  refine s123.congr_controls (fun s _ _ => ?_) (fun s _ _ => ?_)
  · unfold threeRemQ
    have e1 : 1 / 2 * (1 / 2 * s) = s / 4 := by ring
    have e2 : (1 - 1 / 2) * (1 / 2 * s) = s / 4 := by ring
    have e3 : (1 - 1 / 2) * s = s / 2 := by ring
    simp only [e1, e2, e3]
  · unfold threeRemE
    have e1 : 1 / 2 * (1 / 2 * s) = s / 4 := by ring
    have e2 : (1 - 1 / 2) * (1 / 2 * s) = s / 4 := by ring
    have e3 : (1 - 1 / 2) * s = s / 2 := by ring
    simp only [e1, e2, e3]

end LeanProofs.GowersSzemeredi
