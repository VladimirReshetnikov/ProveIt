import GowersSzemeredi.Proofs16ThreeCylinders
import GowersSzemeredi.Proofs16FibreGeometry

/-! Generic face lifts and finite relation sums (Notes L.6, E2).

The remainder of Gowers's identity in dimension `k+1` is a signed sum of the
`2^k - 1` translated vertices `φ_e`, `e ≠ 1`. Each `φ_e` ignores every
coordinate `i` with `e i = false`. This module provides, in every dimension:
* `dropAt j = Fin.removeNth j` and the cylinder `cylAt j Λ` over a
  `k`-dimensional relation;
* `MultiplyLinearWith.cylAt`: a cover of `Λ` with bounded fibres lifts to the
  cylinder. The proof is `relation_lift_last` along a new last coordinate,
  then the permutation `liftPerm j`, which sends `last ↦ j` and
  `castSucc i ↦ j.succAbove i`;
* `relSumFin n Γ`, the pointwise sum of `n + 1` relations, and
  `MultiplyLinearWith.relSumFin`: every summand is covered at scale
  `ρ/(n+1)`, so counts and width exponents multiply at that common scale;
* `exists_false_of_ne_one`: every vertex other than the all-ones vertex
  has a coordinate `i` with `e i = false`.

These replace the named faces of dimension three (`cylMid`, `cylFirst`,
`cylLast`, `relationSum` twice). -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi
open BaseCase

/-! ### Cylinders over a dropped coordinate -/

/-- Drop coordinate `j` of a point. -/
def dropAt {N k : Nat} (j : Fin (k + 1)) (z : Point N (k + 1)) : Point N k :=
  Fin.removeNth j z

/-- The cylinder over `Λ` along coordinate `j`. -/
def cylAt {N k : Nat} [NeZero N] (j : Fin (k + 1)) (Λ : Finset (Point N k × ZMod N)) :
    Finset (Point N (k + 1) × ZMod N) := by
  classical
  exact Finset.univ.filter fun z => (dropAt j z.1, z.2) ∈ Λ

theorem mem_cylAt {N k : Nat} [NeZero N] {j : Fin (k + 1)} {Λ : Finset (Point N k × ZMod N)}
    {z : Point N (k + 1) × ZMod N} : z ∈ cylAt j Λ ↔ (dropAt j z.1, z.2) ∈ Λ := by
  classical
  simp [cylAt]

/-- The permutation sending `last ↦ j` and `castSucc i ↦ j.succAbove i`. -/
def liftPerm {k : Nat} (j : Fin (k + 1)) : Fin (k + 1) ≃ Fin (k + 1) :=
  finSuccEquivLast.trans (finSuccEquiv' j).symm

theorem liftPerm_castSucc {k : Nat} (j : Fin (k + 1)) (i : Fin k) :
    liftPerm j i.castSucc = j.succAbove i := by
  simp [liftPerm, finSuccEquivLast_castSucc, finSuccEquiv'_symm_some]

theorem init_reindex_liftPerm {N k : Nat} (j : Fin (k + 1)) (z : Point N (k + 1)) :
    section16Init (LeanProofs.GowersSzemeredi.coordinateReindex (liftPerm j) z) = dropAt j z := by
  funext i
  simp [section16Init, dropAt, Fin.removeNth, liftPerm_castSucc]

theorem reindex_liftPerm_symm {N k : Nat} (j : Fin (k + 1)) (z : Point N (k + 1)) :
    LeanProofs.GowersSzemeredi.coordinateReindex (liftPerm j).symm
      (LeanProofs.GowersSzemeredi.coordinateReindex (liftPerm j) z) = z := by
  funext i
  simp

/-- **A cover lifts to the cylinder over any dropped coordinate.** -/
theorem MultiplyLinearWith.cylAt {N k : Nat} [NeZero N] [Fact N.Prime]
    {Qb Eb : Real → Real} {Λ : Finset (Point N k × ZMod N)}
    (hML : MultiplyLinearWith Qb Eb Λ)
    (M : Nat) (hfib : ∀ x : Point N k, (Λ.filter fun z => z.1 = x).card ≤ M)
    (hQ : ∀ t, 0 < t → t ≤ 1 → 0 ≤ Qb t)
    (hE : ∀ t, 0 < t → t ≤ 1 → 0 < Eb t ∧ Eb t ≤ 1) (hk : 0 < k) (j : Fin (k + 1)) :
    MultiplyLinearWith (fun t => max (Qb t) ((3 ^ (k + 1) * M : Nat) : Real))
      (fun t => Eb t / 16) (cylAt j Λ) := by
  classical
  have h := hML.relation_lift_last M hfib hQ hE hk
  have h2 := MultiplyLinearWith.coordinateReindex h (liftPerm j).symm
  refine MultiplyLinearWith.subset h2 ?_
  intro z hz
  have hzΛ := mem_cylAt.mp hz
  refine Finset.mem_image.mpr
    ⟨(LeanProofs.GowersSzemeredi.coordinateReindex (liftPerm j) z.1, z.2), ?_, ?_⟩
  · apply mem_lastLiftRelation.mpr
    rw [init_reindex_liftPerm]
    exact hzΛ
  · exact Prod.ext (reindex_liftPerm_symm j z.1) rfl

/-! ### Finite sums of relations -/

theorem mem_relationSum_of {N k : Nat} [NeZero N] {Gamma1 Gamma2 : Finset (Point N k × ZMod N)}
    {x : Point N k} {y1 y2 : ZMod N} (h1 : (x, y1) ∈ Gamma1) (h2 : (x, y2) ∈ Gamma2) :
    (x, y1 + y2) ∈ relationSum Gamma1 Gamma2 := by
  classical
  unfold relationSum
  exact Finset.mem_image.mpr ⟨((x, y1), (x, y2)),
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h1, h2⟩, rfl⟩, rfl⟩

/-- The pointwise sum of `n + 1` relations. -/
def relSumFin {N k : Nat} [NeZero N] :
    (n : Nat) → (Fin (n + 1) → Finset (Point N k × ZMod N)) → Finset (Point N k × ZMod N)
  | 0, Gamma => Gamma 0
  | n + 1, Gamma => relationSum (relSumFin n fun i => Gamma i.castSucc) (Gamma (Fin.last (n + 1)))

theorem mem_relSumFin {N k : Nat} [NeZero N] {x : Point N k} :
    ∀ (n : Nat) (Gamma : Fin (n + 1) → Finset (Point N k × ZMod N)) (a : Fin (n + 1) → ZMod N),
      (∀ i, (x, a i) ∈ Gamma i) → (x, ∑ i, a i) ∈ relSumFin n Gamma
  | 0, Gamma, a, h => by simpa [relSumFin] using h 0
  | n + 1, Gamma, a, h => by
    rw [Fin.sum_univ_castSucc]
    exact mem_relationSum_of (mem_relSumFin n _ _ fun i => h i.castSucc) (h _)

theorem relSumFin_mono {N k : Nat} [NeZero N] :
    ∀ (n : Nat) {Gamma Gamma' : Fin (n + 1) → Finset (Point N k × ZMod N)},
      (∀ i, Gamma i ⊆ Gamma' i) → relSumFin n Gamma ⊆ relSumFin n Gamma'
  | 0, _, _, h => h 0
  | n + 1, _, _, h => relationSum_mono (relSumFin_mono n fun i => h i.castSucc) (h _)

/-- **A finite sum of covered relations is covered**, every summand at scale
`ρ/(n+1)`. -/
theorem MultiplyLinearWith.relSumFin {N k : Nat} [NeZero N] :
    ∀ (n : Nat) {Gamma : Fin (n + 1) → Finset (Point N k × ZMod N)}
      {Q E : Fin (n + 1) → Real → Real},
      (∀ i, MultiplyLinearWith (Q i) (E i) (Gamma i)) →
      (∀ i s, 0 < s → s ≤ 1 → 0 ≤ Q i s) → (∀ i s, 0 < s → s ≤ 1 → 0 ≤ E i s) →
      MultiplyLinearWith (fun s => ∏ i, Q i (s / ((n : Real) + 1)))
        (fun s => ∏ i, E i (s / ((n : Real) + 1))) (relSumFin n Gamma)
  | 0, Gamma, Q, E, h, _, _ => by
    have hfun : ∀ (F : Fin (0 + 1) → Real → Real),
        (fun s => ∏ i, F i (s / (((0 : Nat) : Real) + 1))) = F 0 := by
      intro F; funext s; simp
    rw [hfun Q, hfun E]
    exact h 0
  | n + 1, Gamma, Q, E, h, hQ, hE => by
    have ih := MultiplyLinearWith.relSumFin n (Gamma := fun i => Gamma i.castSucc)
      (Q := fun i => Q i.castSucc) (E := fun i => E i.castSucc) (fun i => h i.castSucc)
      (fun i => hQ i.castSucc) (fun i => hE i.castSucc)
    have hn1 : (0 : Real) < (n : Real) + 1 := by positivity
    have hn2 : (0 : Real) < ((n + 1 : Nat) : Real) + 1 := by positivity
    set lam : Real := ((n : Real) + 1) / (((n + 1 : Nat) : Real) + 1) with hlam
    have hl : 0 < lam := div_pos hn1 hn2
    have hl1 : lam < 1 := by
      rw [hlam, div_lt_one hn2]; push_cast; linarith
    have hsum := MultiplyLinearWith.relationSum ih (h (Fin.last (n + 1))) hl hl1
      (hQ (Fin.last (n + 1))) (hE (Fin.last (n + 1)))
    have hA : ∀ s : Real, lam * s / ((n : Real) + 1) = s / (((n + 1 : Nat) : Real) + 1) := by
      intro s; rw [hlam]; field_simp
    have hB : ∀ s : Real, (1 - lam) * s = s / (((n + 1 : Nat) : Real) + 1) := by
      intro s; rw [hlam]; field_simp; push_cast; ring
    have hfun : ∀ F : Fin (n + 1 + 1) → Real → Real,
        (fun s => (∏ i : Fin (n + 1), F i.castSucc (lam * s / ((n : Real) + 1))) *
            F (Fin.last (n + 1)) ((1 - lam) * s)) =
          fun s => ∏ i, F i (s / (((n + 1 : Nat) : Real) + 1)) := by
      intro F; funext s
      conv_rhs => rw [Fin.prod_univ_castSucc]
      simp only [hA, hB]
    rw [← hfun Q, ← hfun E]
    exact hsum

/-! ### Vertex maps as functions of a face -/

/-- Every vertex other than the all-ones one has an unused coordinate. -/
theorem exists_false_of_ne_one {k : Nat} {e : Fin k → Bool} (he : e ≠ fun _ => true) :
    ∃ i, e i = false := by
  by_contra h
  apply he
  funext i
  by_contra hi
  exact h ⟨i, by simpa using hi⟩

end LeanProofs.GowersSzemeredi
