import CoarseDegrees.Compactness

/-!
# The spectrum of a dyadic code

The representative spectrum clause of research report 10, Theorem 1.4(a), equivalently the
jump-cone spectrum of the synthesis, Section 6:

```
Spec(R(A)) = {b : A ≤ᵀ b′}
```

Stated in limit form, so that no jump operator is needed: the coarse class of `R(A)` has a
representative of the exact Turing degree of `B` precisely when `A` is the limit of a
`B`-computable approximation (`spectrum_Rc`).

One direction is the criterion of `CoarseDegrees.Majority`.  The other needs a representative of
the *exact* degree of `B`, not merely one below it: take any `B`-computable coarse description
and overwrite it, on a computable set of density zero, with a copy of `B`.  Overwriting on a
density-zero set does not change the coarse class, and the copy makes `B` readable back.

The sparse set used is `sparse = {2^k - 1 : k}`, one point in each dyadic column, so that
`CoarseDegrees.densityZero_of_bounded_columns` gives its density directly and `col` decodes it.

Everything in this file is proved.
-/

noncomputable section

open scoped Classical Computability
open TuringDegrees
open scoped SetTuring

namespace CoarseDegrees

/-! ## Splicing two sets along a computable set -/

/-- Two sets reducible to `O`, spliced along a computable set, are reducible to `O`. -/
theorem setTuringReducible_splice {O D E S : Set ℕ}
    (hS : ComputablePred (fun n => n ∈ S)) (hD : D ≤ᵀₛ O) (hE : E ≤ᵀₛ O) :
    ((D \ S) ∪ (E ∩ S)) ≤ᵀₛ O := by
  obtain ⟨_, hSc⟩ := hS
  have h0 : RecursiveIn {characteristic O} (fun n : ℕ => (Part.some n : Part ℕ)) :=
    Partrec.recursiveIn (f := fun n : ℕ => (Part.some n : Part ℕ)) Computable.id
  have hpair := recursiveIn_pair h0 (recursiveIn_pair hD hE)
  have hc : Computable (fun p : ℕ =>
      bif decide (p.unpair.1 ∈ S) then p.unpair.2.unpair.2 else p.unpair.2.unpair.1) := by
    refine Computable.cond (hSc.comp (Computable.fst.comp Computable.unpair))
      (Computable.snd.comp (Computable.unpair.comp (Computable.snd.comp Computable.unpair)))
      (Computable.fst.comp (Computable.unpair.comp (Computable.snd.comp Computable.unpair)))
  refine (recursiveIn_map hpair hc).of_eq fun n => ?_
  simp only [characteristic, Seq.seq, Part.map_some, Part.bind_some, Nat.unpair_pair]
  by_cases hn : n ∈ S
  · simp [characteristicValue, hn, Set.mem_union, Set.mem_sdiff, Set.mem_inter_iff]
  · simp [characteristicValue, hn, Set.mem_union, Set.mem_sdiff, Set.mem_inter_iff]

/-! ## A sparse computable set of markers -/

/-- One marker in each dyadic column: `n` is a marker exactly when `n = 2^k - 1`, and then
`col n = k`. -/
def sparse : Set ℕ := {n | 2 ^ (col n) = n + 1}

theorem mem_sparse_two_pow_sub_one (k : ℕ) : 2 ^ k - 1 ∈ sparse := by
  have : col (2 ^ k - 1) = k := col_two_pow_sub_one k
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  simp only [sparse, Set.mem_setOf_eq, this]
  omega

theorem computable_sparse : ComputablePred (fun n => n ∈ sparse) := by
  refine ⟨fun n => Nat.decEq _ _, ?_⟩
  have hpow : Computable (fun m : ℕ => 2 ^ m) :=
    ((Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 2) Primrec.id).to_comp
  have heq : Computable₂ (fun a b : ℕ => decide (a = b)) :=
    (Primrec.eq (α := ℕ)).computablePred.decide
  exact heq.comp (hpow.comp computable_col) Computable.succ

/-- The markers meet each column in a single point, so they have density zero. -/
theorem densityZero_sparse : DensityZero sparse := by
  refine densityZero_of_bounded_columns fun k => ⟨2 ^ k, fun n hn hcol => ?_⟩
  simp only [sparse, Set.mem_setOf_eq, hcol] at hn
  omega

/-! ## Implanting a copy of `B` -/

/-- `D` with a copy of `B` written on the markers: `2^k - 1` is put in exactly when `k ∈ B`. -/
def implant (D B : Set ℕ) : Set ℕ := (D \ sparse) ∪ (Rc B ∩ sparse)

theorem implant_coarseEq (D B : Set ℕ) : SetCoarseEq (implant D B) D := by
  refine densityZero_sparse.mono fun n hn => ?_
  by_contra hns
  rcases Set.mem_symmDiff.mp hn with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rcases h1 with ⟨h, _⟩ | ⟨_, h⟩
    · exact h2 h
    · exact hns h
  · exact h2 (Or.inl ⟨h1, hns⟩)

theorem implant_reducible {D B : Set ℕ} (hD : D ≤ᵀₛ B) : implant D B ≤ᵀₛ B :=
  setTuringReducible_splice computable_sparse hD (Rc_reducible B)

theorem reducible_implant (D B : Set ℕ) : B ≤ᵀₛ implant D B := by
  have hq : Computable (fun k : ℕ => 2 ^ k - 1) :=
    (Primrec.nat_sub.comp ((Primrec₂.unpaired'.1 Nat.Primrec.pow).comp
      (Primrec.const 2) Primrec.id) (Primrec.const 1)).to_comp
  refine setTuringReducible_of_one_query (fun k => 2 ^ k - 1) hq (fun _ v => v)
    (Computable.snd.to₂) fun k => ?_
  have hmem : (2 ^ k - 1 ∈ implant D B) ↔ k ∈ B := by
    have hs : 2 ^ k - 1 ∈ sparse := mem_sparse_two_pow_sub_one k
    constructor
    · rintro (⟨_, h⟩ | ⟨h, _⟩)
      · exact absurd hs h
      · rwa [mem_Rc, col_two_pow_sub_one] at h
    · intro hk
      exact Or.inr ⟨by rw [mem_Rc, col_two_pow_sub_one]; exact hk, hs⟩
  by_cases hk : k ∈ B
  · rw [characteristicValue, characteristicValue, if_pos hk, if_pos (hmem.mpr hk)]
  · rw [characteristicValue, characteristicValue, if_neg hk, if_neg (fun h => hk (hmem.mp h))]

theorem implant_equivalent {D B : Set ℕ} (hD : D ≤ᵀₛ B) : implant D B ≡ᵀₛ B :=
  ⟨implant_reducible hD, reducible_implant D B⟩

/-! ## The spectrum -/

theorem SetCoarseEq.trans {X Y Z : Set ℕ} (hXY : SetCoarseEq X Y) (hYZ : SetCoarseEq Y Z) :
    SetCoarseEq X Z := by
  refine (hXY.union hYZ).mono fun n hn => ?_
  rcases Set.mem_symmDiff.mp hn with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> by_cases hY : n ∈ Y
  · exact Or.inr (Set.mem_symmDiff.mpr (Or.inl ⟨hY, h2⟩))
  · exact Or.inl (Set.mem_symmDiff.mpr (Or.inl ⟨h1, hY⟩))
  · exact Or.inl (Set.mem_symmDiff.mpr (Or.inr ⟨hY, h2⟩))
  · exact Or.inr (Set.mem_symmDiff.mpr (Or.inr ⟨h1, hY⟩))

/-- **The spectrum of a dyadic code** (report 10, Theorem 1.4(a); synthesis, Section 6).  The
coarse class of `R(A)` has a representative of the exact Turing degree of `B` exactly when `A`
is the limit of a `B`-computable approximation, that is — by Shoenfield's limit lemma — exactly
when `A ≤ᵀ B′`.  So the representative spectrum of `R(A)` is the jump cone `{b : A ≤ᵀ b′}`,
which has no least element unless `A ≤ᵀ ∅′`. -/
theorem spectrum_Rc {A B : Set ℕ} :
    (∃ g : Set ℕ, SetCoarseEq g (Rc A) ∧ g ≡ᵀₛ B) ↔ LimitComputableIn B A := by
  constructor
  · rintro ⟨g, hg, hgB, -⟩
    exact limit_of_description hgB hg
  · intro h
    obtain ⟨D, hD, hDA⟩ := exists_description_of_limit h
    exact ⟨implant D B, (implant_coarseEq D B).trans hDA, implant_equivalent hD⟩

end CoarseDegrees
