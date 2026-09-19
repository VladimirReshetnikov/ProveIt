import CoarseDegrees.Majority

/-!
# The hyper-core of a dyadic code, and the failure of hyperarithmetic compactness

Theorem 1.4(a),(b) of research report 10 (`docs/research-reports/10/coarse_hyperdegrees.tex`).

The cone-avoiding compactness theorem of Hirschfeldt--Jockusch--Kuyper--Schupp (2016,
Theorem 3.7), equivalently the robust-radius characterization of the core (synthesis,
Theorem 4.8), says that a set in the core of `X` is already computable from *some* coarse
description at every small positive radius.  This file shows that the hyperarithmetic analogue
is false, and the dyadic code is the counterexample:

* `hcore_Rc`: the hyper-core of `R(A)` is exactly the collection of sets hyperarithmetic in `A`
  (one inclusion is proved outright, the other uses the admitted transitivity of `≤_h`);
* `exists_computable_approx`: for every `K` there is a *computable* `Y` whose disagreement with
  `R(A)` is confined to the columns from `K` on, so that `|(R(A) △ Y) ∩ [0,N)| ≤ N/2^K` for
  every `N`;
* `hyperarithmetic_compactness_fails`: for non-hyperarithmetic `A` these two coexist, so no
  compactness theorem for `≤_h` can hold.

Everything here is proved except where it appeals to `HypIn.trans` of `CoarseDegrees.Hyper`.
-/

noncomputable section

open scoped Classical Computability
open TuringDegrees
open scoped SetTuring

namespace CoarseDegrees

/-! ## Monotonicity of hyperarithmetic reducibility in the oracle -/

/-- Enlarging the oracle in the Turing sense preserves `Σ¹₁`-ness.  This is the special case of
transitivity in which the lower step is a Turing reduction, and unlike the general case it is
immediate from the normal form. -/
theorem Sigma11In.mono {X Y Z : Set ℕ} (h : Sigma11In Y X) (hYZ : Y ≤ᵀₛ Z) : Sigma11In Z X := by
  obtain ⟨T, hT, hX⟩ := h
  exact ⟨T, hT.trans hYZ, hX⟩

theorem HypIn.mono {X Y Z : Set ℕ} (h : HypIn Y X) (hYZ : Y ≤ᵀₛ Z) : HypIn Z X :=
  ⟨h.1.mono hYZ, h.2.mono hYZ⟩

/-- A computable set is Turing reducible to anything. -/
theorem setTuringReducible_of_computablePred {Y O : Set ℕ}
    (h : ComputablePred (fun n => n ∈ Y)) : Y ≤ᵀₛ O := by
  obtain ⟨_, hc⟩ := h
  have hv : Computable (characteristicValue Y) := by
    refine (Computable.cond hc (Computable.const 1) (Computable.const 0)).of_eq fun n => ?_
    by_cases hn : n ∈ Y <;> simp [characteristicValue, hn]
  exact Partrec.recursiveIn (f := characteristic Y) hv

/-! ## The hyper-core of a dyadic code -/

theorem SetCoarseEq.refl (X : Set ℕ) : SetCoarseEq X X := by
  have : symmDiff X X = (∅ : Set ℕ) := symmDiff_self X
  rw [SetCoarseEq, this]
  refine (tendsto_const_nhds (x := (0 : ℝ)) (f := Filter.atTop)).congr fun N => ?_
  simp [count]

/-- The hyper-core of `X`: the sets hyperarithmetic in every coarse description of `X`.  This is
`Core_h` of report 10, the `≤_h` analogue of `CoarseDegrees.core`. -/
def hcore (X : Set ℕ) : Set (Set ℕ) :=
  {A | ∀ D : Set ℕ, SetCoarseEq D X → HypIn D A}

/-- **The coded set lies in the hyper-core of its dyadic code.**  This is the content of
Theorem 1.4(a): every coarse description of `R(A)` computes a limit approximation to `A`, hence
is hyperarithmetically above `A`. -/
theorem mem_hcore_Rc (A : Set ℕ) : A ∈ hcore (Rc A) := fun _ hD =>
  hypIn_of_description (RecursiveIn.oracle _ (Set.mem_singleton _)) hD

/-- Conversely, nothing in the hyper-core of `R(A)` goes beyond `A`: test the core against the
description `R(A)` itself, which is Turing equivalent to `A`. -/
theorem hcore_Rc_subset (A : Set ℕ) : hcore (Rc A) ⊆ {X | HypIn A X} := fun _ hX =>
  (hX (Rc A) (SetCoarseEq.refl _)).mono (Rc_reducible A)

/-- **The hyper-core of a dyadic code** (report 10, Theorem 1.4(a)): `Core_h(R(A)) = Δ¹₁(A)`.
So the coarse classes of `R(A)` have a least hyperdegree, namely that of `A`, whereas they have
a least Turing degree only when `A ≤ᵀ ∅′`. -/
theorem hcore_Rc (A : Set ℕ) : hcore (Rc A) = {X | HypIn A X} := by
  refine Set.Subset.antisymm (hcore_Rc_subset A) fun X hX D hD => ?_
  exact hX.trans (mem_hcore_Rc A D hD)

/-! ## Computable approximations to a dyadic code -/

/-- The set marked by a finite list of bits: `n` belongs when entry `n` of `l` is `true`.
Only finitely much information is involved, so the set is computable. -/
def finSet (l : List Bool) : Set ℕ := {n | (l[n]?).getD false = true}

instance decidableFinSet (l : List Bool) : DecidablePred (fun n => n ∈ finSet l) :=
  fun _ => instDecidableEqBool _ _

theorem computable_finSet (l : List Bool) : ComputablePred (fun n => n ∈ finSet l) := by
  refine ⟨decidableFinSet l, ?_⟩
  exact ((Primrec.option_getD.comp (Primrec.list_getElem?.comp (Primrec.const l) Primrec.id)
    (Primrec.const false)).to_comp).of_eq fun n => by simp [finSet]

/-- The first `K` bits of `A`. -/
def bitsOf (A : Set ℕ) (K : ℕ) : List Bool := (List.range K).map (fun k => decide (k ∈ A))

theorem mem_finSet_bitsOf {A : Set ℕ} {K n : ℕ} (h : n < K) :
    n ∈ finSet (bitsOf A K) ↔ n ∈ A := by
  simp only [finSet, bitsOf, Set.mem_setOf_eq, List.getElem?_map,
    List.getElem?_range h, Option.map_some, Option.getD_some, decide_eq_true_eq]

/-- The set of numbers whose column index is marked in `l`.  Taking `l` to be the first `K` bits
of `A` gives a computable set agreeing with `R(A)` on every column below `K`. -/
def listApprox (l : List Bool) : Set ℕ := {n | col n ∈ finSet l}

instance decidableListApprox (l : List Bool) : DecidablePred (fun n => n ∈ listApprox l) :=
  fun n => decidableFinSet l (col n)

theorem computable_listApprox (l : List Bool) : ComputablePred (fun n => n ∈ listApprox l) := by
  obtain ⟨_, hf⟩ := computable_finSet l
  exact ⟨decidableListApprox l, (hf.comp computable_col).of_eq fun n => by simp [listApprox]⟩

theorem mem_listApprox_bitsOf {A : Set ℕ} {K n : ℕ} (h : col n < K) :
    n ∈ listApprox (bitsOf A K) ↔ n ∈ Rc A := by
  rw [mem_Rc]
  exact mem_finSet_bitsOf h

/-- **Computable approximations at every radius** (report 10, Theorem 1.4(b)).  For every `K`
there is a computable `Y` disagreeing with `R(A)` only on the columns from `K` on, so its
disagreement has density at most `2^{-K}` in every initial segment. -/
theorem exists_computable_approx (A : Set ℕ) (K : ℕ) :
    ∃ Y : Set ℕ, ComputablePred (fun n => n ∈ Y) ∧
      ∀ N, count (symmDiff (Rc A) Y) N ≤ N / 2 ^ K := by
  refine ⟨listApprox (bitsOf A K), computable_listApprox _, fun N => ?_⟩
  have hsub : (Finset.range N).filter (· ∈ symmDiff (Rc A) (listApprox (bitsOf A K))) ⊆
      (Finset.range N).filter (fun n => 2 ^ K ∣ (n + 1)) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
    refine ⟨hn.1, ?_⟩
    rw [pow_dvd_iff_le_col]
    by_contra hcon
    have hlt : col n < K := by omega
    have hiff : n ∈ Rc A ↔ n ∈ listApprox (bitsOf A K) := (mem_listApprox_bitsOf hlt).symm
    rcases Set.mem_symmDiff.mp hn.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h2 (hiff.mp h1)
    · exact h2 (hiff.mpr h1)
  calc count (symmDiff (Rc A) (listApprox (bitsOf A K))) N
      ≤ ((Finset.range N).filter (fun n => 2 ^ K ∣ (n + 1))).card := Finset.card_le_card hsub
    _ = N / 2 ^ K := card_tail K N

/-- **Hyperarithmetic compactness fails.**  If `A` is not hyperarithmetic then `A` belongs to the
hyper-core of `R(A)`, yet at every radius `2^{-K}` there is a *computable* set that far from
`R(A)`, and no computable set is hyperarithmetically above `A`.  So the conclusion of the
cone-avoiding compactness theorem — that a member of the core is already computed by some
description of small radius — is false for `≤_h`. -/
theorem hyperarithmetic_compactness_fails {A : Set ℕ} (hA : ¬ Hyp A) :
    A ∈ hcore (Rc A) ∧
      ∀ K, ∃ Y : Set ℕ, ComputablePred (fun n => n ∈ Y) ∧
        (∀ N, count (symmDiff (Rc A) Y) N ≤ N / 2 ^ K) ∧ ¬ HypIn Y A := by
  refine ⟨mem_hcore_Rc A, fun K => ?_⟩
  obtain ⟨Y, hYc, hYd⟩ := exists_computable_approx A K
  refine ⟨Y, hYc, hYd, fun hhyp => hA ?_⟩
  exact hhyp.mono (setTuringReducible_of_computablePred hYc)

end CoarseDegrees
