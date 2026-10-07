/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Set
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Projection

namespace OAI

section

namespace Erdos3

open Module

universe u v

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]

theorem span_image_inl_of_basis_extension
    {P R : Submodule K V} (hRP : R ≤ P) {κ μ : Type*}
    (bP : Basis κ K P) (bV : Basis (κ ⊕ μ) K V)
    (hext : ∀ i, bV (Sum.inl i) = (bP i : V)) (s : Set κ)
    (hspan : R.comap P.subtype = Submodule.span K (bP '' s)) :
    R = Submodule.span K (bV '' (Sum.inl '' s)) := by
  have himage : P.subtype '' (bP '' s) = bV '' (Sum.inl '' s) := by
    ext x
    constructor
    · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
      exact ⟨Sum.inl i, ⟨i, hi, rfl⟩, hext i⟩
    · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
      exact ⟨bP i, ⟨i, hi, rfl⟩, (hext i).symm⟩
  calc
    R = (R.comap P.subtype).map P.subtype :=
      (Submodule.map_comap_eq_self (by
        simpa [Submodule.range_subtype] using hRP)).symm
    _ = (Submodule.span K (bP '' s)).map P.subtype := by rw [hspan]
    _ = Submodule.span K (P.subtype '' (bP '' s)) := by rw [Submodule.map_span]
    _ = Submodule.span K (bV '' (Sum.inl '' s)) := by rw [himage]

theorem span_range_inl_complement_basis {P Q : Submodule K V} (hPQ : IsCompl P Q)
    {κ μ : Type*} (bP : Basis κ K P) (bQ : Basis μ K Q) :
    let bV := (bP.prod bQ).map (P.prodEquivOfIsCompl Q hPQ)
    P = Submodule.span K (bV '' Set.range Sum.inl) := by
  classical
  let bV := (bP.prod bQ).map (P.prodEquivOfIsCompl Q hPQ)
  apply le_antisymm
  · intro x hx
    have hxp : (⟨x, hx⟩ : P) ∈ Submodule.span K (Set.range bP) := by
      rw [bP.span_eq]
      exact Submodule.mem_top
    exact Submodule.span_induction (R := K) (s := Set.range bP)
      (p := fun y _ => (y : V) ∈ Submodule.span K (bV '' Set.range Sum.inl))
      (fun y hy => by
        obtain ⟨i, rfl⟩ := hy
        apply Submodule.subset_span
        refine ⟨Sum.inl i, ⟨i, rfl⟩, ?_⟩
        simp [bV])
      (Submodule.zero_mem _)
      (fun _ _ _ _ hy hz => Submodule.add_mem _ hy hz)
      (fun a _ _ hy => Submodule.smul_mem _ a hy) hxp
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    simp

theorem exists_basis_with_nested_supports (n : ℕ) :
    ∀ {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (P : Fin n → Submodule K V), Antitone P →
      ∃ (κ : Type) (_ : Fintype κ) (b : Basis κ K V) (s : Fin n → Set κ),
        Antitone s ∧ ∀ i, P i = Submodule.span K (b '' s i) := by
  induction n with
  | zero =>
      intro V _ _ _ P _
      refine ⟨Fin (finrank K V), inferInstance, finBasis K V, Fin.elim0, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
  | succ n ih =>
      intro V _ _ _ P hanti
      classical
      let P₀ : Submodule K V := P 0
      let tail : Fin n → Submodule K P₀ := fun i => (P i.succ).comap P₀.subtype
      have htail : Antitone tail := by
        intro i j hij
        apply Submodule.comap_mono
        exact hanti (by simpa using hij)
      obtain ⟨κ, instκ, bP, sP, hsP, hbP⟩ := ih tail htail
      let : Fintype κ := instκ
      obtain ⟨Q, hPQ⟩ := Submodule.exists_isCompl P₀
      let bQ := finBasis K Q
      let e : (P₀ × Q) ≃ₗ[K] V := P₀.prodEquivOfIsCompl Q hPQ
      let b : Basis (κ ⊕ Fin (finrank K Q)) K V := (bP.prod bQ).map e
      let s : Fin (n + 1) → Set (κ ⊕ Fin (finrank K Q)) :=
        Fin.cases (Set.range Sum.inl) (fun j => Sum.inl '' sP j)
      refine ⟨κ ⊕ Fin (finrank K Q), inferInstance, b, s, ?_, ?_⟩
      · intro i j hij
        obtain rfl | ⟨i', rfl⟩ := i.eq_zero_or_eq_succ
        · obtain rfl | ⟨j', rfl⟩ := j.eq_zero_or_eq_succ
          · exact fun _ hx => hx
          · rintro x ⟨k, _, rfl⟩
            exact Set.mem_range.mpr ⟨k, rfl⟩
        · obtain rfl | ⟨j', rfl⟩ := j.eq_zero_or_eq_succ
          · exact False.elim ((not_le_of_gt (Fin.succ_pos i')) hij)
          · exact Set.image_mono (hsP (by simpa using hij))
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact span_range_inl_complement_basis hPQ bP bQ
        · apply span_image_inl_of_basis_extension
            (P := P₀) (R := P j.succ) (hanti (Fin.zero_le j.succ))
            bP b (fun k => by simp [b, e]) (sP j)
          simpa [tail, P₀] using hbP j

end Erdos3

end

section

namespace Erdos3

open Module

variable {κ : Type*} {n : ℕ}

noncomputable def nestedSupportWeight (S : Fin n → Set κ) (x : κ) : ℕ :=
  by classical exact (Finset.univ.filter fun i => x ∈ S i).card

theorem nestedSupportWeight_le (S : Fin n → Set κ) (x : κ) :
    nestedSupportWeight S x ≤ n := by
  classical
  simpa only [nestedSupportWeight, Finset.card_univ, Fintype.card_fin] using
    Finset.card_filter_le (s := (Finset.univ : Finset (Fin n))) (p := fun i => x ∈ S i)

theorem mem_nestedSupport_iff (S : Fin n → Set κ) (hS : Antitone S) (i : Fin n) (x : κ) :
    x ∈ S i ↔ i.val < nestedSupportWeight S x := by
  classical
  let A := Finset.univ.filter fun j => x ∈ S j
  constructor
  · intro hx
    have hle : Finset.Iic i ⊆ A := by
      intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS (Finset.mem_Iic.mp hj) hx⟩
    have hcard := Finset.card_le_card hle
    rw [Fin.card_Iic] at hcard
    exact hcard
  · intro hi
    by_contra hx
    have hle : A ⊆ Finset.Iio i := by
      intro j hj
      apply Finset.mem_Iio.mpr
      by_contra hij
      exact hx (hS (le_of_not_gt hij) (Finset.mem_filter.mp hj).2)
    have hcard := Finset.card_le_card hle
    rw [Fin.card_Iio] at hcard
    exact Nat.not_lt_of_ge hcard hi

theorem exists_sorted_weighted_flag_basis {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (P : Fin n → Submodule K V) (hP : Antitone P) :
    ∃ (e : Basis (Fin (finrank K V)) K V) (w : Fin (finrank K V) → ℕ),
      Monotone w ∧ (∀ j, w j ≤ n) ∧
      ∀ i, P i = Submodule.span K (e '' {j | i.val < w j}) := by
  classical
  obtain ⟨κ, instκ, b, S, hS, hb⟩ := exists_basis_with_nested_supports n P hP
  let : Fintype κ := instκ
  let ρ : κ ≃ Fin (finrank K V) := Fintype.equivFinOfCardEq (finrank_eq_card_basis b).symm
  let u : Fin (finrank K V) → ℕ := fun j => nestedSupportWeight S (ρ.symm j)
  let σ := Tuple.sort u
  let e := b.reindex (ρ.trans σ.symm)
  let w : Fin (finrank K V) → ℕ := fun j => u (σ j)
  refine ⟨e, w, Tuple.monotone_sort u, fun j => nestedSupportWeight_le S _, ?_⟩
  intro i
  rw [hb i]
  congr 1
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨σ.symm (ρ k), ?_, ?_⟩
    · simpa only [Set.mem_ofPred_eq, w, u, Equiv.apply_symm_apply, Equiv.symm_apply_apply] using
        (mem_nestedSupport_iff S hS i k).mp hk
    · simp [e, Basis.reindex_apply]
  · rintro ⟨j, hj, rfl⟩
    refine ⟨ρ.symm (σ j), (mem_nestedSupport_iff S hS i _).mpr hj, ?_⟩
    simp [e, Basis.reindex_apply]

end Erdos3

end

end OAI
