/-
  THE FINITE-LABEL OBSTRUCTION (synthesis Lemma 9.7, Theorem 9.8, Corollary 9.9; report R7).

  The permutation-realization lemma is proved with a uniform construction that avoids the
  cycle decomposition of the report: for a permutation `π` of `Fin m` put

      a_i = { κ_n + (π⁻ⁿ i) : n < ω }.

  Then `e '' a_i = a_{π i} ∖ {κ_0 + π i}` whenever `e (κ_n + t) = κ_{n+1} + t`, and the
  `a_i` are pairwise disjoint as soon as consecutive critical points are `m` apart.

  As in `Ultraexacting.lean`, the facts about the embedding used by the proof (it shifts
  the critical sequence together with finite offsets; the label is preserved) are
  hypotheses.  Nothing is admitted in this file.
-/
import Cardinals.Ultraexacting

universe u

namespace Cardinals.FiniteLabel

open Ordinal Set Cardinals.Ultraexacting

variable {m : ℕ}

/-- The tuple realizing the permutation `π`: `a_i = {κ_n + π⁻ⁿ(i) : n < ω}`. -/
def realize (κ : ℕ → Ordinal.{u}) (π : Equiv.Perm (Fin m)) (i : Fin m) : Set Ordinal.{u} :=
  {x | ∃ n : ℕ, x = κ n + (((π⁻¹ ^ n) i : Fin m) : ℕ)}

/-- **Finite-permutation realization (synthesis Lemma 9.7).** -/
theorem image_realize (e : Ordinal.{u} → Ordinal.{u}) (κ : ℕ → Ordinal.{u})
    (hshift : ∀ (n : ℕ) (t : ℕ), t < m → e (κ n + t) = κ (n + 1) + t)
    (hgap : ∀ n, κ n + m ≤ κ (n + 1)) (π : Equiv.Perm (Fin m)) (i : Fin m) :
    e '' realize κ π i = realize κ π (π i) \ {κ 0 + ((π i : Fin m) : ℕ)} := by
  have hκ : StrictMono κ := by
    apply strictMono_nat_of_lt_succ
    intro n
    rcases Nat.eq_zero_or_pos m with hm | hm
    · exact (Fin.elim0 (hm ▸ i))
    · calc κ n < κ n + m := by
            exact (lt_add_iff_pos_right _).mpr (by exact_mod_cast hm)
        _ ≤ κ (n + 1) := hgap n
  -- a point of the form `κ n + t`, `t < m`, determines `n`
  have hblock : ∀ (n n' : ℕ) (t t' : ℕ), t < m → t' < m →
      κ n + t = κ n' + t' → n = n' := by
    intro n n' t t' ht ht' heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have h1 : κ n + t < κ (n + 1) :=
        lt_of_lt_of_le ((add_lt_add_iff_left _).mpr (by exact_mod_cast ht)) (hgap n)
      have h2 : κ (n + 1) ≤ κ n' := hκ.monotone h
      exact absurd heq (ne_of_lt (lt_of_lt_of_le h1 (h2.trans le_self_add)))
    · have h1 : κ n' + t' < κ (n' + 1) :=
        lt_of_lt_of_le ((add_lt_add_iff_left _).mpr (by exact_mod_cast ht')) (hgap n')
      have h2 : κ (n' + 1) ≤ κ n := hκ.monotone h
      exact absurd heq.symm (ne_of_lt (lt_of_lt_of_le h1 (h2.trans le_self_add)))
  have hpow : ∀ n : ℕ, (π⁻¹ ^ (n + 1)) (π i) = (π⁻¹ ^ n) i := by
    intro n
    rw [pow_succ, Equiv.Perm.mul_apply]
    simp
  ext x
  constructor
  · rintro ⟨y, ⟨n, rfl⟩, rfl⟩
    refine ⟨⟨n + 1, ?_⟩, ?_⟩
    · rw [hshift n _ (Fin.is_lt _), hpow]
    · intro hx
      rw [mem_singleton_iff, hshift n _ (Fin.is_lt _)] at hx
      have := hblock (n + 1) 0 _ _ (Fin.is_lt _) (Fin.is_lt _) hx
      omega
  · rintro ⟨⟨n, rfl⟩, hne⟩
    cases n with
    | zero => exact absurd (by simp) hne
    | succ n =>
      refine ⟨κ n + (((π⁻¹ ^ n) i : Fin m) : ℕ), ⟨n, rfl⟩, ?_⟩
      rw [hshift n _ (Fin.is_lt _), hpow]

/-- The realizing sets are pairwise disjoint. -/
theorem disjoint_realize (κ : ℕ → Ordinal.{u}) (hκ : StrictMono κ)
    (hgap : ∀ n, κ n + m ≤ κ (n + 1)) (π : Equiv.Perm (Fin m)) {i j : Fin m} (hij : i ≠ j) :
    Disjoint (realize κ π i) (realize κ π j) := by
  rw [Set.disjoint_left]
  rintro x ⟨n, rfl⟩ ⟨n', hx⟩
  have hnn' : n = n' := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have h1 : κ n + (((π⁻¹ ^ n) i : Fin m) : ℕ) < κ (n + 1) :=
        lt_of_lt_of_le ((add_lt_add_iff_left _).mpr (by exact_mod_cast Fin.is_lt _)) (hgap n)
      have h2 : κ (n + 1) ≤ κ n' := hκ.monotone h
      exact absurd hx (ne_of_lt (lt_of_lt_of_le h1 (h2.trans le_self_add)))
    · have h1 : κ n' + (((π⁻¹ ^ n') j : Fin m) : ℕ) < κ (n' + 1) :=
        lt_of_lt_of_le ((add_lt_add_iff_left _).mpr (by exact_mod_cast Fin.is_lt _)) (hgap n')
      have h2 : κ (n' + 1) ≤ κ n := hκ.monotone h
      exact absurd hx.symm (ne_of_lt (lt_of_lt_of_le h1 (h2.trans le_self_add)))
  subst hnn'
  have h3 : ((((π⁻¹ ^ n) i : Fin m) : ℕ) : Ordinal.{u}) = (((π⁻¹ ^ n) j : Fin m) : ℕ) :=
    (add_right_inj _).mp hx
  have h4 : (π⁻¹ ^ n) i = (π⁻¹ ^ n) j := Fin.ext (by exact_mod_cast h3)
  exact hij ((π⁻¹ ^ n).injective h4)

/-- The image under `e` is a finite change of the permuted coordinate. -/
theorem finiteChange_image_realize (e : Ordinal.{u} → Ordinal.{u}) (κ : ℕ → Ordinal.{u})
    (hshift : ∀ (n : ℕ) (t : ℕ), t < m → e (κ n + t) = κ (n + 1) + t)
    (hgap : ∀ n, κ n + m ≤ κ (n + 1)) (π : Equiv.Perm (Fin m)) (i : Fin m) :
    FiniteChange (e '' realize κ π i) (realize κ π (π i)) := by
  rw [image_realize e κ hshift hgap π i]
  unfold FiniteChange
  apply (Set.finite_singleton (κ 0 + ((π i : Fin m) : ℕ))).subset
  intro x hx
  rcases hx with ⟨⟨_, hnot⟩, hx2⟩ | ⟨hx1, hx2⟩
  · exact absurd ‹_› hx2
  · by_contra hne
    exact hx2 ⟨hx1, hne⟩

/-- The action of a permutation on tuples: `(π • a) i = a (π⁻¹ i)`. -/
def permute (π : Equiv.Perm (Fin m)) (a : Fin m → Set Ordinal.{u}) : Fin m → Set Ordinal.{u} :=
  fun i => a (π⁻¹ i)

/-- **The finite-label obstruction (synthesis Theorem 9.8).**

`Lab` assigns to admissible `m`-tuples of cofinal sets a label in a set `F` on which the
permutations of `Fin m` act by `act`.  Suppose `Lab` is preserved by the embedding,
invariant under finite modification of the coordinates, and equivariant.  Then every
permutation `π` fixes some label. -/
theorem exists_fixed_label {F : Type*} (e : Ordinal.{u} → Ordinal.{u}) (κ : ℕ → Ordinal.{u})
    (hshift : ∀ (n : ℕ) (t : ℕ), t < m → e (κ n + t) = κ (n + 1) + t)
    (hgap : ∀ n, κ n + m ≤ κ (n + 1))
    (Adm : (Fin m → Set Ordinal.{u}) → Prop)
    (hAdm : ∀ π : Equiv.Perm (Fin m), Adm (realize κ π))
    (hAdmP : ∀ (ρ : Equiv.Perm (Fin m)) a, Adm a → Adm (permute ρ a))
    (Lab : (Fin m → Set Ordinal.{u}) → F) (act : Equiv.Perm (Fin m) → F → F)
    (hact : ∀ π x, act π (act π⁻¹ x) = x)
    (hpres : ∀ a, Adm a → Lab (fun i => e '' a i) = Lab a)
    (hmod : ∀ a a', Adm a' → (∀ i, FiniteChange (a i) (a' i)) → Lab a = Lab a')
    (hequiv : ∀ π a, Adm a → Lab (permute π a) = act π (Lab a))
    (π : Equiv.Perm (Fin m)) : ∃ x : F, act π x = x := by
  refine ⟨Lab (realize κ π), ?_⟩
  have hA := hAdm π
  have hA' := hAdmP π⁻¹ _ hA
  -- `e '' a_i =^* a_{π i} = (π⁻¹ • a)_i`
  have key : ∀ i, FiniteChange (e '' realize κ π i) (permute π⁻¹ (realize κ π) i) := by
    intro i
    have := finiteChange_image_realize e κ hshift hgap π i
    simpa [permute] using this
  have h3 : Lab (realize κ π) = act π⁻¹ (Lab (realize κ π)) :=
    calc Lab (realize κ π) = Lab (fun i => e '' realize κ π i) := (hpres _ hA).symm
      _ = Lab (permute π⁻¹ (realize κ π)) := hmod _ _ hA' key
      _ = act π⁻¹ (Lab (realize κ π)) := hequiv π⁻¹ _ hA
  calc act π (Lab (realize κ π)) = act π (act π⁻¹ (Lab (realize κ π))) := by rw [← h3]
    _ = Lab (realize κ π) := hact π _

/-- **Corollary 9.9 (core).**  An `m`-cycle fixes no nonempty proper subset of `Fin m`:
if `S` is invariant under a permutation acting transitively, it is empty or everything.
Together with `exists_fixed_label` (labels = `r`-element subsets, `0 < r < m`) this rules
out an ordinal-definable `r`-of-`m` selector. -/
theorem invariant_subset_of_transitive_perm (π : Equiv.Perm (Fin m))
    (htrans : ∀ i j : Fin m, ∃ k : ℕ, (π ^ k) i = j) (S : Finset (Fin m))
    (hinv : S.image π = S) : S = ∅ ∨ S = Finset.univ := by
  rcases S.eq_empty_or_nonempty with h | ⟨x, hx⟩
  · exact Or.inl h
  · right
    have hiter : ∀ k : ℕ, ∀ z ∈ S, (π ^ k) z ∈ S := by
      intro k
      induction k with
      | zero => intro z hz; simpa using hz
      | succ k ih =>
        intro z hz
        rw [pow_succ', Equiv.Perm.mul_apply, ← hinv]
        exact Finset.mem_image_of_mem π (ih z hz)
    ext y
    simp only [Finset.mem_univ, iff_true]
    obtain ⟨k, hk⟩ := htrans x y
    exact hk ▸ hiter k x hx

end Cardinals.FiniteLabel
