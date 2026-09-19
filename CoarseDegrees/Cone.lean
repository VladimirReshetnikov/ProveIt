import CoarseDegrees.Block

/-!
# No cone theorem for the coarse degrees

Formalization of Theorem 1.5(b) of research report 10
(`docs/coarse-degrees/research-reports/10/coarse_hyperdegrees.tex`) for the nonuniform coarse degrees: above
*every* function `h` there is a function whose coarse class has a least Turing degree and a
function whose coarse class has none.  Hence neither the set `LeastClass` of functions whose
class has a least degree nor its complement contains a cone, and Martin's cone theorem has no
analogue for the coarse degrees (`LeastClass` is invariant: `leastClass_invariant`).

The proof in the report takes the second function to be `J(h) ⊕ A` with `A`, `B` given by the
relativized minimal-pair theorem of the synthesis, which is not formalized.  Here the second
function is `I(Z) ⊕ X` with `X` 1-generic relative to `Z = graph h`, and the required facts are
the relativizations of the two published theorems used for C1 (Route G of
`CoarseDegrees.Published`).  Admitted, with references:

* `OneGenericRel.core_le` — Hirschfeldt--Jockusch--Kuyper--Schupp, Theorem 4.2, relativized;
* `OneGenericRel.not_coarselyComputableIn` — Jockusch--Schupp, remark after Proposition 2.15,
  relativized.

Everything else is proved: the density estimates for joins and halves, the computability of the
block code, the existence of relatively 1-generic sets, the two halves of the theorem, and the
invariance of `LeastClass`.
-/

noncomputable section

open Filter Topology
open scoped Classical Computability
open TuringDegrees
open scoped SetTuring

namespace CoarseDegrees

local infixl:65 " ⊕ₜ " => setJoin

/-! ## The class of functions whose coarse class has a least Turing degree -/

theorem NCRed.trans {f g k : ℕ → ℕ} (hfg : f ≤ₙ g) (hgk : g ≤ₙ k) : f ≤ₙ k := by
  intro D hD
  obtain ⟨E, hE, hED⟩ := hgk D hD
  obtain ⟨F, hF, hFE⟩ := hfg E hE
  exact ⟨F, hF, hFE.trans hED⟩

theorem NCEquiv.trans {f g k : ℕ → ℕ} (hfg : f ≡ₙ g) (hgk : g ≡ₙ k) : f ≡ₙ k :=
  ⟨hfg.1.trans hgk.1, hgk.2.trans hfg.2⟩

/-- The set `𝒜` of report 10, Theorem 1.5. -/
def LeastClass : Set (ℕ → ℕ) := {f | ∃ g, IsLeastNC f g}

/-- `LeastClass` is invariant under nonuniform, hence also uniform, coarse equivalence. -/
theorem leastClass_invariant {f f' : ℕ → ℕ} (h : f ≡ₙ f') : f ∈ LeastClass ↔ f' ∈ LeastClass := by
  constructor
  · rintro ⟨g, hg, hleast⟩
    exact ⟨g, hg.trans h, fun k hk => hleast k (hk.trans h.symm)⟩
  · rintro ⟨g, hg, hleast⟩
    exact ⟨g, hg.trans h.symm, fun k hk => hleast k (hk.trans h)⟩

/-! ## Joins and halves of coarse descriptions -/

/-- The odd half of a set. -/
def oddHalf (C : Set ℕ) : Set ℕ := {k | oddCode k ∈ C}

/-- The even half of a set. -/
def evenHalf (C : Set ℕ) : Set ℕ := {k | evenCode k ∈ C}

theorem oddHalf_reducible (C : Set ℕ) : oddHalf C ≤ᵀₛ C :=
  recursiveIn_precomp (RecursiveIn.oracle (characteristic C) (Set.mem_singleton _))
    computable_oddCode

theorem evenHalf_reducible (C : Set ℕ) : evenHalf C ≤ᵀₛ C :=
  recursiveIn_precomp (RecursiveIn.oracle (characteristic C) (Set.mem_singleton _))
    computable_evenCode

theorem oddCode_lt {k m : ℕ} (h : k < m) : oddCode k < 2 * m := by
  simp only [oddCode, Nat.bit_val]
  simp
  omega

theorem evenCode_lt {k m : ℕ} (h : k < m) : evenCode k < 2 * m := by
  simp only [evenCode, Nat.bit_val]
  simp
  omega

/-- Halving a density-zero set along an injective code `c` with `c k < 2 m` for `k < m`. -/
theorem densityZero_half {S : Set ℕ} (hS : DensityZero S) (c : ℕ → ℕ) (hinj : Function.Injective c)
    (hlt : ∀ {k m}, k < m → c k < 2 * m) : DensityZero {k | c k ∈ S} := by
  have hcount : ∀ m, count {k | c k ∈ S} m ≤ count S (2 * m) := by
    intro m
    apply Finset.card_le_card_of_injOn c
    · intro k hk
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hk ⊢
      exact ⟨hlt hk.1, hk.2⟩
    · exact hinj.injOn
  have hlim : Tendsto (fun m : ℕ => 2 * ((count S (2 * m) : ℝ) / ((2 * m : ℕ) : ℝ))) atTop
      (𝓝 0) := by
    have h2 : Tendsto (fun m : ℕ => 2 * m) atTop atTop :=
      tendsto_atTop_mono (fun m => (by show m ≤ 2 * m; omega)) tendsto_id
    have := (hS.comp h2).const_mul (2 : ℝ)
    simpa using this
  refine squeeze_zero (fun m => by positivity) (fun m => ?_) hlim
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have heq : 2 * ((count S (2 * m) : ℝ) / ((2 * m : ℕ) : ℝ)) = (count S (2 * m) : ℝ) / m := by
      push_cast
      field_simp
    rw [heq]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hcount m) hm'.le

theorem oddCode_injective : Function.Injective oddCode := by
  intro a b h
  simp only [oddCode, Nat.bit_val] at h
  simp at h
  omega

theorem evenCode_injective : Function.Injective evenCode := by
  intro a b h
  simp only [evenCode, Nat.bit_val] at h
  simp at h
  omega

/-- The odd half of a coarse description of `P ⊕ X` is a coarse description of `X`. -/
theorem SetCoarseEq.oddHalf {E P X : Set ℕ} (h : SetCoarseEq E (P ⊕ₜ X)) :
    SetCoarseEq (oddHalf E) X := by
  refine (densityZero_half h oddCode oddCode_injective (fun hk => oddCode_lt hk)).mono ?_
  intro k hk
  simp only [Set.mem_setOf_eq, Set.mem_symmDiff, CoarseDegrees.oddHalf, oddCode_mem_join] at hk ⊢
  exact hk

/-- The even half of a coarse description of `P ⊕ X` is a coarse description of `P`. -/
theorem SetCoarseEq.evenHalf {E P X : Set ℕ} (h : SetCoarseEq E (P ⊕ₜ X)) :
    SetCoarseEq (evenHalf E) P := by
  refine (densityZero_half h evenCode evenCode_injective (fun hk => evenCode_lt hk)).mono ?_
  intro k hk
  simp only [Set.mem_setOf_eq, Set.mem_symmDiff, CoarseDegrees.evenHalf, evenCode_mem_join] at hk ⊢
  exact hk

/-- Joining a fixed set with a coarse description gives a coarse description of the join. -/
theorem SetCoarseEq.join {D X : Set ℕ} (P : Set ℕ) (h : SetCoarseEq D X) :
    SetCoarseEq (P ⊕ₜ D) (P ⊕ₜ X) := by
  have hcount : ∀ n, count (symmDiff (P ⊕ₜ D) (P ⊕ₜ X)) n ≤ count (symmDiff D X) n := by
    intro n
    apply Finset.card_le_card_of_injOn Nat.div2
    · intro m hm
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hm ⊢
      obtain ⟨hmn, hmem⟩ := hm
      have hdiv : m.div2 < n := lt_of_le_of_lt (by rw [Nat.div2_val]; exact Nat.div_le_self m 2) hmn
      refine ⟨hdiv, ?_⟩
      cases hb : m.bodd <;> simp [setJoin, Set.mem_symmDiff, hb] at hmem ⊢
      exact hmem
    · intro m hm m' hm' heq
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hm hm'
      have hodd : ∀ {x : ℕ}, x ∈ symmDiff (P ⊕ₜ D) (P ⊕ₜ X) → x.bodd = true := by
        intro x hx
        cases hb : x.bodd
        · simp [setJoin, Set.mem_symmDiff, hb] at hx
        · rfl
      rw [← Nat.bit_bodd_div2 m, ← Nat.bit_bodd_div2 m', hodd hm.2, hodd hm'.2, heq]
  refine squeeze_zero (fun n => by positivity) (fun n => ?_) h
  exact div_le_div_of_nonneg_right (by exact_mod_cast hcount n) (Nat.cast_nonneg n)

/-! ## Admitted published facts -/

/-- `W` is a set of strings that is computably enumerable relative to `Z`. -/
def REIn (Z : Set ℕ) (W : List Bool → Prop) : Prop :=
  ∃ f : ℕ →. ℕ, RecursiveIn {characteristic Z} f ∧ ∀ σ, W σ ↔ (f (Encodable.encode σ)).Dom

/-- `X` is 1-generic relative to `Z`. -/
def OneGenericRel (Z X : Set ℕ) : Prop :=
  ∀ W : List Bool → Prop, REIn Z W → ∃ σ, IsPrefixOf σ X ∧ (W σ ∨ ∀ τ, σ <+: τ → ¬ W τ)

/-- For any countable family of sets of strings there is a set that meets or avoids each of
them (the finite-extension construction, via `exists_chain`). -/
theorem exists_generic_for (W : ℕ → List Bool → Prop) :
    ∃ X : Set ℕ, ∀ k, ∃ σ, IsPrefixOf σ X ∧ (W k σ ∨ ∀ τ, σ <+: τ → ¬ W k τ) := by
  obtain ⟨c, -, hstep, hmeet⟩ :=
    exists_chain (fun q p : List Bool => p <+: q) []
      (fun k => {σ | W k σ ∨ ∀ τ, σ <+: τ → ¬ W k τ})
      (fun k p => by
        by_cases hex : ∃ τ, p <+: τ ∧ W k τ
        · obtain ⟨τ, hτ, hW⟩ := hex
          exact ⟨τ, hτ, Or.inl hW⟩
        · exact ⟨p, List.prefix_refl _, Or.inr fun τ hτ hW => hex ⟨τ, hτ, hW⟩⟩)
  have hmono : ∀ s t, s ≤ t → c s <+: c t := by
    intro s t hst
    induction t, hst using Nat.le_induction with
    | base => exact List.prefix_refl _
    | succ t _ ih => exact ih.trans (hstep t)
  exact ⟨limitSet c, fun k => ⟨c (k + 1), isPrefixOf_limitSet hmono _, hmeet k⟩⟩

/-- For every `Z` there is a set 1-generic relative to `Z`: there are only countably many oracle
programs, hence countably many `Z`-c.e. sets of strings. -/
theorem exists_oneGenericRel (Z : Set ℕ) : ∃ X, OneGenericRel Z X := by
  haveI : Nonempty OracleProgram := ⟨OracleProgram.zero⟩
  obtain ⟨enum, henum⟩ := exists_surjective_nat OracleProgram
  obtain ⟨X, hX⟩ := exists_generic_for
    (fun k σ => ((enum k).eval (characteristic Z) (Encodable.encode σ)).Dom)
  refine ⟨X, fun W hW => ?_⟩
  obtain ⟨f, hf, hWf⟩ := hW
  obtain ⟨p, hp⟩ := OracleProgram.exists_program (RecursiveIn.iff_nat.mp hf)
  obtain ⟨k, hk⟩ := henum p
  obtain ⟨σ, hσ, hmeet⟩ := hX k
  refine ⟨σ, hσ, ?_⟩
  rcases hmeet with h | h
  · left
    rw [hWf, ← hp, ← hk]
    exact h
  · right
    intro τ hτ hWτ
    apply h τ hτ
    rw [hWf, ← hp, ← hk] at hWτ
    exact hWτ

/-- [HJKS], Theorem 4.2, relativized to `Z`: if `X` is 1-generic relative to `Z` and `A` is
computable from `Z ⊕ D` for every coarse description `D` of `X`, then `A` is computable from `Z`.
The published proof (cone-avoiding compactness, Theorem 3.7, applied to the columns of `X`)
relativizes verbatim; the synthesis proves the relativized compactness theorem as Theorem 4.8. -/
theorem OneGenericRel.core_le {Z X A : Set ℕ} (hX : OneGenericRel Z X)
    (hA : ∀ D, SetCoarseEq D X → A ≤ᵀₛ Z ⊕ₜ D) : A ≤ᵀₛ Z := by
  admit

/-- Jockusch--Schupp 2012, remark after Proposition 2.15, relativized to `Z`: a set 1-generic
relative to `Z` has no `Z`-computable coarse description.  (The unrelativized statement is
proved in `CoarseDegrees.GenericDensity`.) -/
theorem OneGenericRel.not_coarselyComputableIn {Z X : Set ℕ} (hX : OneGenericRel Z X) :
    ¬ ∃ C, C ≤ᵀₛ Z ∧ SetCoarseEq C X := by
  admit

/-! ## The two functions above a given `h` -/

/-- A coarse description of `χ P` yields a set description computable from it. -/
theorem exists_set_description {P : Set ℕ} {E : ℕ → ℕ} (hE : CoarseEq E (χ P)) :
    ∃ C : Set ℕ, SetCoarseEq C P ∧ χ C ≤ₜ E :=
  ⟨_, (normalize_description hE).1, (normalize_description hE).2⟩

/-- Above every `h` there is a function whose coarse class has a least Turing degree. -/
theorem exists_least_above (h : ℕ → ℕ) : ∃ f₀, h ≤ₙ f₀ ∧ f₀ ∈ LeastClass := by
  let Z := graph h
  refine ⟨χ (blockCode Z), ?_, χ (blockCode Z), (CoarseEq.refl _).ncEquiv, ?_⟩
  · intro D hD
    obtain ⟨C, hC, hCD⟩ := exists_set_description hD
    have hZ : χ Z ≤ₜ D := (tRed_chi_iff.mpr (blockCode_decode hC)).trans hCD
    exact ⟨h, CoarseEq.refl h, (tRed_graph h).trans hZ⟩
  · intro k hk
    obtain ⟨E, hE, hEk⟩ := hk.exists_description
    obtain ⟨C, hC, hCE⟩ := exists_set_description hE
    have hZ : χ Z ≤ₜ k := ((tRed_chi_iff.mpr (blockCode_decode hC)).trans hCE).trans hEk
    exact (tRed_chi_iff.mpr (blockCode_reducible Z)).trans hZ

/-- Above every `h` there is a function whose coarse class has no least Turing degree. -/
theorem exists_nonleast_above (h : ℕ → ℕ) : ∃ f₁, h ≤ₙ f₁ ∧ f₁ ∉ LeastClass := by
  let Z := graph h
  obtain ⟨X, hX⟩ := exists_oneGenericRel Z
  refine ⟨χ (blockCode Z ⊕ₜ X), ?_, ?_⟩
  · intro D hD
    obtain ⟨C, hC, hCD⟩ := exists_set_description hD
    have h1 : Z ≤ᵀₛ evenHalf C := blockCode_decode hC.evenHalf
    have hZ : χ Z ≤ₜ D := (tRed_chi_iff.mpr (h1.trans (evenHalf_reducible C))).trans hCD
    exact ⟨h, CoarseEq.refl h, (tRed_graph h).trans hZ⟩
  · rintro ⟨g, hg, hleast⟩
    -- the graph of `g` is computable from `Z ⊕ D` for every description `D` of `X`
    have hcore : ∀ D, SetCoarseEq D X → graph g ≤ᵀₛ Z ⊕ₜ D := by
      intro D hD
      have hdesc : CoarseEq (χ (blockCode Z ⊕ₜ D)) (χ (blockCode Z ⊕ₜ X)) :=
        setCoarseEq_iff.mp (hD.join (blockCode Z))
      have hgD : g ≤ₜ χ (blockCode Z ⊕ₜ D) := hleast _ hdesc.ncEquiv
      have hjoin : blockCode Z ⊕ₜ D ≤ᵀₛ Z ⊕ₜ D :=
        join_reducible ((blockCode_reducible Z).trans (reducible_join_left Z D))
          (reducible_join_right Z D)
      exact tRed_chi_iff.mp (((graph_tRed g).trans hgD).trans (tRed_chi_iff.mpr hjoin))
    have hgZ : g ≤ₜ χ Z := (tRed_graph g).trans (tRed_chi_iff.mpr (hX.core_le hcore))
    -- but `g` computes a description of `X`
    obtain ⟨E, hE, hEg⟩ := hg.exists_description
    obtain ⟨C, hC, hCE⟩ := exists_set_description hE
    refine hX.not_coarselyComputableIn ⟨oddHalf C, ?_, hC.oddHalf⟩
    exact (oddHalf_reducible C).trans (tRed_chi_iff.mp ((hCE.trans hEg).trans hgZ))

/-- **Report 10, Theorem 1.5(b)** for the nonuniform coarse degrees: every cone
`{f : h ≤ₙ f}` meets both `LeastClass` and its complement.  So the cone filter on the coarse
degrees is not an ultrafilter on invariant sets, and there is no analogue of Martin's cone
theorem. -/
theorem no_cone_theorem (h : ℕ → ℕ) :
    (∃ f, h ≤ₙ f ∧ f ∈ LeastClass) ∧ (∃ f, h ≤ₙ f ∧ f ∉ LeastClass) :=
  ⟨exists_least_above h, exists_nonleast_above h⟩

/-- Neither `LeastClass` nor its complement contains a cone. -/
theorem leastClass_no_cone (h : ℕ → ℕ) :
    ¬ (∀ f, h ≤ₙ f → f ∈ LeastClass) ∧ ¬ (∀ f, h ≤ₙ f → f ∉ LeastClass) := by
  obtain ⟨⟨f₀, h₀, m₀⟩, ⟨f₁, h₁, m₁⟩⟩ := no_cone_theorem h
  exact ⟨fun hall => m₁ (hall f₁ h₁), fun hall => hall f₀ h₀ m₀⟩

end CoarseDegrees
