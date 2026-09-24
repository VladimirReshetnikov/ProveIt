import CoarseDegrees.Basic

/-!
# The set level: cores, graphs, generic sets

The published results used for C1 speak about *sets* `X ⊆ ℕ`, binary coarse descriptions and
Turing reducibility of sets, whereas C1 quantifies over arbitrary total functions.  This file
defines the set-level notions (on top of `TuringDegrees.SetTuringReducible` from `C:\ProveIt`)
and proves the bridge:

* `CoarselyComputable (χ X) → SetCoarselyComputable X` (binary normalization, Lemma 2.2 of the
  synthesis);
* if every set in the core of `X` is computable, then every *function* computable from all
  numerical coarse descriptions of `χ X` is computable (graph coding).

It also defines 1-genericity and generic computability, which occur in the hypotheses of the
admitted published theorems of `CoarseDegrees.Published`.  Everything in this file is proved.
-/

noncomputable section

open scoped Classical Computability
open TuringDegrees
open scoped SetTuring

namespace CoarseDegrees

/-- The characteristic function of a set, as a total function `ℕ → ℕ`. -/
abbrev χ (X : Set ℕ) : ℕ → ℕ := characteristicValue X

theorem oracle_chi (X : Set ℕ) : oracle (χ X) = characteristic X := rfl

theorem tRed_chi_iff {A B : Set ℕ} : χ A ≤ₜ χ B ↔ A ≤ᵀₛ B := Iff.rfl

theorem disagree_chi (D X : Set ℕ) : disagree (χ D) (χ X) = symmDiff D X := by
  ext n
  by_cases hD : n ∈ D <;> by_cases hX : n ∈ X <;>
    simp [disagree, characteristicValue, Set.mem_symmDiff, hD, hX]

/-- `D` is a (binary) coarse description of `X`: the symmetric difference has density zero. -/
def SetCoarseEq (D X : Set ℕ) : Prop := DensityZero (symmDiff D X)

theorem setCoarseEq_iff {D X : Set ℕ} : SetCoarseEq D X ↔ CoarseEq (χ D) (χ X) := by
  unfold SetCoarseEq CoarseEq
  rw [disagree_chi]

/-- `X` is coarsely computable (Jockusch--Schupp 2012, Definition 2.13). -/
def SetCoarselyComputable (X : Set ℕ) : Prop :=
  ∃ C : Set ℕ, ComputablePred (fun n => n ∈ C) ∧ SetCoarseEq C X

/-- The core of `X`: the sets computable from every coarse description of `X`.  This is
`X^𝔠` of Hirschfeldt--Jockusch--Kuyper--Schupp 2016, Definition 3.1. -/
def core (X : Set ℕ) : Set (Set ℕ) :=
  {A | ∀ D : Set ℕ, SetCoarseEq D X → A ≤ᵀₛ D}

/-- Binary normalization (synthesis, Lemma 2.2): a computable numerical coarse description of
a set yields a computable binary one. -/
theorem setCoarselyComputable_of_coarselyComputable {X : Set ℕ}
    (h : CoarselyComputable (χ X)) : SetCoarselyComputable X := by
  obtain ⟨E, hE, hEX⟩ := h
  refine ⟨{n | E n = 1}, ?_, ?_⟩
  · have hp : ComputablePred (fun n => E n = 1) := by
      apply Computable.computablePred
      exact Primrec.eq.decide.to_comp.comp hE (Computable.const 1)
    exact hp
  · refine DensityZero.mono hEX ?_
    intro n hn
    simp only [disagree, Set.mem_setOf_eq]
    rcases hn with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have h1' : E n = 1 := h1
      simp [characteristicValue, h2, h1']
    · have h2' : ¬ E n = 1 := h2
      simpa [characteristicValue, h1] using h2'

/-! ## Graph coding -/

/-- The graph of a total function, coded as a set of natural numbers. -/
def graph (g : ℕ → ℕ) : Set ℕ := {k | g k.unpair.1 = k.unpair.2}

/-- The graph of `g` is computable from `g`. -/
theorem graph_tRed (g : ℕ → ℕ) : χ (graph g) ≤ₜ g := by
  have h1 : RecursiveIn {oracle g} (fun k : ℕ => oracle g k.unpair.1) :=
    recursiveIn_precomp (RecursiveIn.oracle _ (Set.mem_singleton _))
      (Computable.fst.comp Computable.unpair)
  have h2 : RecursiveIn {oracle g} (fun k : ℕ => (Part.some k.unpair.2 : Part ℕ)) :=
    Partrec.recursiveIn (f := fun k : ℕ => (Part.some k.unpair.2 : Part ℕ))
      (Computable.snd.comp Computable.unpair)
  have hc : Computable (fun p : ℕ => if p.unpair.1 = p.unpair.2 then 1 else 0) :=
    (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.unpair)
      (Primrec.snd.comp Primrec.unpair)) (Primrec.const 1) (Primrec.const 0)).to_comp
  have h4 := recursiveIn_map (recursiveIn_pair h1 h2) hc
  refine h4.of_eq fun k => ?_
  simp [oracle, characteristicValue, graph, Seq.seq]

/-- A total function with a computable graph is computable. -/
theorem computable_of_graph {g : ℕ → ℕ} (hG : ComputablePred (fun k => k ∈ graph g)) :
    Computable g := by
  obtain ⟨f, hf, hfeq⟩ := ComputablePred.computable_iff.mp hG
  have hmem : ∀ n m, f (Nat.pair n m) = true ↔ g n = m := by
    intro n m
    have := congrFun hfeq (Nat.pair n m)
    simp only [graph, Set.mem_setOf_eq, Nat.unpair_pair] at this
    rw [this]
  have hp : Partrec₂ (fun n m : ℕ => (Part.some (f (Nat.pair n m)) : Part Bool)) :=
    (hf.comp₂ Primrec₂.natPair.to_comp).partrec₂
  refine (Partrec.rfind hp).of_eq fun n => ?_
  apply Part.eq_some_iff.mpr
  rw [Nat.mem_rfind]
  refine ⟨?_, ?_⟩
  · simp [(hmem n (g n)).mpr rfl]
  · intro m hm
    have : f (Nat.pair n m) = false := by
      cases hfm : f (Nat.pair n m)
      · rfl
      · exact absurd ((hmem n m).mp hfm) (Nat.ne_of_gt hm)
    simp [this]

/-- The bridge from sets to functions.  If every set in the core of `X` is computable, then every
total function computable from all numerical coarse descriptions of `χ X` is computable. -/
theorem computable_of_core_trivial {X : Set ℕ}
    (hcore : ∀ A ∈ core X, ComputablePred (fun n => n ∈ A)) (g : ℕ → ℕ)
    (hg : ∀ D, CoarseEq D (χ X) → g ≤ₜ D) : Computable g := by
  apply computable_of_graph
  apply hcore
  intro D hD
  exact tRed_chi_iff.mp ((graph_tRed g).trans (hg (χ D) (setCoarseEq_iff.mp hD)))

/-! ## Generic sets and generic computability -/

/-- The finite binary string `σ` is an initial segment of (the characteristic sequence of) `X`. -/
def IsPrefixOf (σ : List Bool) (X : Set ℕ) : Prop :=
  ∀ i (hi : i < σ.length), σ[i] = true ↔ i ∈ X

/-- `X` is 1-generic: for every c.e. set `W` of finite binary strings, some initial segment of
`X` lies in `W` or has no extension in `W` (Jockusch 1980; Downey--Hirschfeldt 2010, §2.24). -/
def OneGeneric (X : Set ℕ) : Prop :=
  ∀ W : List Bool → Prop, REPred W →
    ∃ σ, IsPrefixOf σ X ∧ (W σ ∨ ∀ τ, σ <+: τ → ¬ W τ)

/-- `X` is generically computable: some partial computable function has a domain of density one
and agrees with the characteristic function of `X` wherever it is defined
(Jockusch--Schupp 2012, Definition 1.1). -/
def GenericallyComputable (X : Set ℕ) : Prop :=
  ∃ φ : ℕ →. ℕ, Partrec φ ∧ DensityZero {n | ¬ (φ n).Dom} ∧ ∀ n, ∀ v ∈ φ n, v = χ X n

end CoarseDegrees
